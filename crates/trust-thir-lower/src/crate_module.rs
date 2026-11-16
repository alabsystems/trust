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
//! 2. **Pass 2** — functions are spliced in: NAMED by their link-time symbol (WS5.2:
//!    `tcx.symbol_name` of the identity instance, stamped at finalization by
//!    `stamp_link_symbols`; the `def_path_str` moves to `display_path`), their `FuncTy` interned
//!    into the assembled module,
//!    and every `Inst::Call { callee }` rewritten through the body's callee-identity ledger
//!    ([`crate::Lowered::callees`]): a LOCAL callee whose body was itself spliced resolves to its
//!    pass-1 `FuncId`; everything else (extern callee, local callee that failed to lower, unknown
//!    or index-ambiguous identity) is fail-closed as a **bodyless declaration** — no body, no
//!    summary, named by the callee instance's link-time symbol when one is computable (WS5.2)
//!    and by a reserved never-linkable `!`-spelling otherwise — which is the IR-level "opaque
//!    external symbol" state (callers stay havoced), with
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
//! Trust (slice 20): patching is also what makes these bodies ADJUDICABLE, so they are routed
//! through the crate-seam differential rather than left as permanent coverage-only skips.
//! `differential::compare` still refuses to interpret a placeholder at the hook, but it now
//! takes the MIR-side snapshot before refusing — the snapshot cannot be taken later, because
//! `mir_built` is a `Steal` already stolen by `mir_promoted` and borrowck has been forced for
//! every body owner long before this seam runs — and `deferred_to_seam` sends the body to
//! [`run_seam_differentials`], which compares it AFTER the patch. That comparison re-tests
//! `unsupported` emptiness first: `resolve_pending_consts` BUMPS it on every failure path, and a
//! body still holding a placeholder must never be interpreted (it would manufacture a false
//! TypeError-vs-value divergence — the exact thing the hook-time gate exists to prevent).
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
//!   diff-stable rendering). GUARDED (WS5.23, F-099): before an artifact set is
//!   committed, the text is re-derived from the `.bin` bytes
//!   (`canonical(deserialize_module(bin))`) and must match byte for byte, otherwise
//!   publication is refused (`TEXT_COMPANION_NOT_CANONICAL`). It is never `Display`
//!   (`trust-ir dump`), which keeps the producer's arena SSA ids.
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
use rustc_ast::attr::AttributeExt;
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_hir::def::DefKind;
use rustc_middle::ty::{self, TyCtxt};
use rustc_session::Session;
use rustc_span::def_id::{DefId, LOCAL_CRATE, LocalDefId};
use rustc_span::Span;
// Trust (wave-16): `GlobalId` is not re-exported at the trust_ir crate root — canonical path.
use trust_ir::value::GlobalId;
use trust_ir::{
    BlockId,
    // Trust (v41 codegen license): the producer's in-band `Function.body_gate` claim.
    BodyGate,
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

mod scalar_correspondence;
// Trust: preserve typed zero-array fields over an exact earlier registered struct.
mod zero_array_struct;
// Trust (2026-09-27): typed splice refusals and R2 over the withheld-layout ledger.
#[cfg(test)]
mod splice_refusal_tests;
#[path = "crate_module/static_globals.rs"]
mod static_globals;
#[path = "crate_module/validation_type_context.rs"]
mod validation_type_context;
// Trust (step 2 increment 4b, owner ruling D18 OD-1): the splice admits `Inst::Drop`.
#[cfg(test)]
#[path = "crate_module/drop_splice_tests.rs"]
mod drop_splice_tests;
// Trust (R8-SEAM, docs/DECISION_QUEUE.md, taken 2026-10-05): the crate-seam differential as it
// was before its one-working-copy rewrite, kept verbatim as the cross-check oracle the TEST-ONLY
// `-Ztrust-ir-seam-reference` option runs beside it (see `SeamScratch`).
#[path = "crate_module/seam_reference.rs"]
mod seam_reference;
#[cfg(test)]
#[path = "crate_module/seam_scratch_tests.rs"]
mod seam_scratch_tests;
// Trust (plan step 3.4, owner rulings D36/D37): the carrier, the session ledger, per-function
// leg 4 and the Clean conservation leg.
#[cfg(test)]
mod carrier_ledger_tests;

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
    /// Trust (absent-callee Stage 3): agreement UNDER THE UNINTERPRETED-CALLEE SUBSTITUTION,
    /// minted only by the fenced adjudicator (`row1_uc_adjudicate`) and NEVER folded into
    /// `Agreed` — its own marker, its own scorecard column, its own `docs/TCB.md` row. The
    /// claim and its documented blind spots (the call site itself; callee effects assumed
    /// absent under the no-channel fence) live in that row.
    AgreedUninterpretedCallee,
}

impl ArtifactVerdict {
    fn marker(self) -> &'static str {
        match self {
            Self::Agreed => "agreed",
            Self::Mismatch => "mismatch",
            Self::Unsupported => "unsupported",
            Self::NotRun => "not-run",
            Self::AgreedUninterpretedCallee => "agreed-uninterpreted-callee",
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
        // Trust (absent-callee Stage 3): the UC class carries `equal: false` BY INVARIANT —
        // strict sameness was not established (the substitution erases the call sites), so
        // nothing keying on `equal` or on `DiffMode::Agreed` can adopt the row.
        (DiffMode::AgreedUninterpretedCallee, false, false) => {
            Ok(ArtifactVerdict::AgreedUninterpretedCallee)
        }
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
    /// Compiler-derived, not provenance-string-derived. The generated built
    /// body has no certificate for the coroutine state-transform protocol.
    generated_ungated: bool,
    /// Exact source ABI and target convention, including explicit compiler-owned adaptations.
    /// Unsupported/absent mappings cannot become a C default during assembly.
    abi: crate::calling_convention::FunctionAbi,
    /// `def.to_def_id().index.as_u32()` — the deterministic body sort key and exact same-crate
    /// lookup identity. Callee `FuncId`s are allocated densely per body and remain separate.
    def_index: u32,
    /// Collision-checked, cross-session identity of this exact definition. Display paths are
    /// deliberately not identity: macro expansion can give several const bodies the same path.
    /// Assembly uses this value only when such definitions need distinct operational names.
    definition: crate::lineage::DefinitionIdentity,
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
    /// Trust (storage value traffic): the intact per-body mini-module carries addressable
    /// `Ty::Storage` geometry at a VALUE position (a signature slot, block parameter, global,
    /// drop-glue key or typed non-`Alloca`/`GEP` instruction), or a callee-ledger entry whose
    /// declaration would carry it by value. Computed at `record` by trust-ir's own
    /// `visit_storage_violations` policy ([`module_carries_storage_value_traffic`]). NEVER
    /// spliced: the shared validator refuses such a slot for the WHOLE crate module, so leaving
    /// the refusal to final validation failed every body in the crate (measured 2026-11-11:
    /// `core` and the `thread_local!` `LazyStorage` initializers). Refuse the body, not the crate.
    storage_value_traffic: bool,
    /// Trust (2026-09-27): the producer's withheld-layout ledger, body-local `StructId`s —
    /// [`crate::Lowered::layout_withheld_structs`]. A row named here has NO layout in `structs`
    /// because the producer withheld a layout rustc DID compute, not because none exists.
    /// Ratification review 2026-09-28: R2 does NOT exempt these rows (a signature that reaches
    /// one is refused as the pin refused it — see [`signature_reaches_unlaid_struct`]); the
    /// ledger only names, in the refusal's debug record, that the row was a withheld claim.
    layout_withheld_structs: Vec<StructId>,
    /// Trust (enum param lane): the body registered >=1 ENUM PARAM PLACEHOLDER LANE — a variant
    /// field whose ground-truth rustc type is a bare `ty::Param`, spelled `Ty::Unit`. NEVER
    /// spliced (`splice_ok` checks this field): the assembled executable module must not contain
    /// an `EnumDef` one of whose lanes claims zero bytes for a caller's `T`. This is also what
    /// confines the forced-`contains_call` bodies out of the crate-seam interpreter — see
    /// `LowerCx::register_enum_param_lane`, whose doc states the 3↔4 dependency in full.
    enum_param_lane: bool,
    /// `tcx.def_path_str` — deterministic but not injective display identity within the crate.
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
    /// Trust (B5 stage 2): this body is a yielding coroutine lowered with the frame-POINTER
    /// convention (`crate::Lowered::coroutine_frame_ptr`). `splice_ok` refuses it on this
    /// field ALONE — a caller lowered elsewhere passes the coroutine BY VALUE, so splicing a
    /// frame-pointer function would be an ABI lie. Own-predicate refusal, never an
    /// instruction scan (the `zst_closure_arg` discipline).
    coroutine_frame_ptr: bool,
    /// Trust (fn-ptr adapter lane): the body's mini-module carries a PRODUCER-SYNTHESIZED
    /// closure→fn-pointer adapter — a function with no rustc counterpart. `splice_ok` refuses the
    /// body on this field ALONE (and `run_seam_differentials` skips it on the same field), for
    /// the reason spelled out at `crate::Lowered::fnptr_adapter`: the per-body channel below is
    /// fn-pointer adapters still lack an admitted transport protocol. Canonical
    /// typed FnOnce adapters use the separate checked transport below.
    fnptr_adapter: bool,
    /// The per-body lowered function (`functions[0]` of the throwaway per-body module), if the
    /// body was a fn body at all.
    function: Option<Function>,
    /// Canonical typed closure adapters carried with their source body.
    adapters: Vec<Function>,
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
    closure_layouts: Vec<trust_ir::ClosureLayoutDescriptor>,
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
    tuple_layouts: Vec<trust_ir::TupleLayoutDescriptor>,
    target_info: Option<trust_ir::TargetInfo>,
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
    global_origins: Vec<crate::GlobalOrigin>,
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
    /// Trust (slice 20): does this body's own module contain a call (`Lowered::contains_call`)?
    /// Recorded so the seam can say WHY a body was deferred without re-deriving it from the
    /// assembled instruction stream — the reachable-callee closure cannot answer it (a
    /// self-recursive body has a one-element closure and is still call-bearing).
    contains_call: bool,
    /// Trust (B9-A, extended slice 20): this body is DEFERRED to the crate-finalize seam
    /// differential (`differential::deferred_to_seam`). It is clean — no unsupported shapes —
    /// and the hook could not reach a verdict for a reason the FINALIZER dissolves. Two such
    /// reasons, and a body may carry either or both:
    ///
    ///   * CALL-BEARING (B9-A): its per-body module carries callees as bodyless declarations,
    ///     so interpretation-equivalence can only be asserted after the crate module links
    ///     their bodies.
    ///   * PENDING-CONST (slice 20): it carries placeholder `Inst::Const` nodes that
    ///     [`resolve_pending_consts`] patches with real values before the seam runs. Such a
    ///     body may be call-FREE; the seam handles it uniformly, since its reachable-callee
    ///     closure is then just the entry and the bundle is a single function.
    ///
    /// The hook SUPPRESSES its own differential event for such bodies (`deferred_to_seam` is the
    /// single source of truth, shared component-wise via `deferred_to_seam_parts`);
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
    /// Trust (WS5.2): this body's LINK-TIME SYMBOL — `Function.name` in the assembled module.
    /// `None` at `record` (the hook runs inside `mir_built`, where `symbol_name` is the E0391
    /// family) and filled once at crate finalization by [`stamp_link_symbols`]: a fn body gets
    /// `tcx.symbol_name` of its identity instance, an initializer the reserved
    /// `__trust_init_<hex>` spelling. A spliceable body with no computable symbol is refused by
    /// name there instead (`unsupported`), so a spliced body without one is a producer defect.
    link_symbol: Option<String>,
    /// Trust (WS5.2): per-ledger-entry link facts, index-aligned with [`Self::callees`] once
    /// [`stamp_link_symbols`] has run (EMPTY before, which every reader treats as "no symbol,
    /// producer unrecorded" — the fail-closed reading, never a guess).
    callee_links: Vec<CalleeLink>,
}

/// Trust (WS5.2): what crate finalization learned about ONE ledgered callee, for the bodyless
/// declaration a call edge to it may become.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct CalleeLink {
    /// `tcx.symbol_name` of the exact resolved instance, when the ledger carries one
    /// ([`crate::link_symbol::callee_link_symbol`]).
    symbol: Option<String>,
    /// The callee's REAL producer ([`crate::link_symbol::declaration_producer`]); `None` =
    /// unrecorded.
    producer: Option<trust_ir::Producer>,
    /// Trust (WS5.2 NARROWED — RESIDUAL, `docs/DECISION_QUEUE.md` D17-DECL-SYMBOL-1): the callee
    /// is a generic instance the frozen D17 instance lane APPENDS at codegen
    /// ([`crate::link_symbol::keeps_instance_lane_spelling`]). A declaration of it keeps its
    /// PRE-WS5.2 spelling ([`instance_lane_decl_name`]) and `symbol` is `None`: the one place
    /// `Function.name` is not yet the link-time symbol.
    instance_lane_spelling: bool,
    /// Original foreign prototype and actual FnAbi, read after body lowering.
    /// It names no body-local table and is carried intact into the real module.
    foreign_signature: Option<FuncTy>,
    foreign_source: Option<crate::foreign_signature::ForeignSource>,
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

/// Trust: resolve actual emitted call/function-address references to minted Clean defs.
/// An admission ledger can contain a callee whose arguments later failed to lower, so
/// ledger membership alone must not demand a body. Keep this read separate from the
/// registry drain and release the Session-state borrow before the caller queries MIR.
pub fn referenced_clean_origin_defs(tcx: TyCtxt<'_>) -> Vec<LocalDefId> {
    let clean_defs: BTreeSet<_> = tcx
        .resolutions(())
        .clean_origin_defs
        .iter()
        .map(|(def, _, _)| def.local_def_index.as_u32())
        .collect();
    if clean_defs.is_empty() {
        return Vec::new();
    }
    // Match the finalizer's complete hook population, including warm/custom-MIR paths.
    // This runs at the analysis seam, never inside an in-flight mir_built provider.
    tcx.par_hir_body_owners(|def| tcx.ensure_done().mir_built(def));
    tcx.sess.with_trust_compiler_state::<CrateModuleRegistry, _>(|registry| {
        referenced_clean_origin_records(registry, &clean_defs)
    })
}

fn referenced_clean_origin_records(
    registry: &CrateModuleRegistry,
    clean_defs: &BTreeSet<u32>,
) -> Vec<LocalDefId> {
    let duplicates: BTreeSet<_> = registry.duplicate_def_indices.iter().copied().collect();
    let mut referenced = BTreeMap::new();
    for record in registry.records.values() {
        // A duplicate owner has no unique producer record. Let the finalizer's
        // inventory refusal report it instead of demanding from the retained first row.
        if duplicates.contains(&record.def_index) {
            continue;
        }
        let Some(function) = &record.function else { continue };
        for def in referenced_clean_callees(function, &record.callees, clean_defs) {
            referenced.insert(def.local_def_index.as_u32(), def);
        }
    }
    referenced.into_values().collect()
}

fn referenced_clean_callees(
    function: &Function,
    callees: &[CalleeRef],
    clean_defs: &BTreeSet<u32>,
) -> Vec<LocalDefId> {
    let mut referenced = BTreeMap::new();
    for node in function.blocks.iter().flat_map(|block| &block.body) {
        let target = match &node.inst {
            Inst::Call { callee, .. } | Inst::Invoke { callee, .. } => *callee,
            Inst::Const { value: Constant::FnDef(callee), .. } => *callee,
            _ => continue,
        };
        let mut matches = callees.iter().filter(|callee| callee.func_id == target);
        let Some(callee) = matches.next() else { continue };
        if matches.next().is_some() {
            // An ambiguous ledger is not authority to choose either source identity.
            // Existing assembly/validation retains responsibility for rejecting it.
            continue;
        }
        if let Some(def) = callee.def_id.as_local() {
            if callee.is_local
                && callee.def_index == def.local_def_index.as_u32()
                && clean_defs.contains(&def.local_def_index.as_u32())
            {
                referenced.insert(def.local_def_index.as_u32(), def);
            }
        }
    }
    referenced.into_values().collect()
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
/// `Borrow(inner unlowered)` (2026-08-11) is the fourth, and it was carved OUT of
/// `Borrow(non-local place)`: that name previously covered three unrelated sites, one of which
/// (`lib.rs`, the `None` arm after `lower_expr(inner)` failed) is a pure echo of a leaf the inner
/// expression already recorded. Sharing a name with two genuine refusals made the census
/// histogram unplannable — summing one string over three meanings measures nothing.
pub const CASCADE_TAGS: [&str; 4] = [
    "VarRef(unbound)",
    "Borrow(unbound local)",
    "AssignOp(unbound local)",
    "Borrow(inner unlowered)",
];

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
    let rec = build_body_record(
        tcx, def, lowered, Some(interpreter_report), Some(derived_report),
        mir_snapshot, collect_all, collect_all_overflowed,
    );
    let def_index = rec.def_index;
    tcx.sess.with_trust_compiler_state::<CrateModuleRegistry, _>(|registry| {
        insert_registry_record(
            &mut registry.records,
            &mut registry.duplicate_def_indices,
            def_index,
            rec,
        );
    });
}

fn build_body_record(
    tcx: TyCtxt<'_>,
    def: LocalDefId,
    lowered: Lowered,
    interpreter_report: Option<&crate::differential::DiffReport>,
    derived_report: Option<&crate::mir_differential::DerivedReport>,
    mir_snapshot: Option<trust_types::VerifiableFunction>,
    collect_all: &[(String, &'static str)],
    collect_all_overflowed: bool,
) -> BodyRecord {
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
    let definition = crate::lineage::DefinitionIdentity::from_def_id(tcx, def.to_def_id());
    let lineage =
        crate::lineage::body_lineage_digest(definition, &lowered.module, &lowered.callees).ok();
    // Trust (storage value traffic): read before the destructure below strips `functions[0]`,
    // so the scan covers the body function, its adapters, every pended signature and the ledger.
    let storage_value_traffic =
        module_carries_storage_value_traffic(&lowered.module, &lowered.callees);

    let Lowered {
        mut module,
        global_origins,
        body_kind,
        symbolic,
        unsubstituted_opaque_return,
        unsupported: lowered_unsupported,
        contains_call,
        place_path_carrier,
        zst_closure_arg,
        coroutine_frame_ptr,
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
        // Trust (2026-09-27): the withheld-layout ledger — carried into the `BodyRecord`, where
        // R2 names it in its refusal record (it admits nothing; ratification review 2026-09-28).
        // Bound explicitly for the same reason.
        layout_withheld_structs,
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
        // (`flip_registry::thin_reborrows_allow_flip`: "the producer holds no record it could hand
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
        // UNCHANGED by the provenance ledger. The field is now a `Vec<ThinReborrow>` rather than a
        // `bool`, and the flip gate now CERTIFIES one of its classes instead of refusing all of
        // them — but the reason this file ignores it is about MISREPRESENTATION, which is
        // orthogonal to provenance, so it neither gains nor loses force. The binding is still
        // explicit for the same reason `opaque_collapse` is: a future field must not slip past
        // this destructure.
        thin_reborrows: _thin_reborrows,
        // Trust (wave-MR): the `&mut` twin, and the splice reads it the SAME way for the same
        // reason — the arm emits zero instructions and mints nothing, so the module
        // misdescribes no bytes. The refusal that does apply to it is the FLIP's
        // (`flip_registry::mut_reborrows_allow_flip`, whole-class), not this one.
        mut_reborrows: _mut_reborrows,
        // Trust (wave-EF): the register_enum decline-reason ledger. Empty unless
        // `TRUST_ENUM_DECLINE_CENSUS=1`; carried to coverage BESIDE `unsupported`, never
        // inside it. Bound explicitly for the same reason `opaque_collapse` is.
        enum_declines: lowered_enum_declines,
        // Trust (enum-switch provenance): consumed by `to_mir`'s wave-V reshape via the
        // differential and the flip registry, NOT by crate assembly — the assembled module is the
        // producer's IR verbatim, and this set describes how that IR maps BACK to built MIR. Bound
        // explicitly for the same reason `opaque_collapse` is: a future field must not slip past
        // this destructure.
        enum_fold_switch_blocks: _enum_fold_switch_blocks,
    } = lowered;
    // Trust (slice 20): the shared predicate, NOT a hand-rolled copy. `deferred_to_seam` is
    // documented as the single source of truth for the hook's event suppression and this flag;
    // it now actually is one. A divergence between the two drops seam verdicts silently (the
    // scorecard is first-event-wins), so the two must not be separately maintained.
    let deferred = crate::differential::deferred_to_seam_parts(
        lowered_unsupported.is_empty(),
        pending_consts.is_empty(),
        contains_call,
    );
    // Trust: `functions[0]` is THE body function. The producer maintains that: both
    // `lower_fn` and `lower_const_body` add exactly one function, and the fn-ptr adapter lane
    // appends its synthetic functions only AFTER that one (`lower_module_inner`'s flush, which
    // fails the body closed unless exactly one function is already present). Everything past
    // index 0 is retained in `adapters` and must pass the canonical typed closure
    // adapter check before transport. The existing fn-pointer flag still refuses
    // those older shims independently.
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
    let retain_artifact_details =
        tcx.sess.opts.unstable_opts.trust_dump.ir.is_some() || emit_requested(tcx);
    let interpreter = if let Some(interpreter_report) = interpreter_report {
        if interpreter_report.unsupported != lowered_unsupported {
            differential_errors.push(format!(
                "direct-THIR differential inventory mismatch for `{def_path}` (def index \
                 {def_index}): report carried {} unsupported event(s), lowering carried {}",
                interpreter_report.unsupported.len(),
                lowered_unsupported.len(),
            ));
        }
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
        interpreter
    } else {
        InterpreterEvidence {
            verdict: ArtifactVerdict::NotRun,
            samples: 0,
            detail: "query assembly: differential not requested".to_string(),
        }
    };
    let derived_mir = if let Some(derived_report) = derived_report {
        DerivedMirEvidence {
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
        }
    } else {
        DerivedMirEvidence {
            verdict: ArtifactVerdict::NotRun,
            detail: "query assembly: derived MIR not requested".to_string(),
            markers_exact: false,
            markers_detail: String::new(),
        }
    };
    if deferred && interpreter.verdict != ArtifactVerdict::NotRun {
        differential_errors.push(format!(
            "direct-THIR deferred differential invariant failed for `{def_path}` (def index \
             {def_index}): hook-time verdict was `{}` instead of `not-run`",
            interpreter.verdict.marker(),
        ));
    }

    let abi = crate::calling_convention::FunctionAbi::of_definition(tcx, def.to_def_id());
    let rec = BodyRecord {
        generated_ungated: tcx.def_kind(def) == DefKind::SyntheticCoroutineBody,
        coroutine_frame_ptr,
        abi,
        def_index,
        definition,
        kind: body_kind,
        symbolic: symbolic || unsubstituted_opaque_return,
        union_lane,
        storage_value_traffic,
        layout_withheld_structs,
        enum_param_lane,
        def_path,
        place_path_carrier,
        zst_closure_arg,
        fnptr_adapter,
        function,
        adapters: module.functions,
        func_ty,
        structs: module.structs,
        enums: module.enums,
        types: module.types,
        tuple_layouts: module.tuple_layouts,
        target_info: module.target_info,
        // Trust (wave-16): promoted-borrow globals snapshot.
        globals: module.globals,
        global_origins,
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
        closure_layouts: module.closure_layouts,
        pending_consts,
        contains_call,
        deferred,
        interpreter,
        derived_mir,
        differential_errors,
        mir_snapshot,
        lineage,
        // Trust (WS5.2): filled at crate finalization (`stamp_link_symbols`), never here —
        // this hook runs inside `mir_built`.
        link_symbol: None,
        callee_links: Vec::new(),
    };

    rec
}

/// A structural query assembly over exactly one supplied body. This is NOT a
/// published crate, complete inventory, checked differential, callable license
/// or source-refinement result. Missing callees remain canonical bodyless/havoc
/// declarations; this wrapper grants no implementation or returned values.
pub struct QueryAssembly {
    module: Module,
    entry: FuncId,
    original_callees: Vec<CalleeRef>,
    declarations: usize,
}

impl QueryAssembly {
    pub fn module(&self) -> &Module { &self.module }
    pub fn entry(&self) -> FuncId { self.entry }
    /// Original BODY-LOCAL ids and standing, not assembled function ids.
    pub fn original_callees(&self) -> &[CalleeRef] { &self.original_callees }
    pub fn declaration_count(&self) -> usize { self.declarations }
}

#[derive(Debug, PartialEq, Eq)]
pub enum QueryAssemblyRefusal {
    ActiveMirBuilding,
    AnalysisNotCompleted,
    AnalysisFailed,
    UnsupportedTarget,
    TargetMismatch,
    InvalidModule(Vec<String>),
    UnsupportedOwner,
    BodyShape,
    PendingConstants,
    UnencodableBody(trust_ir::BinaryProjectionError),
    DropLowering(String),
    CanonicalAssembly(Vec<String>),
    CallerNotRetained(String),
}

/// Reuse the ordinary record conversion and two-pass table/callee assembly
/// without touching Trust Session registries or finalizing a crate artifact.
/// This requires ordinary compiler analysis to finish before exact-instance
/// symbol queries: it refuses an active MIR-building freeze and observes only
/// a completed `analysis(())` cache entry. It never forces analysis or finalization.
/// No pending-constant resolution, seam differential, publication,
/// coverage-completeness or codegen-license step runs here.
/// `lowered` is structural producer data, not a source/proof capability.
pub fn assemble_query_body(
    tcx: TyCtxt<'_>, def: LocalDefId, query: (Lowered, Option<String>),
) -> Result<QueryAssembly, QueryAssemblyRefusal> {
    if trust_mir_extract::ctfe_reentrancy::frozen() {
        return Err(QueryAssemblyRefusal::ActiveMirBuilding);
    }
    if !matches!(tcx.sess.target.pointer_width, 32 | 64) {
        return Err(QueryAssemblyRefusal::UnsupportedTarget);
    }
    // A symbol query may demand MIR. Observe only the genuine completed analysis
    // query, with normal cache-hit dependency bookkeeping; never reenter analysis.
    let cache = &tcx.query_system.query_vtables.analysis.cache;
    let (_, index) = rustc_middle::query::QueryCache::lookup(cache, &())
        .ok_or(QueryAssemblyRefusal::AnalysisNotCompleted)?;
    tcx.prof.query_cache_hit(index.into());
    tcx.dep_graph.read_index(index);
    if tcx.sess.dcx().has_errors_excluding_lint_errors().is_some() {
        return Err(QueryAssemblyRefusal::AnalysisFailed);
    }
    let (lowered, drop_refusal) = query;
    if lowered.module.target_info.as_ref().is_some_and(|target| *target != source_target_info(tcx)) {
        return Err(QueryAssemblyRefusal::TargetMismatch);
    }
    if let Some(reason) = drop_refusal { return Err(QueryAssemblyRefusal::DropLowering(reason)); }
    if !matches!(tcx.def_kind(def), DefKind::Fn | DefKind::AssocFn)
        || !matches!(lowered.body_kind, BodyKind::Fn) {
        return Err(QueryAssemblyRefusal::UnsupportedOwner);
    }
    if lowered.module.functions.first().is_none_or(|f| f.id != FuncId::new(0)) {
        return Err(QueryAssemblyRefusal::BodyShape);
    }
    if !lowered.pending_consts.is_empty() {
        return Err(QueryAssemblyRefusal::PendingConstants);
    }
    // Ordinary record conversion computes the mini-module's lineage identity.
    // Its infallible encoder assumes a producer-owned wire image; the query
    // API also accepts caller-supplied structural data. Check the intact
    // input with the same wire writer before allowing that identity operation.
    if let Some(refusal) = lowered.module.wire_image_refusal() {
        return Err(QueryAssemblyRefusal::UnencodableBody(refusal));
    }
    let original_callees = lowered.callees.clone();
    let record = build_body_record(tcx, def, lowered, None, None, None, &[], false);
    let def_index = record.def_index;
    let mut records = vec![record];
    // Use the ordinary exact-instance symbol owner. It can only add a refusal;
    // no guessed display-path symbol or executable-callee standing is minted.
    let _symbol_refusals = stamp_link_symbols(tcx, &mut records);
    let mut assembled = assemble("unpublished-query-body", &records, &BTreeSet::new());
    if !assembled.errors.is_empty() {
        return Err(QueryAssemblyRefusal::CanonicalAssembly(assembled.errors));
    }
    let Some((_, entry)) = assembled.assigned.iter().find(|(index, _)| *index == def_index) else {
        let reason = assembled.coverage_rows.iter().find(|r| r.def_index == def_index)
            .and_then(|r| r.splice_refusal).map(|r| r.marker().to_string())
            .unwrap_or_else(|| "caller not admitted by canonical assembly".to_string());
        return Err(QueryAssemblyRefusal::CallerNotRetained(reason));
    };
    stamp_target_info_if_vacuous(tcx, &mut assembled.module);
    let validation = trust_ir_build::validate_module(&assembled.module);
    if !validation.is_empty() {
        return Err(QueryAssemblyRefusal::InvalidModule(
            validation.into_iter().map(|error| format!("{error:?}")).collect(),
        ));
    }
    Ok(QueryAssembly {
        module: assembled.module, entry: *entry, original_callees,
        declarations: assembled.declarations,
    })
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
    /// Trust (Step 2/3, owner directive 2026-08-30): the direct lane may BIRTH
    /// claim-free `Pending` obligation rows — recorded at emission, installed
    /// fail-closed at the finalizer — and nothing else. Not contract-bound
    /// (no `Function.summary` contracts, no typed clause carrier), no proof
    /// authority, no native verification requests. Rollback is a one-line
    /// const move back to [`Self::StructuralParityOnly`].
    ObligationBearingPending,
}

impl DirectObligationCapability {
    /// Stable spelling written to `coverage.json` and tracing output.
    pub const fn marker(self) -> &'static str {
        match self {
            Self::StructuralParityOnly => "structural-parity-only-v1",
            Self::ObligationBearingPending => "obligation-bearing-pending-v2",
        }
    }

    /// Whether this artifact may be treated as source-proof authority.
    pub const fn grants_proof_authority(self) -> bool {
        match self {
            Self::StructuralParityOnly => false,
            // Pending rows are CLAIMS. A claim is not authority, and the
            // tier that admits them must say so in the same breath.
            Self::ObligationBearingPending => false,
        }
    }

    /// Whether this producer can build direct native verification requests.
    pub const fn emits_native_verification_requests(self) -> bool {
        match self {
            Self::StructuralParityOnly => false,
            Self::ObligationBearingPending => false,
        }
    }

    /// The tier-ladder view of this capability, for the tier-aware inventory
    /// check in [`crate::direct_obligations`]. Variant-to-variant; no logic.
    pub const fn tier(self) -> crate::direct_obligations::DirectObligationTier {
        match self {
            Self::StructuralParityOnly => {
                crate::direct_obligations::DirectObligationTier::StructuralParityOnly
            }
            Self::ObligationBearingPending => {
                crate::direct_obligations::DirectObligationTier::ObligationBearingPending
            }
        }
    }
}

/// Current direct THIR obligation capability. Changing this is a deliberate
/// soundness event: source identity, typed formulas, state binding, and exact
/// function/obligation ownership must all be wired first.
///
/// Trust (Step 2/3): moved `StructuralParityOnly` -> `ObligationBearingPending`
/// under the owner directive of 2026-08-30 (step two of the three-step plan),
/// with the identity, the emission-bound sites, the fail-closed installer and
/// the tier-aware inventory check landed and adversarially verified in
/// `crate::direct_obligations` first. The rows this admits are `Pending`
/// claims; both authority methods above still return `false` at this tier.
pub const DIRECT_OBLIGATION_CAPABILITY: DirectObligationCapability =
    DirectObligationCapability::ObligationBearingPending;

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

/// Trust: one body the CRATE-ASSEMBLY re-splice fixpoint refused, carried out to the
/// compiler so `-Ztrust-ir-lower=strict` can report it.
///
/// WHY THIS CHANNEL EXISTS. Strict's only per-body arm (`rustc_mir_build`'s builder)
/// reads the `mir_built`-time report, and `54ea2954cd` moved the unsignable-Rust-ABI
/// refusal LATER — into the re-splice fixpoint in `finalize_and_dump`, which runs long
/// after that report is taken. The body was refused (`lowered: false, spliced: false`)
/// and strict exited 0 anyway, against its own help text: "a body the producer cannot
/// fully lower [is] a compile error instead of a coverage-only skip". That is a contract
/// violation, not a policy choice, and it was introduced by moving the refusal rather
/// than by any decision about what strict means.
///
/// This is deliberately the SAME SHAPE as [`SeamVerdict`]: a `def_index` the compiler
/// reconstructs into a `LocalDefId` and a reason it renders at that body's span. The seam
/// channel already proved the pattern for verdicts that can only be known after the whole
/// crate is assembled; a late refusal is another one.
#[derive(Debug, Clone)]
pub struct RefusedBody {
    /// `DefId::index` of the refused body — reconstructed compiler-side.
    pub def_index: u32,
    /// The producer's own refusal text, carrying its v7/D3 options.
    pub reason: String,
}

/// Trust (B9-A): what [`finalize_and_dump`] produced. `seam` is emitted on every
/// direct-TrustIR compile (the registry is populated unconditionally for the
/// lane); `dump` is `Some` whenever either the dump option or first-class
/// `--emit=trust-ir` requested an artifact set.
pub struct FinalizeSummary {
    pub seam: Vec<SeamVerdict>,
    /// Bodies refused by the crate-assembly re-splice fixpoint, AFTER the
    /// `mir_built`-time report strict's per-body arm reads. See [`RefusedBody`].
    pub refused_bodies: Vec<RefusedBody>,
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
///
/// Trust (R8-SEAM, `docs/DECISION_QUEUE.md`, taken 2026-10-05): every comparison runs on ONE
/// working copy of the assembled module ([`SeamScratch`]) instead of a whole-module copy per
/// sample leg, per drop-bearing closure and per pointer-lane comparison. `uc_events`, when given,
/// also receives every row-1 UC probe outcome this pass traces (the cross-check of
/// `seam_reference.rs` compares them); the returned [`SeamScratchStats`] count what the working
/// copy did.
fn run_seam_differentials(
    records: &[BodyRecord],
    assembled: &Assembled,
    uc_events: Option<&std::cell::RefCell<Vec<UcProbeEvent>>>,
) -> (Vec<SeamVerdict>, SeamScratchStats) {
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
    // Trust (R8-SEAM): the pass's ONE working copy of the crate module, made on first use.
    let mut scratch = SeamScratch::new(&assembled.module);
    for r in records.iter().filter(|r| r.deferred) {
        // Trust (slice 20) — THE PENDING-CONST FAIL-CLOSE. MANDATORY, and it must be the FIRST
        // gate in this loop.
        //
        // `r.deferred` was decided at the HOOK, before `resolve_pending_consts` ran. That pass
        // is not infallible and does not merely fail to improve a body — it BUMPS
        // `r.unsupported` at every failure site it has (`PendingStr(eval failed at finalize)`,
        // `PendingStr(empty)`, `PendingStr(global not patched)`, `PendingStr(global patch
        // conflict)`, `PendingConst(eval failed at finalize)`, `PendingConst(placeholder not
        // found)`, `PendingConst(sentinel leak)`, and the `check_str_global_ledger` rows).
        //
        // A body that took any of those still carries its PLACEHOLDER. Interpreting it is
        // precisely what the hook-time gate exists to prevent: the placeholder is a
        // `Constant::PhantomData` where the oracle has a real value, so the comparison
        // manufactures a false TypeError-vs-value DIVERGENCE — a published claim that the
        // producer is wrong about a body whose const nobody ever evaluated.
        //
        // Re-testing emptiness here is therefore not belt-and-braces: it is the same gate,
        // re-asked at the only point where its answer can have changed. It is stated for ALL
        // deferred bodies rather than only pending-const ones because it is true of all of them
        // (a call-only deferred body's `unsupported` is untouched by that pass), and a gate that
        // reads "no body may be linked while it carries an unsupported shape" is a stronger and
        // more obviously correct invariant than one scoped to the lane that motivated it.
        if !r.unsupported.is_empty() {
            // Trust (owner call 2026-09-17(b)): SPLIT THE NOTE BY CAUSE. The gate is unchanged
            // — any unsupported shape still refuses interpretation — but the note is read as
            // data: `scripts/trust_ir_producer_scorecard.py` buckets
            // "finalizer const resolution failed" as `clean-skip-pending-const-unresolved`,
            // "the only number that says whether the lane's ceiling is the gate or the
            // evaluator". A body refused for minting an unsignable Rust-ABI call edge has
            // nothing to do with const evaluation, and reusing that note would inflate that
            // number with a population it does not measure. The two sets are disjoint by
            // construction: the unsignable-edge refusal only ever marks a body that SPLICED,
            // and a body `resolve_pending_consts` marked never splices.
            verdicts.push(skip(r.def_index, unsupported_body_skip_note(&r.unsupported)));
            continue;
        }
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
        // body to link. LOAD-BEARING: a reachable vararg-sig declaration would err
        // `SignatureMismatch` in the interpreter, which would surface as a FALSE oracle verdict.
        //
        // Trust (B8 step 1): "no local body to link" is FIVE different facts — see [`DeclKind`].
        // This gate is the corpus's largest single non-verdict class (983 clean rows on
        // postbuild-slice20-control), and until this slice it reported all five under one name,
        // which happened to be the name of only one of them. `blocker_summary` below names them.
        //
        // NOTE FOR ANYONE PRICING THIS CLASS: the count here is a FIRST-BLOCKER count. This loop
        // is an eight-step first-wins chain, so a body refused at step 2 has never been tested
        // against steps 3-8, and clearing step 2 for it is not the same as reaching a verdict.
        // Measured on the same artifact, the bodies that DO clear step 2 reach `Agreed` 70 times
        // out of 164 — and they are the easy end of the population (a fully bodyful closure).
        let declarations: Vec<FuncId> = closure
            .iter()
            .copied()
            .filter(|&fid| {
                assembled.module.function_by_id(fid).map(|f| f.is_declaration()).unwrap_or(true)
            })
            .collect();
        if !declarations.is_empty() {
            // Trust (absent-callee Stage 3): the fenced UC adjudication is SEMANTICS now — the
            // sanctioned graduation of the Stage-1.5 probe, per
            // docs/design/2026-08-31-absent-callee-adjudication.md §6 stages 2-3. It runs
            // unconditionally (a verdict cannot depend on the tracing level), traces every
            // outcome exactly as the probe did (single emission — the dead-path probe below no
            // longer calls it), and mints `DiffMode::AgreedUninterpretedCallee` — NEVER plain
            // `Agreed` — only when every sampled leg agreed under the full no-channel fence
            // and the count/shape pairing. Every other outcome keeps the skip verbatim.
            let uc = build_expected_absent_bundle(r, &closure, &declarations, records, assembled)
                .ok()
                .and_then(|(bundle, entry_slot)| {
                    row1_uc_probe(
                        r,
                        entry,
                        &declarations,
                        assembled,
                        &mut scratch,
                        &bundle,
                        entry_slot,
                        uc_events,
                    )
                });
            // Trust (slice 20 ride-along b): the row-1 DEAD-PATH probe stays an instrument,
            // behind tracing — its outcome is a measurement, not a verdict.
            if tracing::enabled!(tracing::Level::DEBUG) {
                row1_dead_path_probe(r, entry, &closure, &declarations, records, assembled);
            }
            if let Some((samples, detail)) = uc {
                verdicts.push(SeamVerdict {
                    def_index: r.def_index,
                    equal: false,
                    samples,
                    mode: DiffMode::AgreedUninterpretedCallee,
                    note: detail,
                });
                continue;
            }
            // Trust (B8 step 1): NAME the blockers. Everything before the `[blockers: …]` marker
            // is the pre-split string byte for byte, because three published analyses quote it as
            // a substring and the scorecard's legacy rule still matches on it.
            verdicts.push(skip(
                r.def_index,
                &format!(
                    "seam-deferred body: reachable callee closure includes an \
                     extern/declaration-only callee (no local body to link) [blockers: {}]; \
                     crate-seam interpretation not asserted (coverage-only)",
                    blocker_summary(assembled, &declarations)
                ),
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
        // `mir_snapshot`. Any missing snapshot => callee-set asymmetry => fail-closed skip.
        //
        // Trust (slice 20): a PENDING-CONST callee is no longer an instance of that. It used to
        // be — `compare` returned `None` for such a body, so any deferred caller reaching one
        // lost its whole verdict to this asymmetry skip — and the parenthetical here named it as
        // the example. Moving the pending-const gate below the extraction gives those bodies a
        // snapshot like every other clean body, so the example is now stale and is removed
        // rather than left to mislead. What remains genuinely missing here is a callee whose
        // record never reached extraction at all (unsupported shapes, or the unrevealed-opaque
        // guard), which is the real asymmetry this gate is for.
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
        // Trust (vtable slice 12): same order as the hook's single-body path — the array
        // InsertField→InsertElement respell runs BEFORE classification so the Array
        // dead-seed walk sees the interpreter-native form.
        differential::rewrite_array_insert_fields(&mut bundle);
        // Trust (absent-callee Stage 0, instrument only): the TRACED classifier, so
        // the skip note names WHICH Undef broke the dead-seed proof. This is the
        // number the absent-callee design needs priced: of the live havocs, how many
        // are the ABSENT-CALLEE result Undef versus an unrelated havoc. Same
        // classification, same skip; only the note gains the offender.
        let bundle = match differential::classify_undefs_traced(&bundle) {
            (differential::UndefClass::Live, offender) => {
                verdicts.push(skip(
                    r.def_index,
                    &format!(
                        "seam-deferred body: MIR oracle bundle carries a LIVE havoc \
                         (`Inst::Undef` outside the proven-dead-seed shape){}; coverage-only \
                         skip — NOT a THIR divergence",
                        offender.map(|o| format!(" — offender: {o}")).unwrap_or_default()
                    ),
                ));
                continue;
            }
            (differential::UndefClass::DeadSeeds, _) => differential::substitute_dead_seeds(bundle),
            (differential::UndefClass::None, _) => bundle,
        };
        // Trust (vtable slice 6): the seam mirrors the hook's single-body preprocessing
        // step for step — same slot after the dead-seed substitution, same differential-
        // local scope (the bundle is this comparison's own assembly). The call-bearing
        // promoted-borrow mains (regions-reassign-let-bound-pointer, macro-named-default)
        // carry the once-stored escaping slot in the ENTRY body and reach the tail gate
        // only here, so a hook-only rewrite would leave the seam population unaligned.
        let mut bundle = bundle;
        differential::respell_promoted_slots_as_globals(&mut bundle);

        // step 8 — verdict.
        //
        // Trust (step 2 increment 4b, owner ruling D18 OD-1): a DROP is an uninterpreted EVENT
        // here, not an instruction the interpreter runs (it refuses `Inst::Drop` with a
        // `TypeError`, which would read as a THIR defect). The THIR side is interpreted with its
        // drops removed — the MIR side's drop glue is neutral in this differential already — so
        // the verdict is about the value flow AROUND the drops, and the drops themselves are
        // compared with rustc's elaborated drop points, event by event, by the
        // effect-conservation gate (`effect_conservation::drop_leg`, `drop_oracle.rs`), which
        // refuses the body for codegen and strict on any difference. No body is excluded.
        //
        // Trust (R8-SEAM): the THIR side is the working copy with exactly the blocks
        // `module_without_drops(&assembled.module, &closure)` changes patched in (none when it
        // returns `None`), so it is that module's content without a whole-module copy per body;
        // `compare_entries_in_place` appends and removes the pointer lane's wrappers itself.
        let patches = scratch.drop_patches(&closure);
        let (mut rep, wrapped) = scratch.compare_patched(patches, |work| {
            differential::compare_entries_in_place(
                work,
                entry,
                &mut bundle,
                FuncId::new(entry_slot as u32),
            )
        });
        scratch.stats.wrapped += usize::from(wrapped);
        // Trust: `compare_entries` is the classification authority. In particular, a typed
        // `MirOracle` result is never reclassified by matching its human-readable note. Structural
        // signature comparison already resolves module-local ids through each module's own tables,
        // and the producer emits canonical zero-result unit calls, so neither case needs a seam-only
        // exception. Any remaining signature/result-arity mismatch is a genuine lowering defect.
        if rep.mode == DiffMode::Agreed {
            // Trust (slice 20): the seam population is no longer call-bearing bodies alone, so
            // the note names the reason this body was deferred rather than asserting the one
            // that used to be the only possibility. A pending-const body may be call-FREE, and
            // a note that called it "call-bearing" would be false on its face and would also
            // mis-attribute the lane in every downstream reading of the log.
            let why = if r.pending_consts.is_empty() {
                "call-bearing body linked at crate finalize"
            } else if r.contains_call {
                "call-bearing pending-const body linked and const-patched at crate finalize"
            } else {
                "pending-const body re-adjudicated after finalizer const patching"
            };
            rep.notes.push(format!(
                "THIR-trust-ir == MIR-trust-ir on {} sampled input(s) (seam differential: {why})",
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
    if uc_events.is_some() {
        // The cross-check's restoration witness: every comparison restored what it patched.
        scratch.stats.restored = scratch.work.as_ref().is_none_or(|work| work == scratch.base);
    }
    (verdicts, scratch.stats)
}

/// Trust (R8-SEAM): one row-1 UC probe outcome, exactly as `row1_uc_probe` traces it.
#[derive(Debug, Clone, PartialEq, Eq)]
struct UcProbeEvent {
    def_index: u32,
    outcome: String,
    samples: usize,
    detail: String,
}

/// Trust (R8-SEAM): what the seam's working copy did in one pass.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
struct SeamScratchStats {
    /// Whole-module copies made (one per crate at most).
    copies: usize,
    /// Comparisons run on the working copy.
    comparisons: usize,
    /// Of them, UC probe legs (their call sites substituted by block patches).
    uc_legs: usize,
    /// Of them, comparisons whose closure carried drops (removed by block patches).
    drop_strips: usize,
    /// Blocks patched in, summed over comparisons.
    patched_blocks: usize,
    /// Comparisons whose pointer lane appended (and removed) the materialized-referent wrappers.
    wrapped: usize,
    /// The working copy equals the assembled module after the pass (checked only when
    /// `uc_events` is given, which is the cross-check's run).
    restored: bool,
}

/// Trust (R8-SEAM, `docs/DECISION_QUEUE.md`, taken 2026-10-05): the seam's ONE working copy of
/// the assembled crate module, and the once-built indices its patches are read from.
///
/// Before R8-SEAM the seam copied the WHOLE assembled module at three sites:
/// * `row1_uc_probe`, once per sample leg, to substitute the bodyless callees' call sites;
/// * `module_without_drops`, once per drop-bearing closure, to remove the drops the reference
///   interpreter refuses;
/// * `differential::build_pointee_wrapper`, once per pointer-lane comparison, to append the
///   materialized-referent wrapper.
///
/// Measured on `core` (`docs/design/2026-10-02-step2-inc6-trust-ir-in-metadata.md`, step 6.0
/// and its R8-SEAM entry), those copies and their drops were most of the producer's cost.
///
/// Every comparison now runs on `work`, a copy of `base` made once, on first use. A comparison
/// PATCHES exactly the blocks its leg or its drop removal changes (each with the body the old
/// copy carried there), hands `work` to `differential::compare_entries_in_place` (which appends
/// and removes the pointer lane's wrapper itself), and RESTORES what it patched — also on unwind.
/// Between comparisons `work` is content-identical to `base`, so each comparison sees a module
/// content-identical to the copy the pre-R8-SEAM site built, and computes the same report from
/// it: it samples the same, refuses the same and admits nothing new. The pre-R8-SEAM
/// implementation is kept, verbatim, as the cross-check oracle in `seam_reference.rs`, which
/// the TEST-ONLY `-Ztrust-ir-seam-reference` option runs beside this one.
struct SeamScratch<'m> {
    base: &'m Module,
    work: Option<Module>,
    /// Every `Inst::Call` of `base` whose callee is a bodyless declaration, keyed by callee, each
    /// list in module order. Built once, on first use.
    decl_calls: Option<FxHashMap<FuncId, Vec<DeclCallSite>>>,
    /// `FuncId` -> every position in `base.functions` holding that id, ascending. Built once.
    positions: Option<FxHashMap<FuncId, Vec<usize>>>,
    stats: SeamScratchStats,
}

/// Trust (R8-SEAM): one call site of a bodyless declaration, at `base.functions[func]
/// .blocks[block].body[node]`. The derived order is module order.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct DeclCallSite {
    func: usize,
    block: usize,
    node: usize,
    callee: FuncId,
    /// The call node's result count.
    results: usize,
}

/// Trust (R8-SEAM): the body one comparison installs at `functions[func].blocks[block]`.
#[derive(Debug, Clone, PartialEq)]
struct BlockPatch {
    func: usize,
    block: usize,
    body: Vec<InstrNode>,
}

impl<'m> SeamScratch<'m> {
    fn new(base: &'m Module) -> Self {
        SeamScratch {
            base,
            work: None,
            decl_calls: None,
            positions: None,
            stats: SeamScratchStats::default(),
        }
    }

    /// Every `Inst::Call` of the base whose callee is one of `declarations`, in module order —
    /// the nodes the pre-R8-SEAM producer-side walk of `row1_uc_probe` matched against its
    /// `decl_set`, in the order it met them. (Every member of that set resolves to a bodyless
    /// function by the time a leg runs: the fence returns `uc-unfenced` "declaration
    /// unresolvable" first, and the step-2 gate puts a resolving function in `declarations` only
    /// when it is bodyless. So the index, which keeps the calls whose callee resolves to a
    /// bodyless function, holds every node that walk could match.)
    fn decl_call_sites(&mut self, declarations: &[FuncId]) -> Vec<DeclCallSite> {
        let base = self.base;
        let index = self.decl_calls.get_or_insert_with(|| {
            let mut index: FxHashMap<FuncId, Vec<DeclCallSite>> = FxHashMap::default();
            for (func, f) in base.functions.iter().enumerate() {
                for (block, b) in f.blocks.iter().enumerate() {
                    for (node, n) in b.body.iter().enumerate() {
                        let Inst::Call { callee, .. } = &n.inst else { continue };
                        if base.function_by_id(*callee).is_some_and(Function::is_declaration) {
                            index.entry(*callee).or_default().push(DeclCallSite {
                                func,
                                block,
                                node,
                                callee: *callee,
                                results: n.results.len(),
                            });
                        }
                    }
                }
            }
            index
        });
        let wanted: BTreeSet<FuncId> = declarations.iter().copied().collect();
        let mut sites: Vec<DeclCallSite> =
            wanted.iter().filter_map(|d| index.get(d)).flatten().copied().collect();
        sites.sort_unstable();
        sites
    }

    /// Every position in the base's function table that holds `id`, ascending.
    fn positions_of(&mut self, id: FuncId) -> &[usize] {
        let base = self.base;
        let positions = self.positions.get_or_insert_with(|| {
            let mut positions: FxHashMap<FuncId, Vec<usize>> = FxHashMap::default();
            for (at, f) in base.functions.iter().enumerate() {
                positions.entry(f.id).or_default().push(at);
            }
            positions
        });
        positions.get(&id).map_or(&[], Vec::as_slice)
    }

    /// The blocks `module_without_drops(base, closure)` changes, each with the drop-free body
    /// that function's copy carries there; empty when it returns `None` (no closure member, as
    /// `function_by_id` resolves it, carries a drop). That function removes every `Inst::Drop`
    /// from every function whose id is in `closure`, which changes exactly the blocks of those
    /// functions that hold one.
    fn drop_patches(&mut self, closure: &[FuncId]) -> Vec<BlockPatch> {
        let is_drop = |n: &InstrNode| matches!(n.inst, Inst::Drop { .. });
        let has_drop = |f: &Function| f.blocks.iter().flat_map(|b| b.body.iter()).any(is_drop);
        let base = self.base;
        if !closure.iter().any(|&fid| base.function_by_id(fid).is_some_and(has_drop)) {
            return Vec::new();
        }
        let mut at: BTreeSet<usize> = BTreeSet::new();
        for &fid in closure {
            at.extend(self.positions_of(fid).iter().copied());
        }
        let mut patches = Vec::new();
        for func in at {
            for (block, b) in base.functions[func].blocks.iter().enumerate() {
                if b.body.iter().any(is_drop) {
                    let body = b.body.iter().filter(|n| !is_drop(n)).cloned().collect();
                    patches.push(BlockPatch { func, block, body });
                }
            }
        }
        if !patches.is_empty() {
            self.stats.drop_strips += 1;
        }
        patches
    }

    /// The blocks the UC substitution changes: at each `(site, Some(inst))` the call node with
    /// its instruction replaced by `inst`, at each `(site, None)` the call node removed — what
    /// the pre-R8-SEAM producer-side walk did to its copy, node for node. `substitution` is in
    /// module order.
    fn substitution_patches(&self, substitution: &[(DeclCallSite, Option<Inst>)]) -> Vec<BlockPatch> {
        let mut patches: Vec<BlockPatch> = Vec::new();
        let mut i = 0;
        while i < substitution.len() {
            let (func, block) = (substitution[i].0.func, substitution[i].0.block);
            let mut j = i;
            while j < substitution.len()
                && (substitution[j].0.func, substitution[j].0.block) == (func, block)
            {
                j += 1;
            }
            let group = &substitution[i..j];
            let original = &self.base.functions[func].blocks[block].body;
            let mut body = Vec::with_capacity(original.len());
            let mut next = group.iter().peekable();
            for (at, n) in original.iter().enumerate() {
                match next.next_if(|(site, _)| site.node == at) {
                    Some((_, Some(inst))) => {
                        let mut n = n.clone();
                        n.inst = inst.clone();
                        body.push(n);
                    }
                    Some((_, None)) => {}
                    None => body.push(n.clone()),
                }
            }
            patches.push(BlockPatch { func, block, body });
            i = j;
        }
        patches
    }

    /// Run `compare` on the working copy with `patches` installed, then restore it — also on
    /// unwind. The restore also drops anything appended past the base's function, func-type and
    /// obligation tables (`compare_entries_in_place` appends its wrappers there and removes them
    /// itself), so a comparison that appended leaves no trace in the next one.
    fn compare_patched<R>(
        &mut self,
        patches: Vec<BlockPatch>,
        compare: impl FnOnce(&mut Module) -> R,
    ) -> R {
        struct Restore<'w> {
            work: &'w mut Module,
            saved: Vec<BlockPatch>,
            functions: usize,
            func_types: usize,
            obligations: usize,
        }
        impl Drop for Restore<'_> {
            fn drop(&mut self) {
                self.work.functions.truncate(self.functions);
                self.work.func_types.truncate(self.func_types);
                self.work.proof_obligations.truncate(self.obligations);
                for saved in self.saved.drain(..).rev() {
                    self.work.functions[saved.func].blocks[saved.block].body = saved.body;
                }
            }
        }
        let base = self.base;
        let stats = &mut self.stats;
        let work = self.work.get_or_insert_with(|| {
            stats.copies += 1;
            base.clone()
        });
        stats.comparisons += 1;
        stats.patched_blocks += patches.len();
        let mut guard = Restore {
            saved: Vec::with_capacity(patches.len()),
            functions: base.functions.len(),
            func_types: base.func_types.len(),
            obligations: base.proof_obligations.len(),
            work,
        };
        for patch in patches {
            let original = std::mem::replace(
                &mut guard.work.functions[patch.func].blocks[patch.block].body,
                patch.body,
            );
            guard.saved.push(BlockPatch { func: patch.func, block: patch.block, body: original });
        }
        compare(&mut *guard.work)
    }
}

/// Trust (step 2 increment 4b, owner ruling D18 OD-1): the seam's THIR side with every
/// `Inst::Drop` of the closure's functions removed, or `None` when the closure carries no drop.
/// A drop is an uninterpreted EVENT in the seam differential; the effect-conservation gate
/// compares the events with rustc's elaborated drop points (see the call site, step 8).
fn module_without_drops(module: &Module, closure: &[FuncId]) -> Option<Module> {
    let has_drop = |f: &Function| {
        f.blocks.iter().flat_map(|b| b.body.iter()).any(|n| matches!(n.inst, Inst::Drop { .. }))
    };
    if !closure.iter().any(|&fid| module.function_by_id(fid).is_some_and(has_drop)) {
        return None;
    }
    let mut m = module.clone();
    for f in m.functions.iter_mut().filter(|f| closure.contains(&f.id)) {
        for b in &mut f.blocks {
            b.body.retain(|n| !matches!(n.inst, Inst::Drop { .. }));
        }
    }
    Some(m)
}

/// Trust (B8 step 1): render a deferred body's bodyless reachable callees as a counted,
/// deterministically-ordered [`DeclKind`] census for the step-2 skip note — e.g.
/// `extern=3, local-unlowered=1`.
///
/// The counts are DISTINCT reachable callees, not call sites: `declarations` is filtered out of
/// the step-1 BFS closure, which dedups on `FuncId`. So `extern=3` means three different bodyless
/// functions are reachable, however many times each is called. That is the right unit here — the
/// question the census answers is what would have to be MODELLED to clear the gate.
///
/// This is the whole of the measurement. Everything downstream (the scorecard's
/// `clean-skip-seam-decl-*` split, the dominant/sole/participation census, the ranking of what
/// Step 2 should be) is a pure function of this string.
///
/// Three properties it must have, each of which a test pins:
///
/// * **Deterministic.** Classes are emitted in [`DeclKind::ALL`] order, never in the order the
///   BFS happened to walk the closure, so the note is stable across runs and the artifact stays
///   diffable against a control.
/// * **Total.** A declaration whose key this taxonomy cannot parse — or, defensively, a closure
///   member that is not in the module at all, which the step-2 filter admits via its
///   `unwrap_or(true)` — is counted under `unclassified`. It is NEVER attributed to a
///   neighbouring class: the census exists to expose drift between this taxonomy and
///   `resolve_callee`, and quietly rounding a stranger into `extern` would hide precisely that.
///   `unclassified` is expected to be 0; a non-zero count is a finding, not a rounding error.
/// * **Non-empty.** The caller only reaches this with `!declarations.is_empty()`, so the marker
///   always carries at least one class and the scorecard can distinguish "split" from "this
///   artifact predates the split" by presence alone.
fn blocker_summary(assembled: &Assembled, declarations: &[FuncId]) -> String {
    let mut counts = [0usize; DeclKind::ALL.len()];
    let mut unclassified = 0usize;
    for fid in declarations {
        let kind = assembled
            .decl_keys
            .iter()
            .find(|declaration| declaration.func_id == *fid)
            .and_then(|declaration| DeclKind::from_key(&declaration.key));
        match kind {
            Some(k) => counts[DeclKind::ALL.iter().position(|c| *c == k).unwrap()] += 1,
            None => unclassified += 1,
        }
    }
    let mut parts: Vec<String> = DeclKind::ALL
        .iter()
        .zip(counts)
        .filter(|(_, n)| *n > 0)
        .map(|(k, n)| format!("{}={}", k.prefix(), n))
        .collect();
    if unclassified > 0 {
        parts.push(format!("unclassified={unclassified}"));
    }
    parts.join(", ")
}

/// The note of the seam-differential SKIP a body with a non-empty `unsupported` list gets —
/// split BY CAUSE, never by verdict: every arm is the same coverage-only skip, and the caller
/// records it with the same `skip(..)` + `continue` whatever the note says.
///
/// Trust (owner call 2026-09-17(b)): the unsignable-edge refusal has its own note, because
/// `scripts/trust_ir_producer_scorecard.py` buckets "finalizer const resolution failed" as
/// `clean-skip-pending-const-unresolved` and a population with nothing to do with const
/// evaluation must not inflate it. Trust (WS5.2): the link-identity refusals
/// (`NoLinkTimeSymbol(` / `LinkSymbolCollision(`) get their OWN note for the same reason; the
/// unsignable-edge note keeps precedence when a body carries both, so that bucket is exactly
/// what it was before WS5.2.
fn unsupported_body_skip_note<C>(unsupported: &[(String, C)]) -> &'static str {
    let unsignable_edge =
        unsupported.iter().any(|(reason, _)| reason.starts_with(UNSIGNABLE_BODY_REASON_TAG));
    let link_identity = unsupported.iter().any(|(reason, _)| {
        reason.starts_with(crate::link_symbol::NO_LINK_SYMBOL_TAG)
            || reason.starts_with(crate::link_symbol::LINK_SYMBOL_COLLISION_TAG)
    });
    if link_identity && !unsignable_edge {
        "seam-deferred body: refused for link-time symbol identity (no computable \
         symbol, or a call edge whose declaration would share its symbol with \
         another row); coverage-only skip"
    } else if unsignable_edge {
        "seam-deferred body: refused for minting an unsignable Rust-ABI call edge \
         (the callee's declaration has no signature this producer can state); \
         coverage-only skip"
    } else {
        "seam-deferred body: finalizer const resolution failed (body marked \
         unsupported by resolve_pending_consts; placeholder never patched); \
         coverage-only skip"
    }
}

/// The name the MIR ORACLE knows a module function by (WS5.2): its DEF PATH. Since
/// `Function.name` became the link-time symbol, the def path is `display_path`; a row with no
/// display path (the identity-less `!unknown_callee_N` / `!ambiguous_callee_N` declarations)
/// keeps its name, exactly as before. [`build_expected_absent_bundle`] keys its
/// expected-absent set on this, so the oracle's input is the string it always was.
fn oracle_callee_name(function: &Function) -> String {
    function.display_path.clone().unwrap_or_else(|| function.name.clone())
}

/// Trust (slice 20 ride-along b): the ROW-1 DEAD-PATH PROBE. **Instrument only — ships no
/// behaviour.**
///
/// # The question
///
/// `run_seam_differentials` step 2 refuses every deferred body whose reachable-callee closure
/// contains a bodyless (extern / unresolved / declaration-only) callee. That refusal is correct
/// as a refusal — there is no body to link, and a reachable vararg declaration would err
/// `SignatureMismatch` in the interpreter and surface as a FALSE oracle verdict. But it is
/// STATIC: it asks whether such a callee exists in the closure, never whether any sampled
/// execution reaches it.
///
/// Those two questions come apart exactly when the call sits behind a guard the samples do not
/// satisfy — a `panic!` arm, an error path, a `debug_assert`. For such a body the declaration is
/// present but dead, and interpretation-equivalence is perfectly assertible.
///
/// # What it measures
///
/// The bundle is rebuilt with the bodyless callees named EXPECTED-ABSENT (so the bridge demotes
/// their obligation instead of minting the fatal marker step 6 aborts on), the two static aborts
/// that would pre-empt the dynamic question are bypassed, and the comparison is run. A body that
/// reaches `Agreed` proves no sample executed the absent-callee `Assert(false)` — the interpreter
/// would have trapped on it. That count is the number this probe exists to produce.
///
/// # What it is NOT
///
/// It is not a verdict, and nothing it computes is written anywhere a verdict is read from. The
/// caller pushes the identical step-2 skip either way. `Agreed` here means "would have been
/// adjudicable", and the honest reading of the count is a LOWER BOUND on the dead-path
/// population: a body can also fail to reach `Agreed` for an ordinary oracle-incapacity reason
/// that has nothing to do with the absent callee. Under-counting is the right direction for a
/// number whose purpose is to decide whether to spend a campaign.
///
/// # MEASURED LIMITATION — read this before quoting the number (2026-08-19, n=104)
///
/// The first run returned `absent-path-dead-agreed = 0` out of 104 probed bodies, split
/// `oracle-live-havoc` 55 (52.9%), `not-run` 28 (26.9%), `bundle-failed` 21 (20.2%).
///
/// The 0 is real and decision-relevant: **no row-1 body is adjudicable through the seam
/// machinery as it stands.** But the DOMINANT bucket is an artifact of this probe, not an
/// independent obstacle, and saying otherwise would overstate what was measured. The bridge
/// encodes an absent callee as `Assert(false)` + NoPanic marker + a HAVOC RESULT, and that
/// havoc result is an `Inst::Undef` (trust-ir-bridge lower.rs ~19527, ~28385). A bare scalar
/// `Undef` can never satisfy `undef_is_dead_seed` (which demands an aggregate InsertField
/// chain), so `classify_undefs` returns `Live` and this function returns BEFORE the interpreter
/// runs. For those 55 bodies the dynamic question was never actually asked — they were refused
/// by the absent callee's own encoding.
///
/// So this probe answers "is row 1 cheap to unlock?" (no — lifting the static declaration gate
/// alone yields zero) but it does NOT answer "is the absent call on a dead path?" for the
/// majority of the population. Making row 1 adjudicable requires MODELLING AN ABSENT CALLEE'S
/// RESULT as something the comparison tolerates — a fresh symbolic the dead-seed proof accepts,
/// or a reachability test on the `Assert` itself — not merely relaxing step 2. Anyone extending
/// this should fix that first; otherwise the same 53% will keep being counted as evidence for a
/// conclusion it cannot support.
/// Trust (absent-callee Stage 1.5, INSTRUMENT ONLY — this prices the design's
/// conversion rate; it mints no verdict, touches no artifact row, and its whole
/// output is one tracing event): the two-sided UNINTERPRETED-CALLEE probe.
///
/// Both sides of the seam comparison model an absent callee's result as the
/// SAME fixed constant, per docs/design/2026-08-31-absent-callee-adjudication.md
/// §2(c): the producer's `Inst::Call` to a bodyless declaration is rewritten to
/// `Inst::Const { ret_ty, v }` binding the same result (a zero-result call is
/// deleted), and the oracle's absent-callee encoding — `Assert(const false)` +
/// `Inst::Undef` — is neutralized to the same constant. That single substitution
/// retires BOTH gates the Stage 0 pricing found binding: the vararg
/// `SignatureMismatch` (no vararg call remains to execute) and the observation
/// tail gate's no-executable-body arm (no reachable edge to a declaration
/// remains). Run at TWO leg values (0 and 1) so an agreement that holds only at
/// zero does not read as an agreement; `uc-agreed` means both legs agreed.
///
/// FENCED, fail-closed to `uc-unfenced`: a declaration with more than one
/// return, a non-scalar return, or an oracle Undef whose type has no scalar
/// constant (the ~300 aggregate offenders Stage 0 counted) refuses the whole
/// probe row — the same no-channel posture the design's verdict-bearing lane
/// will need, priced here first.
/// Trust (absent-callee Stage 3): build the ORACLE bundle with the bodyless callees declared
/// expected-absent — the exact construction `row1_dead_path_probe` has always used, extracted
/// so the Stage-3 adjudication can run UNCONDITIONALLY (it is semantics now, not a probe)
/// while the dead-path probe stays behind tracing. `Err` carries the probe-outcome name for
/// the caller's trace line.
fn build_expected_absent_bundle(
    r: &BodyRecord,
    closure: &[FuncId],
    declarations: &[FuncId],
    records: &[BodyRecord],
    assembled: &Assembled,
) -> Result<(trust_ir::Module, usize), &'static str> {
    use crate::differential;

    // Trust (WS5.2): the MIR oracle names a callee by its DEF PATH, which is a declaration's
    // `display_path` now that `Function.name` is the link-time symbol — so the expected-absent
    // set is read from there (`oracle_callee_name`), keeping this probe's input exactly what it
    // was.
    let absent: std::collections::HashSet<String> = declarations
        .iter()
        .filter_map(|&fid| assembled.module.function_by_id(fid).map(oracle_callee_name))
        .collect();
    let mut members: Vec<(u32, &trust_types::VerifiableFunction)> = Vec::new();
    for &fid in closure {
        if declarations.contains(&fid) {
            continue;
        }
        let Some(di) = assembled.assigned.get(fid.as_usize()).map(|(d, _)| *d) else {
            return Err("member-not-spliced");
        };
        let Some(vf) = records
            .binary_search_by_key(&di, |rec| rec.def_index)
            .ok()
            .and_then(|i| records[i].mir_snapshot.as_ref())
        else {
            return Err("member-snapshot-missing");
        };
        members.push((di, vf));
    }
    members.sort_by_key(|(di, _)| *di);
    let Some(entry_slot) = members.iter().position(|(di, _)| *di == r.def_index) else {
        return Err("entry-not-in-bundle");
    };
    let funcs: Vec<trust_types::VerifiableFunction> =
        members.iter().map(|(_, vf)| (*vf).clone()).collect();
    let Ok(mut bundle) = trust_ir_bridge::lower_to_trust_ir_functions_with_expected_absent(
        format!("{}::row1probe", assembled.module.name),
        &funcs,
        &absent,
    ) else {
        return Err("bundle-failed");
    };
    differential::rewrite_bool_not_icmp(&mut bundle);
    differential::rewrite_array_insert_fields(&mut bundle);
    Ok((bundle, entry_slot))
}

/// Trust (H1, 2026-09-16): the per-DECLARATION half of `row1_uc_probe`'s no-channel fence —
/// conjuncts 1 and 2 of `docs/design/2026-08-31-absent-callee-adjudication.md` §6 over one
/// declaration's signature — preceded by the check the fence was MISSING. Returns the
/// declaration's planned return type (`None` for a zero-result declaration) or the
/// `uc-unfenced` detail the caller traces.
///
/// WHY H1 EXISTS. Conjunct 1 iterates `ft.params`. A bodyless declaration the producer could
/// not sign is emitted `params: [] + is_vararg: true` — the params-side "unknown" encoding,
/// which trust-ir v41 refuses at finalization (`RustAbiVararg`). But this probe runs at the
/// seam, BEFORE finalization refuses (crate_module's seam differential precedes
/// `unsignable_declaration_refusals`), it traces `uc-agreed` through the same event the
/// scorecard consumes, and under `-Ztrust-policy=advisory` the crate keeps compiling with the
/// vararg row in place. Measured: nothing on the path read `ft.is_vararg`, so conjunct 1
/// iterated an EMPTY parameter list and passed — "every argument is a scalar" was true of a
/// declaration whose arguments were unknown. That is a vacuous fence, not a fence. A vararg
/// declaration now refuses by name before conjunct 1 can look at its empty list.
///
/// Pure on purpose — see `uc_declaration_fence_refuses_a_vararg_row_before_conjunct_1`.
fn uc_declaration_fence(ft: &FuncTy) -> Result<Option<Ty>, String> {
    use crate::differential;
    // H1 — the unknown-signature encoding carries no parameter facts to fence.
    if ft.is_vararg {
        return Err("vararg declaration".to_string());
    }
    // conjunct 1 — every argument a by-value interpretable scalar: no pointer, no
    // aggregate, no Func, no ZST env. Copies of scalars carry no channel.
    if let Some(bad) = ft.params.iter().find(|t| !differential::is_interpretable_scalar(t)) {
        return Err(format!("non-scalar callee param {bad}"));
    }
    // conjunct 2 — the return is one interpretable scalar, or absent.
    match ft.returns.len() {
        0 => Ok(None),
        1 => {
            let rt = &ft.returns[0];
            // Trust (wave-UCF): the admissible return set is the scalar set PLUS the
            // fat-pointer kinds — the latter modeled at their single two-zero constant
            // (see `const_of`). Aggregates (struct/enum/tuple) stay refused: their
            // substitution needs a per-field seeding and a STRUCTURAL type pairing
            // across two independently-numbered def tables, each a design decision no
            // one has reviewed.
            if !differential::is_interpretable_scalar(rt) && !matches!(rt, Ty::FatPtr(_)) {
                return Err(format!("non-scalar callee ret {rt}"));
            }
            Ok(Some(rt.clone()))
        }
        n => Err(format!("declaration returns {n} values")),
    }
}

/// Trust (absent-callee Stage 2→3): the fenced UNINTERPRETED-CALLEE adjudicator. Returns
/// `Some((samples, detail))` — and ONLY then may the caller mint
/// `DiffMode::AgreedUninterpretedCallee` — when every sampled leg of the substitution agreed
/// under the full no-channel fence of `docs/design/2026-08-31-absent-callee-adjudication.md`
/// §6 (conjuncts 1–5) plus the Stage-2 count/shape pairing. Every refusal and every
/// non-agreeing outcome traces exactly as the Stage-1.5 probe did and returns `None`, so the
/// scorecard's disclosed adjudication line keeps its full population.
///
/// The legs are `differential::sample_values` over the (single, fence-enforced) declared
/// return type — the design's "sample_values(ret_ty) outer loop" — not the probe's fixed
/// {0, 1}; a plan whose every site is zero-result runs one leg (nothing is substituted, the
/// deletion is the whole model).
///
/// Trust (R8-SEAM, 2026-10-05): the producer side's substitution is a set of block patches over
/// the seam's ONE working copy ([`SeamScratch`]), read from its once-built index of the
/// declarations' call sites, instead of a walk of a whole-module copy per leg. The patched copy
/// is the module that walk built, node for node, so every leg compares what it compared. Each
/// outcome is also pushed to `uc_events` when given (the cross-check's run).
#[allow(clippy::too_many_arguments)]
fn row1_uc_probe(
    r: &BodyRecord,
    entry: FuncId,
    declarations: &[FuncId],
    assembled: &Assembled,
    scratch: &mut SeamScratch<'_>,
    oracle_bundle: &trust_ir::Module,
    entry_slot: usize,
    uc_events: Option<&std::cell::RefCell<Vec<UcProbeEvent>>>,
) -> Option<(usize, String)> {
    use crate::differential::{self, DiffMode};
    use trust_ir::{Constant, Inst, Ty};

    let emit = |outcome: &str, samples: usize, detail: &str| {
        tracing::debug!(
            def_index = r.def_index,
            def_path = r.def_path.as_str(),
            declarations = declarations.len(),
            outcome,
            samples,
            detail,
            "trust-ir-lower: row1 UC probe"
        );
        if let Some(events) = uc_events {
            events.borrow_mut().push(UcProbeEvent {
                def_index: r.def_index,
                outcome: outcome.to_string(),
                samples,
                detail: detail.to_string(),
            });
        }
    };

    // The scalar constant for leg `v`, or None — the fence.
    fn const_of(ty: &Ty, v: i128) -> Option<Constant> {
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
            | Ty::Isize
            | Ty::Usize
            | Ty::Char => Some(Constant::Int(v)),
            // Trust (Stage 3): `Ty::Ptr` is DELIBERATELY absent — substituting a
            // pointer-returning callee with fabricated integer addresses would hand both
            // sides a value whose derefs trap "identically" only by construction of the
            // fabrication. A pointer return refuses the row as `uc-unfenced`, matching
            // the design's conjunct 2 (`is_interpretable_scalar` excludes `Ptr`).
            Ty::Bool => Some(Constant::Bool(v != 0)),
            Ty::F32 | Ty::F64 => Some(Constant::Float(v as f64)),
            Ty::Unit => Some(Constant::PhantomData),
            // Trust (wave-UCF): a FAT-POINTER return is modeled at the ONE constant trust-ir
            // fecd740 admits — the two-zero aggregate `[Int(0), Int(0)]`, the null/empty
            // fat value (`shape_matches_ty` refuses any nonzero word, and
            // `constant_to_value` materializes NullPtr data + the zero of the kind's own
            // metadata type). `v` is deliberately IGNORED: no other fat constant exists to
            // sample, so the leg selection below runs this type at a single leg, and the
            // per-row detail discloses single-value modeling. Both sides receive the same
            // constant; a callee whose real return is dereferenced would trap on BOTH sides
            // identically only for the null value — which is exactly the disclosed
            // uninterpreted-callee assumption, no stronger here than for scalars.
            Ty::FatPtr(_) => Some(Constant::Aggregate(vec![Constant::Int(0), Constant::Int(0)])),
            _ => None,
        }
    }

    // ---- Stage 3 no-channel fence, conjuncts 1/2/3/5 (4 is structural: after the
    // substitution no declaration call remains, so `compare_entries` runs the FULL
    // observation tail gate with nothing excused). Any miss traces `uc-unfenced` with the
    // conjunct named and the row stays a disclosed probe outcome, never a verdict. ----
    // Trust (wave-UCF2): a plan may span SEVERAL return types (`caller_str` reaches both a
    // `fatptr<str>`-returning extern and a bodyless `usize`-returning std helper — measured,
    // the single-type fence refused exactly that shape). Each site substitutes a value from
    // ITS OWN type's admissible sample list; a joint leg is one assignment across all sites,
    // and the leg count is the largest per-type list (shorter lists cycle). Every substituted
    // constant is well-formed for its own type by construction, so no ill-typed constant can
    // reach either module.
    let mut planned_ret_tys: Vec<Ty> = Vec::new();
    for &fid in declarations {
        let Some(decl) = assembled.module.function_by_id(fid) else {
            emit("uc-unfenced", 0, "declaration unresolvable");
            return None;
        };
        // conjunct 3 — one arity, no per-site result-count split.
        if decl.name.contains("|nres:") {
            emit("uc-unfenced", 0, &format!("arity-split declaration {}", decl.name));
            return None;
        }
        let Some(ft) = assembled.module.func_types.get(decl.ty.as_usize()) else {
            emit("uc-unfenced", 0, "declaration func_type unresolvable");
            return None;
        };
        // H1 + conjuncts 1 and 2, as the pure [`uc_declaration_fence`] so the vacuity H1
        // closes is pinned by a unit test rather than by a trace nobody reads.
        match uc_declaration_fence(ft) {
            Err(detail) => {
                emit("uc-unfenced", 0, &detail);
                return None;
            }
            Ok(Some(rt)) => {
                if !planned_ret_tys.iter().any(|t| *t == rt) {
                    planned_ret_tys.push(rt);
                }
            }
            Ok(None) => {}
        }
    }
    // conjunct 5 — no pointer-shaped channel on the CALLER's own entry: every entry param an
    // interpretable scalar.
    {
        let Some(ef) = assembled.module.function_by_id(entry) else {
            emit("uc-unfenced", 0, "entry unresolvable");
            return None;
        };
        let Some(eft) = assembled.module.func_types.get(ef.ty.as_usize()) else {
            emit("uc-unfenced", 0, "entry func_type unresolvable");
            return None;
        };
        if let Some(bad) = eft.params.iter().find(|t| !differential::is_interpretable_scalar(t))
        {
            emit("uc-unfenced", 0, &format!("non-scalar entry param {bad}"));
            return None;
        }
    }
    // The sampled legs: the design's `sample_values(ret_ty)` outer loop, generalized to a
    // JOINT leg over every planned return type. A fat-pointer type has exactly ONE
    // admissible constant (the two-zero null/empty fat value `const_of` mints ignoring the
    // leg), so its list is the singleton. Zero-result-only plans run one leg — the deletion
    // is the whole model.
    let mut ty_samples: Vec<(Ty, Vec<i128>)> = Vec::new();
    for rt in &planned_ret_tys {
        let vs = if matches!(rt, Ty::FatPtr(_)) {
            vec![0]
        } else {
            let vs = differential::sample_values(rt);
            if vs.is_empty() {
                emit("uc-unfenced", 0, &format!("no sample values for ret {rt}"));
                return None;
            }
            vs
        };
        ty_samples.push((rt.clone(), vs));
    }
    let leg_count = ty_samples.iter().map(|(_, vs)| vs.len()).max().unwrap_or(1);
    let value_for = |ty: &Ty, leg_idx: usize| -> i128 {
        ty_samples
            .iter()
            .find(|(t, _)| t == ty)
            .map(|(_, vs)| vs[leg_idx % vs.len()])
            .unwrap_or(0)
    };

    let mut legs: Vec<differential::DiffMode> = Vec::new();
    let mut last_note = String::new();
    let mut samples_total = 0usize;
    // Trust (Stage 2 pairing): the conjuncts the 16 measured uc-diverged rows exist to
    // justify — checked on the first leg (the counts are leg-invariant) and refused as
    // `uc-unpaired` rather than compared. (1) COUNT pairing: every producer call site
    // with a bound result must pair with exactly one oracle absent-callee `Undef`, and
    // every producer zero-result site with an oracle `Assert(false)` that has no Undef;
    // (2) SHAPE pairing: the multiset of producer return types must equal the multiset
    // of oracle Undef types — a divergence between two differently-typed constants is a
    // pairing artifact, not a producer defect, and must not be compared at all.
    let mut pairing_checked = false;
    // Trust (R8-SEAM): the call sites the producer-side walk below used to find by visiting every
    // node of a whole-module copy, from the scratch's once-built index, in the order it met them.
    let sites = scratch.decl_call_sites(declarations);
    for leg_idx in 0..leg_count {
        // ---- producer side: Call{decl} -> Const, as patches over the working copy ----
        let mut substitution: Vec<(DeclCallSite, Option<Inst>)> = Vec::with_capacity(sites.len());
        let mut prod_sites = 0usize;
        let mut prod_unit_sites = 0usize;
        let mut prod_ret_tys: Vec<String> = Vec::new();
        let mut unfenced: Option<String> = None;
        for site in &sites {
            let callee = &site.callee;
            prod_sites += 1;
            let rets: Vec<Ty> = assembled
                .module
                .function_by_id(*callee)
                .and_then(|d| assembled.module.func_types.get(d.ty.as_usize()).cloned())
                .map(|ft| ft.returns)
                .unwrap_or_default();
            match (rets.len(), site.results) {
                (0, 0) => {
                    substitution.push((*site, None));
                    prod_unit_sites += 1;
                }
                (1, 1) => match const_of(&rets[0], value_for(&rets[0], leg_idx)) {
                    Some(c) => {
                        prod_ret_tys.push(format!("{}", rets[0]));
                        substitution
                            .push((*site, Some(Inst::Const { ty: rets[0].clone(), value: c })));
                    }
                    None => {
                        unfenced = Some(format!("producer ret {}", rets[0]));
                    }
                },
                _ => {
                    unfenced = Some("producer arity".to_string());
                }
            }
        }
        // ---- oracle side: Assert(false) removed, Undef -> the same const ----
        let mut oracle = oracle_bundle.clone();
        let mut oracle_sites = 0usize;
        let mut oracle_asserts = 0usize;
        let mut oracle_undef_tys: Vec<String> = Vec::new();
        for f in &mut oracle.functions {
            for blk in &mut f.blocks {
                // value ids defined by `Const Bool(false)` in this block
                let false_ids: std::collections::HashSet<trust_ir::ValueId> = blk
                    .body
                    .iter()
                    .filter(|n| {
                        matches!(
                            &n.inst,
                            Inst::Const { value: Constant::Bool(false), .. }
                        )
                    })
                    .flat_map(|n| n.results.iter().copied())
                    .collect();
                let mut keep: Vec<bool> = Vec::with_capacity(blk.body.len());
                for node in &mut blk.body {
                    let mut retain = true;
                    match &node.inst {
                        Inst::Assert { cond, .. } if false_ids.contains(cond) => {
                            retain = false;
                            oracle_asserts += 1;
                        }
                        Inst::Undef { ty } => {
                            oracle_sites += 1;
                            oracle_undef_tys.push(format!("{ty}"));
                            match const_of(ty, value_for(ty, leg_idx)) {
                                Some(c) => {
                                    node.inst = Inst::Const { ty: ty.clone(), value: c };
                                }
                                None => {
                                    unfenced = Some(format!("oracle undef {ty}"));
                                }
                            }
                        }
                        _ => {}
                    }
                    keep.push(retain);
                }
                let mut it = keep.into_iter();
                blk.body.retain(|_| it.next().unwrap_or(true));
            }
        }
        if let Some(u) = unfenced {
            emit("uc-unfenced", 0, &u);
            return None;
        }
        if prod_sites == 0 && oracle_sites == 0 {
            emit("uc-no-sites", 0, "");
            return None;
        }
        if !pairing_checked {
            pairing_checked = true;
            let ret_sites = prod_sites - prod_unit_sites;
            if ret_sites != oracle_sites || prod_sites != oracle_asserts {
                emit(
                    "uc-unpaired",
                    0,
                    &format!(
                        "counts: prod {prod_sites} ({ret_sites} ret) vs oracle \
                         {oracle_asserts} asserts / {oracle_sites} undefs"
                    ),
                );
                return None;
            }
            let mut a = prod_ret_tys.clone();
            let mut b = oracle_undef_tys.clone();
            a.sort();
            b.sort();
            if a != b {
                emit("uc-unpaired", 0, &format!("ty multiset: {a:?} vs {b:?}"));
                return None;
            }
        }
        let patches = scratch.substitution_patches(&substitution);
        scratch.stats.uc_legs += 1;
        let (rep, wrapped) = scratch.compare_patched(patches, |work| {
            differential::compare_entries_in_place(
                work,
                entry,
                &mut oracle,
                FuncId::new(entry_slot as u32),
            )
        });
        scratch.stats.wrapped += usize::from(wrapped);
        samples_total += rep.samples_checked;
        last_note = rep.notes.last().cloned().unwrap_or_default();
        legs.push(rep.mode);
        if !matches!(legs.last(), Some(DiffMode::Agreed)) {
            break; // one non-agreeing leg decides the row
        }
    }
    let outcome = if legs.iter().all(|m| matches!(m, DiffMode::Agreed)) && legs.len() == leg_count
    {
        "uc-agreed"
    } else if legs.iter().any(|m| matches!(m, DiffMode::MirOracle)) {
        "uc-diverged"
    } else {
        "uc-not-run"
    };
    emit(
        outcome,
        samples_total,
        if outcome == "uc-not-run" { &last_note } else { "" },
    );
    if outcome == "uc-agreed" {
        let detail = format!(
            "agreed under the uninterpreted-callee substitution: {} declaration(s) modeled \
             as the same constant on both sides at {} sampled return value(s) ({} input \
             sample(s) total); no-channel fence conjuncts 1-5 + count/shape pairing held. NOT \
             plain agreement: the call sites themselves are erased by the substitution and \
             callee effects are assumed absent -- see docs/TCB.md",
            declarations.len(),
            leg_count,
            samples_total
        );
        return Some((samples_total, detail));
    }
    None
}

fn row1_dead_path_probe(
    r: &BodyRecord,
    entry: FuncId,
    closure: &[FuncId],
    declarations: &[FuncId],
    records: &[BodyRecord],
    assembled: &Assembled,
) {
    use crate::differential::{self, DiffMode};

    let emit = |outcome: &str, samples: usize| {
        tracing::debug!(
            def_index = r.def_index,
            def_path = r.def_path.as_str(),
            declarations = declarations.len(),
            outcome,
            samples,
            "trust-ir-lower: row1 dead-path probe"
        );
    };

    // The bundle build is shared with the Stage-3 adjudicator; each `Err` name is the
    // probe-outcome the inline build used to emit.
    let (bundle, entry_slot) = match build_expected_absent_bundle(
        r,
        closure,
        declarations,
        records,
        assembled,
    ) {
        Ok(pair) => pair,
        Err(outcome) => {
            emit(outcome, 0);
            return;
        }
    };

    // The two static aborts the real seam takes are DELIBERATELY not taken here. Step 6's
    // absent-marker abort is pre-empted by the expected-absent demotion above; step 7's
    // `oracle_has_const_false_assert` is the exact static test whose DYNAMIC counterpart is the
    // question — an unconditional-looking `Assert(false)` that no sample reaches is precisely a
    // dead path. Everything else mirrors the seam's preprocessing order step for step, so the
    // probe measures the same pipeline the campaign would have to use.
    // (The bool-not/array-insert rewrites ran inside the shared builder; the Stage-3
    // adjudicator now runs at the step-2 arm itself — unconditionally, once — so this
    // probe no longer calls it, which also keeps the scorecard's trace-line counts
    // single-emission.)
    let bundle = bundle;
    // Trust (absent-callee Stage 0, instrument only): traced, so the probe's
    // dominant bucket finally says WHICH havoc it is — the design's first
    // unpriced unknown ("of 497 havocs, how many are the absent-callee Undef").
    let bundle = match differential::classify_undefs_traced(&bundle) {
        (differential::UndefClass::Live, offender) => {
            tracing::debug!(
                def_index = r.def_index,
                def_path = r.def_path.as_str(),
                declarations = declarations.len(),
                outcome = "oracle-live-havoc",
                samples = 0usize,
                offender = offender.as_deref().unwrap_or(""),
                "trust-ir-lower: row1 dead-path probe"
            );
            return;
        }
        (differential::UndefClass::DeadSeeds, _) => differential::substitute_dead_seeds(bundle),
        (differential::UndefClass::None, _) => bundle,
    };
    let mut bundle = bundle;
    differential::respell_promoted_slots_as_globals(&mut bundle);

    let rep = differential::compare_entries(
        &assembled.module,
        entry,
        &bundle,
        FuncId::new(entry_slot as u32),
    );
    let outcome = match rep.mode {
        // The load-bearing bucket: every sample ran to completion without the interpreter
        // trapping on an absent callee, and both sides agreed.
        DiffMode::Agreed => "absent-path-dead-agreed",
        DiffMode::MirOracle => "divergence-or-trap",
        DiffMode::NotRun => "not-run",
        // `compare_entries` never mints the UC class (only the Stage-3 adjudicator does,
        // and it does not run under this probe); named so a future change cannot fold it
        // into an agreement bucket silently.
        DiffMode::AgreedUninterpretedCallee => "uc-mode-unexpected",
    };
    // Trust (absent-callee Stage 0, instrument only): on `not-run`, say WHY — the
    // design's second unpriced unknown ("of 211 not-runs, how many are the
    // observation tail gate vs fuel/signature/value-floor"). The differential's
    // last note is the refusing gate's own words.
    if matches!(rep.mode, DiffMode::NotRun) {
        tracing::debug!(
            def_index = r.def_index,
            def_path = r.def_path.as_str(),
            declarations = declarations.len(),
            outcome,
            samples = rep.samples_checked,
            why = rep.notes.last().map(String::as_str).unwrap_or(""),
            "trust-ir-lower: row1 dead-path probe"
        );
        return;
    }
    emit(outcome, rep.samples_checked);
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
                        if matches!(
                            verdict,
                            ArtifactVerdict::Agreed | ArtifactVerdict::AgreedUninterpretedCallee
                        ) && outcome.samples == 0
                        {
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

/// Require an exact one-to-one handoff from rustc's HIR plus generated-body
/// inventory to the producer registry. An unsupported body still has a `BodyRecord` carrying
/// explicit reasons; absence is never another spelling of "unsupported".
///
/// Both inputs are reduced to plain ids so this invariant is unit-testable
/// without a `TyCtxt`. The finalizer supplies `hir_body_owners` plus actual
/// synthetic coroutine definitions, separately from the independent census.
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
        "direct producer body inventory mismatch: expected {} unique HIR/generated body owner(s), recorded {} \
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
    // Trust (Step 2/3): body delegated to the tier-aware check, ALWAYS at the
    // pre-birth arm. The three existing run sites of this function are
    // zero-checks over inventories that must still be empty at their point in
    // the flow — obligation birth happens strictly AFTER run 3, so runs 1-3
    // keep their meaning verbatim at BOTH capability tiers (run 1's seam
    // oracle and run 3's "the clean-origin append introduced nothing"
    // inference hold unchanged). The recorded tier is applied by run 4 alone,
    // at the install site in `finalize_and_dump`. The pre-birth arm is pinned
    // byte-identical to this function's frozen body by
    // `structural_parity_arm_is_byte_identical_to_the_frozen_tripwire` in
    // `crate::direct_obligations`.
    crate::direct_obligations::inventory_errors_at_tier(
        module,
        crate::direct_obligations::DirectObligationTier::StructuralParityOnly,
    )
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
        refused_bodies: Vec::new(),
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

// ---------------------------------------------------------------------------
// Gap G2: PUBLISHING the assembled crate module.
//
// [`finalize_and_dump`] assembles ONE `trust_ir::Module` per crate, relinks the
// cross-producer call edges into it — and then DROPS it, having only rendered
// bytes to disk. Nothing in the process can ask for it. Meanwhile the codegen
// exit (`rustc_codegen_trust_cg::trust_ir_frontend`) forces the PER-BODY
// `trust_ir_of` query and lowers one function at a time, so the Rust->Clean
// call edge `link_clean_origin_edges` just re-pointed is dead weight at
// codegen, and `trust_cg_lower::adapter::translate_module` — the mature
// whole-module consumer, and a NON-optional dependency of this repo's
// `trust-cg-bridge` — has ZERO callers in this repo's own sources. Re-measured
// 2026-09-01, `grep -rn translate_module --include=*.rs` per tree:
// `crates/` 0, `compiler/` 0, `src/` 0, `tests/` 0, `library/` 0. The callers
// that exist are all inside PINNED SIBLING REPOS — `first-party/trust-cg`'s own
// crates, and `first-party/ty`'s `tla-trust-cg` JIT lane, which really does
// compile whole modules through it. So the consumer is mature and in use; what
// is missing is a producer that hands it a crate module.
//
// This block closes the PRODUCER half only: the module is interned into
// Session-scoped state, with a symbol -> `FuncId` map, so a consumer can take
// its inventory from it. The codegen-side routing is a separate change in a
// separate file.
//
// WHY SESSION STATE, and not a query or a return value:
//
//   * A QUERY would have to be declared in `compiler/rustc_middle`'s query
//     macro and provided from `rustc_mir_build` — two files outside this
//     change, and the artifact is not keyed on a `DefId` (it is one per crate,
//     produced by a seam that is not a query at all). `trust_ir_of`'s own
//     provider is the counter-example that proves the shape: it is per-body
//     because THIR is per-body.
//   * A RETURN VALUE dies at the caller. `trust_ir_crate_finalize` consumes
//     `FinalizeSummary` for diagnostics and drops it; publishing through it
//     would mean plumbing a `Module` through `rustc_interface` into codegen —
//     again, files outside this change.
//   * SESSION STATE is the shape this crate already uses three times over
//     (`CrateModuleRegistry`, `ArtifactPublicationState`,
//     `direct_obligations::DirectObligationRegistry`). The type is the key, so
//     no new crate edge and no new flag is needed; the storage lives on
//     `Session`, which outlives the `analysis` seam that finalizes and the
//     codegen seam that would consume — and, critically, does NOT outlive it,
//     so a driver that builds two Sessions in one process cannot leak one
//     crate's module into another's codegen.
//
// THE HARD CONSTRAINT, and how it is discharged:
//
// No Clean-origin function below tier `gate` may become reachable by codegen
// as a result of publication. TIER `gate` EXISTS AND IS REACHABLE —
// `clean_origin_join::CleanOriginTier::Gate`, minted after `recheck_kernel_tv`
// accepts a carrier-gated row, and pinned live by
// `tests/run-make/trust-ir-emit-clean-origin` for `cleanWsum` / `cleanSnd` /
// `cleanK32`. An earlier revision of this comment said it did not exist; that
// was a stale reading of an older `CleanOriginTier` doc and it is corrected
// here, because it is the stated reason for an affirmative on-wire claim.
//
// Until plan step 3.4 the constraint was discharged WITHOUT relying on the
// tier: `compute_codegen_license` leg 4 refused the whole module for ANY
// appended body-bearing function REGARDLESS OF ITS TIER — strictly STRICTER
// than design §9, which forbids consumption only BELOW `gate` — and the cost
// was every Rust body of a Clean-island crate.
//
// Since plan step 3.4 (owner rulings D36/D37) it is discharged PER FUNCTION,
// still without a reachability walker: an appended Clean-origin body is
// stamped `Gated { "clean-carrier-gate" }` only when its session-ledger entry
// (the gate's authenticated published token, bound to that exact Function)
// authenticates, and `Ungated` otherwise; the direct bodies keep their
// license either way. Below-`gate` rows are never licensed (the §9 rule), and
// a `gate` row's stamp is honored only by a consumer that re-checks its ledger
// entry (plan step 3.6, F1's `Compiler::compile` lane). Every consumer checks
// every body of the module it lowers: trust-cg's `enforce_module` refuses a
// reachable `Ungated` body, the crate-module lane removes every Clean body from
// its lowering context, and `module_to_lir` refuses every `Producer::Clean`
// body by name. On a tier-`gate` module the coverage disclosure's
// `"body_gate":"carrier-faithful"` and the v41 field now agree; THE FIELD IS
// NORMATIVE (§9's in-band refusal hook, what `trust_ir_build` and trust-cg
// read).
//
// The v41 format (developed as "v39") grew `Function.body_gate` +
// `validate_module_for_codegen` for exactly this. Measured 2026-09-01, neither
// was reachable here (pin `fecd740`; the batch then sat on the unmerged
// `v39-format-batch` branch, `64d8776`). It has since landed as trust-ir binary
// v41, but NO producer in this repo stamps `body_gate`, so the field still
// licenses nothing on its own. So the gate is built
// HERE, in the publication API, and it is DENY-BY-DEFAULT: the artifact does
// not hand out a bare `Module` that a consumer can enumerate, it hands out a
// separately-computed CODEGEN LICENSE that starts empty and is only ever
// widened by a positive record.
// ---------------------------------------------------------------------------

/// The assembled crate module, PUBLISHED for an in-process consumer (gap G2).
///
/// Holding this value is NOT a license to emit code for anything in it. The
/// module is the CONTEXT a whole-module consumer lowers against; the set of
/// functions it may emit code FOR is [`Self::codegen_inventory`], which is
/// computed separately, starts empty, and refuses the whole module rather than
/// license a subset it cannot prove closed.
pub struct PublishedCrateModule {
    crate_name: String,
    module: Module,
    /// Exact pass-1 local-definition identities, independent of display/link names.
    direct_definitions: crate::direct_definition_map::DirectDefinitionMap,
    symbols: BTreeMap<String, FuncId>,
    ambiguous_symbols: Vec<String>,
    /// Trust (WS5.2): `display_path` -> `FuncId`, ambiguity removed and reported, exactly like
    /// `symbols`. `Function.name` is the LINK-TIME SYMBOL now, so a consumer that knows a body by
    /// its def path (the F1 frontend's inventory projection) resolves it HERE and then CHECKS
    /// the row's name against the symbol it mangled — it never renames.
    display_paths: BTreeMap<String, FuncId>,
    ambiguous_display_paths: Vec<String>,
    codegen_licensed: Vec<FuncId>,
    codegen_license_refusal: Option<String>,
    /// In-process source data, not an inventory entry or an emission license.
    pending_rust_calls: Vec<crate::clean_origin_join::PendingRustCallSource>,
}

impl PublishedCrateModule {
    /// The direct body assigned to this local DefIndex in this Session.
    /// This association confers neither a codegen license nor a verdict.
    pub(crate) fn direct_function_for_definition(&self, def_index: u32) -> Option<FuncId> {
        self.direct_definitions.get(def_index)
    }

    /// Exact pass-1 source prefix length, independent of names and gate stamps.
    pub(crate) fn direct_source_count(&self) -> usize {
        self.direct_definitions.len()
    }

    /// The crate this module was assembled for.
    pub fn crate_name(&self) -> &str {
        &self.crate_name
    }

    /// The whole assembled module — including its Clean-origin definitions and
    /// the re-pointed cross-producer call edges. This is the LOWERING CONTEXT,
    /// not a work list: see [`Self::codegen_inventory`].
    pub fn module(&self) -> &Module {
        &self.module
    }

    /// Unlicensed deferred source context beside this exact immutable module.
    /// Its ids belong to `module()`, not a relocated codegen module. Source
    /// registry authentication, TV and actual Rust evidence remain owed.
    pub fn pending_rust_call_source(
        &self,
        def_index: u32,
    ) -> Option<&crate::clean_origin_join::PendingRustCallSource> {
        self.pending_rust_calls.iter().find(|row| row.def_index == def_index)
    }

    /// Resolve an intra-module callee by symbol.
    ///
    /// A name held by MORE THAN ONE function is absent from this map (it is in
    /// [`Self::ambiguous_symbols`] instead), so an ambiguous symbol resolves to
    /// `None` and the consumer must refuse. That is deliberately stricter than
    /// `trust_ir::Module::function_by_name`, which takes the FIRST match: the
    /// assembler's names are display identity only — resolution is by `FuncId`
    /// — and one crate can genuinely mint two functions with one name (a
    /// bodyless declaration beside a definition, or `clean_origin_join`'s
    /// general-lane rows, whose own refusal text says such a name "is resolved
    /// by no one").
    pub fn resolve_symbol(&self, symbol: &str) -> Option<FuncId> {
        self.symbols.get(symbol).copied()
    }

    /// The full symbol -> `FuncId` map, ambiguity already removed.
    pub fn symbols(&self) -> &BTreeMap<String, FuncId> {
        &self.symbols
    }

    /// Names held by more than one function, and therefore resolvable by no
    /// one. Sorted, deduped, and disclosed rather than silently first-wins.
    pub fn ambiguous_symbols(&self) -> &[String] {
        &self.ambiguous_symbols
    }

    /// Trust (WS5.2): the full `display_path` -> `FuncId` map, ambiguity already removed. A
    /// function with no `display_path` is absent. Display paths are NOT identity (trust-ir
    /// validates them for usability only); this map is a LOOKUP a consumer must follow with a
    /// symbol check, never a join key on its own.
    pub fn display_paths(&self) -> &BTreeMap<String, FuncId> {
        &self.display_paths
    }

    /// Trust (WS5.2): display paths held by more than one function (a macro-generated item
    /// family, a declaration beside a definition, a Clean row whose Lean name equals a Rust
    /// path), and therefore resolvable by no one. Sorted and deduped.
    pub fn ambiguous_display_paths(&self) -> &[String] {
        &self.ambiguous_display_paths
    }

    /// THE CODEGEN LICENSE: the functions of this module a consumer may emit
    /// code for, ascending: the direct-lane bodies. Possibly EMPTY (a refused
    /// license, or no spliceable body). Since plan step 3.4 a Clean-origin
    /// definition no longer empties it (leg 4 is per function, D37), and it
    /// never lists one: a `clean-carrier-gate` row is licensed only to a
    /// consumer that re-checks its session-ledger entry (plan step 3.6), never
    /// through this inventory.
    ///
    /// A consumer must take its work list from HERE and must never enumerate
    /// `module().functions` directly.
    pub fn codegen_inventory(&self) -> &[FuncId] {
        &self.codegen_licensed
    }

    /// Is this exact `FuncId` licensed for codegen? Deny-by-default.
    pub fn is_codegen_licensed(&self, id: FuncId) -> bool {
        self.codegen_licensed.binary_search(&id).is_ok()
    }

    /// Why the license was REFUSED, when it was. `None` means the license was
    /// granted — which is not the same as non-empty: a crate with no spliceable
    /// body has an empty license and no refusal.
    pub fn codegen_license_refusal(&self) -> Option<&str> {
        self.codegen_license_refusal.as_deref()
    }
}

/// Session-scoped storage for the published crate module (see the block comment
/// above for why this is Session state rather than a query).
///
/// `refusal` is not an afterthought: a consumer that asks and gets nothing must
/// learn WHY it got nothing, because "no module" and "a module the producer
/// refused to publish" demand the same fail-closed action but very different
/// bug reports.
#[derive(Default)]
struct PublishedCrateModuleState {
    published: Option<PublishedCrateModule>,
    refusal: Option<String>,
}

/// What a consumer is told when no finalization ever reached publication.
const NO_PUBLISHED_CRATE_MODULE: &str =
    "no crate module was published for this Session: `-Z trust-ir-lower` did not run, or crate \
     finalization refused before reaching publication";

/// The consumer entry point for the published crate module (gap G2).
///
/// `Err` carries the reason — never silence. The closure form is what the
/// Session state's mutex forces; the borrow does not escape it.
pub fn with_published_crate_module<R>(
    sess: &Session,
    f: impl FnOnce(Result<&PublishedCrateModule, &str>) -> R,
) -> R {
    sess.with_trust_compiler_state::<PublishedCrateModuleState, _>(|state| match &state.published {
        Some(published) => f(Ok(published)),
        None => f(Err(state.refusal.as_deref().unwrap_or(NO_PUBLISHED_CRATE_MODULE))),
    })
}

/// symbol -> `FuncId`, with every ambiguous name REMOVED and reported.
///
/// Returns `(map, ambiguous)`. A name that appears twice is deleted from the
/// map entirely — not left pointing at whichever function came first.
fn build_symbol_map(module: &Module) -> (BTreeMap<String, FuncId>, Vec<String>) {
    unique_function_index(module.functions.iter().map(|f| (f.name.as_str(), f.id)))
}

/// Trust (WS5.2): `display_path` -> `FuncId`, by the same ambiguity-removing rule as
/// [`build_symbol_map`]. Functions without a display path contribute nothing.
fn build_display_path_map(module: &Module) -> (BTreeMap<String, FuncId>, Vec<String>) {
    unique_function_index(
        module.functions.iter().filter_map(|f| f.display_path.as_deref().map(|path| (path, f.id))),
    )
}

/// The one "ambiguity resolves to no one" index both maps above share.
fn unique_function_index<'a>(
    rows: impl Iterator<Item = (&'a str, FuncId)>,
) -> (BTreeMap<String, FuncId>, Vec<String>) {
    use std::collections::btree_map::Entry;

    let mut index: BTreeMap<String, FuncId> = BTreeMap::new();
    let mut ambiguous: BTreeSet<String> = BTreeSet::new();
    for (key, id) in rows {
        match index.entry(key.to_string()) {
            Entry::Vacant(entry) => {
                entry.insert(id);
            }
            Entry::Occupied(_) => {
                ambiguous.insert(key.to_string());
            }
        }
    }
    for key in &ambiguous {
        index.remove(key);
    }
    (index, ambiguous.into_iter().collect())
}

/// THE CODEGEN LICENSE (gap G2's hard constraint), computed deny-by-default.
///
/// `Ok(ids)` licenses exactly `ids`; `Err(reason)` licenses NOTHING and says
/// why. There is no partial answer and no escape hatch.
///
/// # The rule
///
/// A function is licensed iff it is a DIRECT-lane spliced body — the class the
/// per-body `trust_ir_of` exit already lowers today, so licensing it in a
/// crate-module inventory exposes nothing that was not already exposed — AND
/// the module contains NO body-bearing function outside that class, Clean-origin
/// bodies excepted since plan step 3.4 (leg 4 below).
///
/// # Why the second clause was whole-module rather than per-function
/// (history; since plan step 3.4 it is per function for Clean-origin bodies)
///
/// The tempting rule is "license a direct body unless it can REACH an ungated
/// one". That rule is only as good as the walker that decides reachability, and
/// such a walker has to enumerate every `FuncId`-bearing construct in
/// `trust_ir::Inst` and `trust_ir::Constant` (`Call`, `CallIndirect`, `Invoke`,
/// `SeqMap { fwd }`, `Constant::FnDef`, `Constant::Closure { func }`, …). An
/// exhaustive `match` would catch a NEW VARIANT at compile time, but it cannot
/// catch a new `FuncId` FIELD added to an existing variant — and an
/// under-collecting walker OVER-licenses, silently, which is precisely the
/// failure this constraint exists to prevent.
///
/// Refusing the whole module when it holds any ungated body made the
/// reachability question VACUOUS instead of answering it with a walker whose
/// completeness nobody can check. It cost a real thing: a crate with a Clean
/// island got NO whole-module codegen license at all, EVEN AT TIER `gate`
/// (measured on the crate-module lane: a Rust-only body of such a crate was
/// `[crate-module-unavailable]`). Plan step 3.4 (owner ruling D37, OD-2 part 2)
/// removes that cost WITHOUT a walker: the license stays a positive record of
/// the direct set, an appended Clean-origin body is stamped per function
/// (`clean-carrier-gate` beside an authenticated ledger entry, `Ungated`
/// otherwise), and reachability is never decided here — every consumer checks
/// every body of the module it lowers (leg 4 below). The walker argument above
/// still holds, and is why no walker was introduced.
///
/// # The legs, each fail-closed
///
/// 1. `module.functions[i].id == i` — the dense-id invariant the assembler
///    maintains end to end. The license is computed POSITIONALLY, so a
///    renumbered module must license nothing rather than license by index.
/// 2. `assigned[i].1 == FuncId(i)` — pass 1's own dense assignment. If the
///    direct set cannot be identified positionally, nothing is licensed.
/// 3. Every member of the direct set is body-bearing AND carries
///    `Producer::TRust`. This is the INDEPENDENT second signal: position says
///    "pass 1 put it here", provenance says "the direct lane made it", and a
///    disagreement between two independent signals is a refusal, never a
///    tie-break.
/// 4. Every function at or above `assigned.len()` is a bodyless declaration
///    or a `Producer::Clean` body. A declaration is an opaque external symbol
///    — nothing to emit, and a call to one is not a leak — so declarations are
///    unlicensed without being disqualifying. A body of ANY OTHER producer
///    there (anything this producer learns to append later) still disqualifies
///    the whole module.
///
/// # Leg 4 is per function for Clean-origin bodies (plan step 3.4, owner ruling D37)
///
/// Until plan step 3.4 any appended body withdrew the license of every body,
/// the direct ones included, because "an under-collecting walker OVER-licenses"
/// (above). D37 (OD-2 part 2) replaced that for Clean-origin bodies: an
/// appended `Producer::Clean` body never withdraws the direct license. It is
/// licensed itself only when [`clean_carrier_licensed`] says so (an
/// authenticated session-ledger entry, stamped `clean-carrier-gate`), and is
/// otherwise stamped `Ungated` by [`stamp_codegen_license`]. NO WALKER DECIDES
/// ANYTHING: this function still answers only for the direct set, and every
/// consumer checks every body of the module it lowers — trust-cg's
/// `CodegenLicensePolicy::enforce_module` refuses a reachable `Ungated` body on
/// the `Compiler::compile` lane, the crate-module lane removes every Clean body
/// from its lowering context, and `module_to_lir` refuses every
/// `Producer::Clean` body by name, lowered or inlined
/// (docs/design/2026-10-02-step3-lean-through-trust-ir.md §5.2). Appended bodies
/// of any other producer keep the whole-module refusal: no consumer argument
/// has been made for them (docs/DECISION_QUEUE.md, STEP3.4-LEG4-SCOPE).
fn compute_codegen_license(
    module: &Module,
    assigned: &[(u32, FuncId)],
) -> Result<Vec<FuncId>, String> {
    // Leg 1.
    for (i, f) in module.functions.iter().enumerate() {
        if f.id.as_usize() != i {
            return Err(format!(
                "dense-FuncId invariant broken: functions[{i}] carries id {}. The codegen \
                 license is computed positionally, so a renumbered module licenses nothing.",
                f.id.index()
            ));
        }
    }
    // Leg 2.
    for (i, (def_index, id)) in assigned.iter().enumerate() {
        if id.as_usize() != i {
            return Err(format!(
                "pass-1 direct assignment is not dense: assigned[{i}] is (def_index {def_index}, \
                 FuncId {}). The direct set cannot be identified positionally, so nothing is \
                 licensed.",
                id.index()
            ));
        }
    }
    if assigned.len() > module.functions.len() {
        return Err(format!(
            "pass-1 assigned {} direct bodies but the module holds only {} functions; the \
             direct set is not a prefix of the module, so nothing is licensed.",
            assigned.len(),
            module.functions.len()
        ));
    }
    // Leg 3.
    for (i, f) in module.functions.iter().take(assigned.len()).enumerate() {
        if f.is_declaration() {
            return Err(format!(
                "FuncId {i} (`{}`) is in the pass-1 direct set but is BODYLESS; position and \
                 body disagree, so nothing is licensed.",
                f.name
            ));
        }
        if f.producer != Some(trust_ir::Producer::TRust) {
            return Err(format!(
                "FuncId {i} (`{}`) is in the pass-1 direct set but carries producer {:?}, not \
                 Some(TRust); position and provenance disagree, so nothing is licensed.",
                f.name, f.producer
            ));
        }
    }
    // Canonical adapters have a positive source-owner and real-body witness;
    // arbitrary auxiliary functions still withdraw the whole license.
    let adapters = crate::closure_adapter::licensed_adapters(module, assigned.len())
        .ok_or_else(|| "unowned or noncanonical closure adapter".to_owned())?;
    // Leg 4 — THE GATE, per function for Clean-origin bodies (plan step 3.4, D37).
    let foreign: Vec<&Function> = module
        .functions
        .iter()
        .skip(assigned.len())
        .filter(|f| !f.is_declaration() && f.producer != Some(trust_ir::Producer::Clean) && !adapters.contains(&f.id))
        .collect();
    if !foreign.is_empty() {
        let sample = foreign
            .iter()
            .take(3)
            .map(|f| format!("FuncId {} `{}` ({:?})", f.id.index(), f.name, f.producer))
            .collect::<Vec<_>>()
            .join(", ");
        return Err(format!(
            "{} body-bearing function(s) outside the direct-lane set from a producer other than \
             Clean — only an appended Clean-origin body is licensed per function (plan step \
             3.4, D37); any other appended body still withdraws the whole module, so NOTHING in \
             this module is licensed for codegen: {sample}{}",
            foreign.len(),
            if foreign.len() > 3 { ", …" } else { "" }
        ));
    }
    let mut licensed: Vec<_> = (0..assigned.len()).map(|i| FuncId::new(i as u32)).collect();
    licensed.extend(adapters);
    Ok(licensed)
}

/// THE CLEAN CARRIER HALF OF LEG 4 (plan step 3.4, design §5.2): the appended
/// `Producer::Clean` bodies licensed `clean-carrier-gate` — exactly the members
/// of `authenticated` (the session-ledger entries whose token authenticated
/// the Function at that `FuncId`, `AuthenticatedCleanRow::authenticate_in`)
/// that sit outside the direct prefix, are body-bearing and are
/// `Producer::Clean`. Every other appended body is stamped `Ungated`. It
/// licenses nothing on its own: a consumer honors the stamp only beside the
/// ledger entry (plan step 3.6), and the direct license never depends on it.
fn clean_carrier_licensed(
    module: &Module,
    assigned: &[(u32, FuncId)],
    authenticated: &BTreeSet<FuncId>,
) -> BTreeSet<FuncId> {
    authenticated
        .iter()
        .copied()
        .filter(|id| id.as_usize() >= assigned.len())
        .filter(|id| {
            module.function_by_id(*id).is_some_and(|f| {
                f.id == *id && !f.is_declaration() && f.producer == Some(trust_ir::Producer::Clean)
            })
        })
        .collect()
}

/// The functions stamped `clean-carrier-gate`, read back off the module.
fn clean_carrier_stamps(module: &Module) -> BTreeSet<FuncId> {
    let stamp = trust_clean_ir_gate::clean_carrier_gate_stamp();
    module.functions.iter().filter(|f| f.body_gate.as_ref() == Some(&stamp)).map(|f| f.id).collect()
}

/// THE RUST PRODUCER'S GATE AUTHORITY — the name this producer stamps into
/// `trust_ir::BodyGate::Gated { authority }` for a body it licensed (trust-ir
/// binary v41).
///
/// # What passing this gate ASSERTS
///
/// Exactly [`compute_codegen_license`]'s four legs, and nothing else:
///
/// 1. the function sits at its own dense `FuncId` in the assembled module;
/// 2. it is a member of pass 1's DIRECT set — the class the per-body
///    `trust_ir_of` codegen exit already selects and emits today, so a license
///    here exposes nothing that was not already exposed;
/// 3. it is body-bearing AND carries `Producer::TRust` — two independent
///    signals that the direct lane made it, whose disagreement is a refusal;
/// 4. the module it lives in holds NO body-bearing function outside that set
///    other than appended Clean-origin bodies (plan step 3.4, D37), each of
///    which is stamped per function (`clean-carrier-gate` or `Ungated`) and
///    which every consumer removes from, or refuses in, the lowering context
///    it emits from — so no appended below-tier definition is reached by
///    inlining without a consumer refusing it.
///
/// Plus the two preconditions [`decide_publication`] re-checks on the same
/// module: crate finalization recorded no error, and no pending-const sentinel
/// survived.
///
/// # What it does NOT assert — read this before recognizing it
///
/// It is a STRUCTURAL PROVENANCE gate, not a verification of the body. It
/// states nothing about the body's semantics: no proof was checked, no
/// translation validation ran, no kernel re-checked a lowering equation, and no
/// borrow, ownership or panic-freedom claim was discharged. The name carries
/// the word `structural` so that it cannot be read as a verification claim by
/// anyone who reads only the authority string. It is deliberately NOT
/// comparable to Clean's `clean-kernel-tv`, whose authority is an in-process
/// CleanCic kernel RE-CHECK of the lowering equation, attached in the same step
/// as a `Certified` `TranslationValidation` obligation.
///
/// `trust_ir::BodyGate`'s contract puts recognition in the CONSUMER's hands and
/// makes an unrecognized authority a REFUSAL, never a pass. A consumer that
/// needs a semantic gate therefore refuses this one by simply not listing it —
/// which is why `trust_cg_lower::CodegenLicensePolicy::default()`'s recognized
/// set stays `{"clean-kernel-tv"}` and compiling this producer's artifacts
/// there is an explicit, opt-in
/// `--recognize-authority trust-direct-lane-structural`.
pub const TRUST_DIRECT_LANE_AUTHORITY: &str = "trust-direct-lane-structural";

/// THE CODEGEN INVENTORY, read off the v41 stamps [`stamp_codegen_license`]
/// wrote — never computed a second time.
///
/// Deny-by-default in the strongest form available: a module nobody stamped
/// carries no `Gated` function at all, so its inventory is EMPTY. An edit that
/// drops the stamp therefore licenses NOTHING, instead of licensing whatever a
/// second, still-running computation happens to say.
///
/// Only this producer's own authority counts. A `Gated` body naming some other
/// authority is not in the inventory, so possession of a foreign license never
/// becomes permission here.
///
/// Ascending and deduplicated: `PublishedCrateModule::is_codegen_licensed`
/// binary-searches it.
fn inventory_from_stamps(module: &Module) -> Vec<FuncId> {
    let mut ids: Vec<FuncId> = module
        .functions
        .iter()
        .filter(|f| !f.is_declaration())
        .filter(|f| {
            matches!(
                f.body_gate.as_ref(),
                Some(BodyGate::Gated { authority, .. }) if authority == TRUST_DIRECT_LANE_AUTHORITY
            )
        })
        .map(|f| f.id)
        .collect();
    ids.sort_unstable();
    ids.dedup();
    ids
}

/// `(gated, ungated, no-claim)` over the assembled module: bodies carrying this
/// producer's positive license, bodies affirmatively ungated, and functions
/// making no claim. Logged at the stamp site so ONE compile reports the shape
/// of its own license rather than needing the artifact re-read.
fn license_stamp_census(module: &Module) -> (usize, usize, usize) {
    let mut gated = 0;
    let mut ungated = 0;
    let mut no_claim = 0;
    for function in &module.functions {
        match function.body_gate.as_ref() {
            Some(BodyGate::Gated { .. }) => gated += 1,
            Some(BodyGate::Ungated) => ungated += 1,
            None => no_claim += 1,
        }
    }
    (gated, ungated, no_claim)
}

/// STAMP the v41 codegen license into the assembled module — the producer's
/// in-band claim, and from here on the ONLY representation of the license.
///
/// Returns the license REFUSAL, or `None` when the license was granted. The
/// licensed SET is deliberately NOT returned: a consumer's inventory is read
/// back off these stamps by [`inventory_from_stamps`], so the wire claim and
/// the inventory are ONE fact with ONE writer and cannot disagree. That is
/// stronger than testing two computations for agreement, which is why the
/// agreement is not tested — it is unspellable.
///
/// Every function receives a claim, and each of v41's three states is used for
/// exactly what the format says it means:
///
/// * `Gated { authority }` — a LICENSED direct-lane body, under
///   [`TRUST_DIRECT_LANE_AUTHORITY`], which names a structural gate.
/// * `Gated { "clean-carrier-gate" }` — plan step 3.4 (D36/D37): an appended
///   Clean-origin body [`clean_carrier_licensed`] licensed, i.e. one whose
///   session-ledger entry authenticated the exact Function. The join wrote the
///   stamp before its final authentication; this stamp KEEPS it for exactly
///   that set and nothing else. It is a codegen license, never a proof grade,
///   and it is honored only beside the ledger entry (plan step 3.6).
/// * `Ungated` — a body-bearing function the gate did not license. A REFUSED
///   license licenses NOTHING, so when legs 1-4 refuse, every body in the
///   module — the direct ones included — is stamped `Ungated`. Since plan
///   step 3.4 an appended Clean-origin body does NOT refuse the license: one
///   without an authenticated ledger entry (below tier `gate`, or a token that
///   no longer authenticates) is stamped `Ungated` by itself and the direct
///   bodies keep their license (owner ruling D37). On a below-`gate` row the
///   coverage disclosure's tier and this field agree that it is not
///   licensed; on a `gate` row both say so too (`carrier-faithful` in the
///   disclosure, the `clean-carrier-gate` stamp here). This field is the
///   normative codegen license. The census logged at the stamp site reports
///   this field's answer, not the disclosure's.
/// * `None` — a bodyless declaration. An opaque external symbol produces no
///   code, so it needs no license and makes no claim. v41's producer
///   conformance rule asks for an affirmative claim per BODY; a declaration is
///   not one, and `trust_ir_build`'s own codegen-license validator skips
///   declarations for the same reason.
///
/// # This REFUSES MORE and ADMITS NOTHING NEW
///
/// Before this, every function this producer emitted went out with
/// `body_gate: None` — the pre-v41 grandfather state that
/// `trust_cg_lower::CodegenLicensePolicy::default()` PERMITS. After it:
///
/// * an unlicensed body is `Ungated`, which NO policy may permit (trust-cg
///   refuses it unconditionally; `trust_ir_build::validate_module_for_codegen`
///   reports it as its own error), so a below-`gate` Clean-origin body is
///   refused wherever it is reached instead of silently compiled (before plan
///   step 3.4 the whole Clean-island crate was);
/// * a licensed body is `Gated` under an authority no consumer recognizes by
///   default, so it too is refused until a consumer opts in by name.
///
/// The stamp cannot license a body the inventory does not already license,
/// because the inventory IS the stamp and both come from the single
/// [`compute_codegen_license`] call below. What it adds is a claim a consumer
/// may refuse — not permission. The `clean-carrier-gate` stamp is the one the
/// join wrote and its ledger entry authenticated, kept or removed here; it is
/// NOT in [`inventory_from_stamps`] (a consumer of this producer's inventory
/// never emits a Clean-origin body) and it is admitted, ADMITTING MORE BY
/// RULING (D36), only by F1's Clean admission against the ledger (step 3.6).
///
/// Plan step 3.4: `clean_carrier` is the set of appended Clean-origin bodies
/// whose session-ledger entry authenticated (computed by the finalize from the
/// join's handed-over tokens). Only [`clean_carrier_licensed`]'s subset of it is
/// stamped `clean-carrier-gate`, and only when legs 1-4 grant the license;
/// the read-back below covers both authorities.
fn stamp_codegen_license(
    module: &mut Module,
    assigned: &[(u32, FuncId)],
    clean_carrier: &BTreeSet<FuncId>,
) -> Option<String> {
    let decision = compute_codegen_license(module, assigned);
    let licensed: BTreeSet<FuncId> = match &decision {
        Ok(ids) => ids.iter().copied().collect(),
        Err(_) => BTreeSet::new(),
    };
    let clean_licensed: BTreeSet<FuncId> = match &decision {
        Ok(_) => clean_carrier_licensed(module, assigned, clean_carrier),
        Err(_) => BTreeSet::new(),
    };
    for function in &mut module.functions {
        function.body_gate = if function.is_declaration() {
            None
        } else if licensed.contains(&function.id) {
            Some(BodyGate::Gated { authority: TRUST_DIRECT_LANE_AUTHORITY.to_string(), evidence: None })
        } else if clean_licensed.contains(&function.id) {
            Some(trust_clean_ir_gate::clean_carrier_gate_stamp())
        } else {
            Some(BodyGate::Ungated)
        };
    }
    // Read the stamps back through the WALK A CONSUMER USES, not through a
    // second copy of the loop above: a licensed id that is absent from the
    // module, or one that is a declaration, would otherwise be silently
    // dropped from the inventory. Leg 2 and leg 3 already refuse both shapes,
    // so this is unreachable — and an unreachable inconsistency that still
    // withdraws the whole license is the only kind worth leaving in.
    let stamped: BTreeSet<FuncId> = inventory_from_stamps(module).into_iter().collect();
    let clean_stamped = clean_carrier_stamps(module);
    if stamped != licensed || clean_stamped != clean_licensed {
        for function in &mut module.functions {
            if !function.is_declaration() {
                function.body_gate = Some(BodyGate::Ungated);
            }
        }
        return Some(format!(
            "codegen-license STAMP DISAGREEMENT: `compute_codegen_license` licensed {} \
             function(s) and {} clean-carrier-gate row(s) but the stamps read back {} and {}. \
             Two readings of one license disagree, so every body is re-stamped `ungated` and \
             NOTHING is licensed.",
            licensed.len(),
            clean_licensed.len(),
            stamped.len(),
            clean_stamped.len()
        ));
    }
    decision.err()
}

/// Decide what publication should do with the assembled module: hand back the
/// [`PublishedCrateModule`] to intern, or the reason it must not be interned.
///
/// PURE — no `Session`, no `TyCtxt` — so every decision this makes is testable
/// from `trust_ir` alone. `trust-thir-lower` needs `rustc_private` and cannot
/// be built from the plain `crates/` workspace, so the amount of this change
/// that can be covered by a test at all is exactly the amount that stays out of
/// the compiler's types.
///
/// The two preconditions live HERE rather than at the call site, so they are
/// properties of publication itself and not of wherever it is called from:
///
/// * `errors` is empty at the one call site by construction (every
///   `errors.extend` in [`finalize_and_dump`] is followed by an `is_empty` early
///   return), and it is re-checked anyway. A module the finalizer was in the
///   middle of REJECTING must never become a consumer's input, and that must not
///   depend on every future early return staying where it is.
/// * The pending-const sentinel tripwire is the artifact writer's, re-run
///   UNCONDITIONALLY. The writer only runs it when a dump or `--emit` was
///   requested; publication happens on every `-Z trust-ir-lower` compile, so its
///   precondition has to too. A leftover sentinel is a `Constant::PhantomData`
///   standing in for a value the finalizer failed to evaluate — a consumer that
///   emitted code for it would emit the WRONG VALUE, silently, which is strictly
///   worse than emitting nothing.
///
/// A REFUSED CODEGEN LICENSE IS NOT A REFUSED PUBLICATION. A module holding a
/// Clean-origin definition is still published — a consumer needs it as lowering
/// context and for disclosure — with an EMPTY inventory. Possession is not a
/// license; that separation is the whole shape of the gate.
///
/// `codegen_license_refusal` is [`stamp_codegen_license`]'s verdict, carried
/// rather than recomputed; the licensed SET is read back off the module's own
/// v41 stamps, so the inventory a consumer receives and the claim on the wire
/// are one fact.
///
/// Two structural re-checks are made on that fact, one per DIRECTION of the
/// verdict, because each direction has its own way of being internally
/// inconsistent and neither implies the other:
///
/// * license GRANTED — the licensed set must be exactly pass 1's direct
///   prefix. Stamps that do not match that arity mean some pass wrote a claim
///   the license did not authorize.
/// * license REFUSED — the inventory must be EMPTY. "A refused license
///   licenses nothing" is the load-bearing sentence of this whole gate, and
///   until now it was the ONE direction with no structural re-check: the arity
///   check sat inside `if codegen_license_refusal.is_none()`, so a pass that
///   mutated `body_gate` AFTER the stamp could hand out a non-empty
///   `codegen_inventory()` alongside a refusal. Nothing in the tree does that
///   today (the stamp is pinned as the last mutation by
///   `crate_module_publication_order_tests`, and `prepare_crate_module` refuses
///   on the refusal string before reading the inventory), which is exactly why
///   the missing leg was invisible. It is checked here so that the sentence is
///   true of the STRUCTURE and not only of the current call order.
fn decide_publication(
    crate_name: &str,
    module: Module,
    assigned: &[(u32, FuncId)],
    errors: &[String],
    codegen_license_refusal: Option<String>,
) -> Result<PublishedCrateModule, String> {
    if !errors.is_empty() {
        return Err(format!(
            "refused to publish `{crate_name}`: crate finalization recorded {} error(s)",
            errors.len()
        ));
    }
    let sentinels = count_const_sentinels(&module);
    if sentinels > 0 {
        return Err(format!(
            "refused to publish `{crate_name}`: {sentinels} unpatched pending-const sentinel(s) \
             in the assembled module"
        ));
    }
    let (symbols, ambiguous_symbols) = build_symbol_map(&module);
    let (display_paths, ambiguous_display_paths) = build_display_path_map(&module);
    let codegen_licensed = inventory_from_stamps(&module);
    match &codegen_license_refusal {
        None => {
            let expected = compute_codegen_license(&module, assigned)?;
            if codegen_licensed != expected {
                return Err(format!(
                    "refused to publish `{crate_name}`: the codegen license was GRANTED for the \
                     {} direct-lane body/bodies pass 1 assigned, but the module's v41 stamps \
                     license {} function(s). The stamp IS the inventory, so a module whose \
                     stamps do not match the direct set is not publishable.",
                    assigned.len(),
                    codegen_licensed.len()
                ));
            }
        }
        Some(refusal) => {
            if !codegen_licensed.is_empty() {
                return Err(format!(
                    "refused to publish `{crate_name}`: the codegen license was REFUSED, but \
                     the module's v41 stamps license {} function(s) ({}). A refused license \
                     licenses NOTHING, so a non-empty inventory here means a pass wrote a \
                     `body_gate` claim after the stamp; the module is not publishable. The \
                     refusal was: {refusal}",
                    codegen_licensed.len(),
                    codegen_licensed
                        .iter()
                        .map(|id| format!("FuncId {}", id.index()))
                        .collect::<Vec<_>>()
                        .join(", ")
                ));
            }
        }
    }
    let direct_definitions =
        crate::direct_definition_map::DirectDefinitionMap::from_assembly(&module, assigned);
    Ok(PublishedCrateModule {
        crate_name: crate_name.to_string(),
        module,
        direct_definitions,
        symbols,
        ambiguous_symbols,
        display_paths,
        ambiguous_display_paths,
        codegen_licensed,
        codegen_license_refusal,
        pending_rust_calls: Vec::new(),
    })
}

/// Attach data only after publication's existing semantic decision succeeds.
/// Returning an error drops both the candidate and all retained contexts.
fn retain_pending_rust_call_sources(
    decision: Result<PublishedCrateModule, String>,
    pending: Vec<crate::clean_origin_join::PendingRustCallSource>,
) -> Result<PublishedCrateModule, String> {
    let mut published = decision?;
    let mut definitions = BTreeSet::new();
    let mut functions = BTreeSet::new();
    for row in &pending {
        let valid = published.module.function_by_id(row.func_id).is_some_and(|function| {
            !function.is_declaration()
                && function.producer == Some(trust_ir::Producer::Clean)
                && function.name == row.link_symbol
        });
        if !valid || !definitions.insert(row.def_index) || !functions.insert(row.func_id) {
            return Err("retained Rust-call source disagrees with its unique published Clean body".into());
        }
    }
    published.pending_rust_calls = pending;
    Ok(published)
}

/// Install one publication decision into the Session slot.
///
/// PURE in the slot — the `Session` stays in [`publish_crate_module`], which is
/// then a five-line adapter — so the double-publication rule below is testable.
///
/// [`finalize_and_dump`] runs once per Session. A SECOND publication is an
/// invariant violation, and it makes BOTH candidates suspect: the first is
/// WITHDRAWN rather than kept (stale, and silently the wrong crate) or replaced
/// (silently the wrong crate the other way round).
fn install_published_crate_module(
    state: &mut PublishedCrateModuleState,
    crate_name: &str,
    decision: Result<PublishedCrateModule, String>,
) {
    if state.published.is_some() || state.refusal.is_some() {
        state.published = None;
        state.refusal = Some(format!(
            "refused: a crate module was already published for this Session, so a second \
             finalization tried to publish `{crate_name}` over it. Both are withdrawn."
        ));
        return;
    }
    match decision {
        Ok(published) => state.published = Some(published),
        Err(refusal) => state.refusal = Some(refusal),
    }
}

/// Publish the assembled module into Session state, or record WHY it was not
/// published. Called once per crate finalization.
///
/// A refusal is always recorded. A consumer that asks and gets nothing must
/// learn which nothing it got: "finalization never reached publication" and
/// "the producer refused to publish what it assembled" demand the same
/// fail-closed action but very different bug reports.
fn publish_crate_module(
    sess: &Session,
    crate_name: &str,
    module: Module,
    assigned: &[(u32, FuncId)],
    errors: &[String],
    codegen_license_refusal: Option<String>,
    pending_rust_calls: Vec<crate::clean_origin_join::PendingRustCallSource>,
) {
    let decision = retain_pending_rust_call_sources(
        decide_publication(crate_name, module, assigned, errors, codegen_license_refusal),
        pending_rust_calls,
    );
    match &decision {
        Ok(published) => {
            tracing::debug!(
                crate_name = %published.crate_name,
                functions = published.module.functions.len(),
                direct = assigned.len(),
                symbols = published.symbols.len(),
                ambiguous_symbols = published.ambiguous_symbols.len(),
                licensed = published.codegen_licensed.len(),
                license_refused = published.codegen_license_refusal.is_some(),
                "trust-ir-lower: crate module publication"
            );
            if let Some(reason) = published.codegen_license_refusal.as_deref() {
                tracing::debug!(reason = %reason, "trust-ir-lower: codegen license refused");
            }
        }
        Err(reason) => {
            tracing::debug!(
                reason = %reason,
                "trust-ir-lower: crate module publication refused"
            );
        }
    }
    sess.with_trust_compiler_state::<PublishedCrateModuleState, _>(move |state| {
        install_published_crate_module(state, crate_name, decision)
    });
}

fn clean_origin_thir_overlap_errors(
    assigned: &[(u32, FuncId)],
    emitted: &[crate::clean_origin_join::EmittedRow],
) -> Vec<String> {
    emitted
        .iter()
        .filter(|row| assigned.binary_search_by_key(&row.def_index, |(index, _)| *index).is_ok())
        .map(|row| {
            format!(
                "fatal Clean/THIR source-identity overlap for def index {} path {:?}: both \
                 producers emitted a defined function; operational name disambiguation is not \
                 authority to duplicate one source definition",
                row.def_index, row.def_path,
            )
        })
        .collect()
}

/// Trust: the crate-level finalizer. Called (via `rustc_mir_build::trust_ir_crate_finalize`) from
/// the `rustc_interface` `analysis` seam after the crate has been confirmed error-free. It forces
/// `mir_built` for every body owner after taking the interface-prepared, already-invalidated
/// artifact transaction, then drains the resulting direct-THIR registry. The seam differential is inert
/// when the crate has no HIR body owners; an explicitly requested genuinely empty dump still
/// publishes a deterministic empty module and coverage sidecar. A partial/missing registry is a
/// semantic finalization error, never an empty success.
// Trust (IR-1, docs/design/2026-08-27-two-language-direct-to-trust-ir.md §3):
// `clean_origin` is the finalize-seam collection of Clean-origin trust-ir
// spellings (re-earned kernel verdict per def, `rustc_mir_transform::
// clean_origin_ir`). `None` = verification off, the collection deliberately
// did not run — recorded as a disclosed absence in coverage, never silently.
// All substantive append/disclosure logic lives in `clean_origin_join` /
// `contract_disclosure`; this frozen file only plumbs.
pub fn finalize_and_dump(
    tcx: TyCtxt<'_>,
    clean_origin: Option<Vec<crate::clean_origin_join::CleanOriginIrOutcome>>,
) -> FinalizeSummary {
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
    let mut expected_body_indices =
        tcx.hir_body_owners().map(|def| def.to_def_id().index.as_u32()).collect::<Vec<_>>();
    tcx.par_hir_body_owners(|def| tcx.ensure_done().mir_built(def));
    // These real generated definitions have MIR but no HIR body. Their fed
    // mir_built cannot rerun a producer callback, so absence/duplication of the
    // dedicated creation-time handoff is an inventory error, not an exclusion.
    expected_body_indices.extend(tcx.mir_keys(()).iter().filter_map(|def| {
        (tcx.def_kind(*def) == DefKind::SyntheticCoroutineBody)
            .then_some(def.to_def_id().index.as_u32())
    }));
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
        // producer inventory. `std::mem::take` above reset CrateModuleRegistry.
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
    // Trust: zero-authority cold-static storage capture, after the complete
    // analysis inventory and outside mir_built's CTFE freeze. Existing direct
    // refusal/grade/initialization semantics are unchanged.
    let source_static_readback = crate::source_static_readback::finalize(tcx);
    resolve_pending_consts(tcx, &mut records);

    // Trust (WS5.2): `Function.name` IS the link-time symbol. Stamp every spliceable body's
    // symbol and every ledgered callee's link facts HERE, once, past every `mir_built` — and
    // refuse, by name, each body for which no symbol exists, BEFORE assembly, so the refusal is
    // an ordinary unsplice (its callers see a `local-unlowered` edge) and never a guessed name.
    let link_symbol_refusals = stamp_link_symbols(tcx, &mut records);

    // Trust (owner call 2026-09-17(b), `reports/2026-09-14-rust-abi-vararg-producer-half.md`):
    // the declarations `link_clean_origin_edges` may still SIGN. A row whose `local_def_index`
    // names one of these is exempt from per-body refusal — see `unsignable_minting_bodies` for
    // why the exemption is a superset and therefore cannot admit anything.
    let clean_origin_local_defs: std::collections::BTreeSet<u32> = clean_origin
        .iter()
        .flatten()
        .filter_map(|outcome| match outcome {
            crate::clean_origin_join::CleanOriginIrOutcome::Emitted(record) => {
                Some(record.def_index)
            }
            // Trust: pending Rust-call plans can sign this exact Clean declaration
            // after their Rust body identities are bound in the owning module.
            // The transaction still refuses unresolved or invalid call plans.
            crate::clean_origin_join::CleanOriginIrOutcome::RustCalls(record) => {
                Some(record.def_index)
            }
            crate::clean_origin_join::CleanOriginIrOutcome::Skipped(_)
            | crate::clean_origin_join::CleanOriginIrOutcome::General(_) => None,
        })
        .collect();

    let mut spliced_veto: std::collections::BTreeSet<u32> = std::collections::BTreeSet::new();
    let mut assembled = assemble(&crate_name, &records, &spliced_veto);
    // Trust (2026-09-27): the FIRST typed refusal each body met across the re-assembly rounds.
    // A later round holds a vetoed body out as `SpliceRefusal::Vetoed`; the row it publishes
    // names the refusal that first kept it out instead (see `restore_vetoed_refusals`).
    let mut first_refusals: BTreeMap<u32, SpliceRefusal> = BTreeMap::new();
    record_first_refusals(&assembled.coverage_rows, &mut first_refusals);
    // Trust (owner call 2026-09-17(b)): REFUSE THE BODY, NOT THE CRATE. Every body that mints a
    // call edge to a Rust-ABI declaration this producer cannot sign is marked unsupported —
    // `splice_ok` then refuses it and `coverage.json` reports the reason with its v7/D3 options —
    // and the crate is assembled again without it. What used to happen instead was that ONE such
    // edge anywhere failed the whole module at finalization, so the crate produced nothing.
    //
    // A FIXPOINT, because refusal is contagious in exactly the way pass 1's own loop documents:
    // dropping body B turns every `Local(B)` edge into a `local-unlowered:` declaration, which
    // may itself be unsignable, which refuses B's callers. Each round refuses at least one body
    // that WAS spliced in the round before, so the spliced set strictly shrinks and the bound
    // below cannot be reached without a defect; reaching it is an error, never a silent stop.
    //
    // The declaration row itself needs no separate disposal: pass 2 mints a declaration only
    // from a spliced body's edge, so once every minting body is refused the row is never minted,
    // the dense `FuncId` space is recomputed from scratch, and nothing dangles. That is why this
    // is a re-assembly and not a post-hoc removal from an assembled module.
    let refusal_round_bound = records.len() + 1;
    let mut refusal_rounds = 0usize;
    let mut refused_bodies: Vec<RefusedBody> = link_symbol_refusals;
    while assembled.errors.is_empty() {
        // Trust (WS5.2): the same body-not-crate refusal for a call edge whose declaration would
        // share its link-time symbol with another row (`symbol_collision_minting_bodies`).
        let mut refused = unsignable_minting_bodies(&assembled, &clean_origin_local_defs);
        refused.extend(symbol_collision_minting_bodies(&assembled));
        refused.sort();
        refused.dedup();
        if refused.is_empty() {
            break;
        }
        if refusal_rounds >= refusal_round_bound {
            errors.push(format!(
                "trust-ir producer defect [unsignable-rust-abi-declaration]: the per-body \
                 refusal of unsignable Rust-ABI call edges did not converge in \
                 {refusal_round_bound} round(s) over {} recorded bodies. Each round must refuse \
                 at least one previously-spliced body, so this is a producer defect — report it.",
                records.len(),
            ));
            break;
        }
        let mut applied = 0usize;
        for (def_index, reason) in refused {
            // Carried out to the compiler BEFORE the `records` lookup, and kept even when
            // that lookup misses: strict must report a body this fixpoint refused whether
            // or not the record is still addressable here. See `RefusedBody`.
            //
            // ONE ROW PER BODY, not per refused EDGE. `unsignable_minting_bodies` yields a
            // `(def_index, reason)` pair per unsignable CALLEE, so a body minting two of
            // them yields two pairs — and emitting both gave the same body two identical
            // diagnostics at the same span (measured: `36:10 36:10` on
            // `trust_ir_lower_tuple_match_deref_variant.rs`). The strict diagnostic is a
            // statement about the BODY ("the producer did not fully lower it"), which is
            // true once; the per-callee detail is already aggregated on the coverage row by
            // `bump_unsupported` below, which is where a reader goes for the full list.
            if !refused_bodies.iter().any(|r| r.def_index == def_index) {
                refused_bodies.push(RefusedBody { def_index, reason: reason.clone() });
            }
            let Ok(index) = records.binary_search_by_key(&def_index, |r| r.def_index) else {
                continue;
            };
            // A refused body was spliced in THIS assembly, so `splice_ok` held and its
            // `unsupported` rows were empty. The count is progress, not aggregation.
            if records[index].unsupported.is_empty() {
                applied += 1;
            }
            bump_unsupported(&mut records[index].unsupported, &reason);
        }
        if applied == 0 {
            // No previously-clean body was marked, so a re-assembly would reproduce this one.
            // Stop and let the crate-level refusal below name the surviving rows.
            break;
        }
        // Trust: MONOTONICITY, enforced rather than argued — see `assemble`'s `spliced_veto`.
        //
        // The spliced set is materialised ONCE per round rather than rescanned per
        // record. The nested form this replaces was O(records x coverage_rows), and
        // pass 2 pushes exactly one coverage row per record, so the two lengths are
        // equal and it was quadratic in body count PER ROUND — on a loop that may run
        // up to `records.len() + 1` rounds, on what this change makes the normal path.
        // Same answer, same order, strictly less work: `spliced_now` is exactly the
        // predicate the filter asked for.
        let spliced_now: BTreeSet<u32> = assembled
            .coverage_rows
            .iter()
            .filter(|row| row.spliced)
            .map(|row| row.def_index)
            .collect();
        spliced_veto.extend(
            records
                .iter()
                .map(|r| r.def_index)
                .filter(|def_index| !spliced_now.contains(def_index)),
        );
        assembled = assemble(&crate_name, &records, &spliced_veto);
        record_first_refusals(&assembled.coverage_rows, &mut first_refusals);
        refusal_rounds += 1;
    }
    restore_vetoed_refusals(&mut assembled.coverage_rows, &first_refusals);
    tracing::debug!(
        crate_name = %crate_name,
        rounds = refusal_rounds,
        vetoed = spliced_veto.len(),
        spliced = assembled.spliced,
        "trust-ir-lower: unsignable Rust-ABI edge body refusal"
    );

    errors.append(&mut assembled.errors);
    if !errors.is_empty() {
        // Declaration contradictions are fatal BEFORE temporal/Clean joins. Their reserved
        // placeholders keep the dense ID table honest defensively, but no later relinker is
        // authorized to reinterpret a contradicted identity.
        return failed_semantic_finalization(errors, prepared_publication, emit_target.as_ref());
    }
    stamp_target_info_if_vacuous(tcx, &mut assembled.module);
    // Whole-module validation is deliberately deferred until every Clean-origin function,
    // relinked edge, disclosure row, and direct obligation has been installed.  Validating this
    // intermediate assembly would miss precisely the post-join mutations the final authority
    // boundary must cover.  The unconditional fail-closed check is immediately before rendering.
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
    // Trust (IR-3, design §5): the authored-contract disclosure — a DesignOnly
    // SpecModule from the typed `trust_contracts` query, non-claim by
    // construction; the tripwire re-run below covers it.
    if let Err(error) = crate::contract_disclosure::install_contract_disclosure(
        tcx,
        &assembled.assigned,
        &mut assembled.module,
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
    // Trust (R8-SEAM): `-Ztrust-ir-seam-reference=<report path>` is a TEST-ONLY tracked option
    // (`TRUST_AUTHORITY: EvidenceControl`, unset in every real build): it also runs the
    // pre-R8-SEAM seam over the pre-R8-SEAM differential (`seam_reference.rs`) and fails
    // finalization on any difference in the verdicts or the UC probe's traced outcomes — it can
    // only ADD an error. An option, not an environment variable: ambient inputs are banned for
    // Trust behavior (`LEGACY_TRUST_SEMANTIC_ENV_VARS`), and a hooked compile must not share an
    // artifact or incremental identity with an unhooked one.
    let seam = match tcx.sess.opts.unstable_opts.trust_ir_seam_reference.as_deref() {
        Some(report) => seam_reference::cross_checked(&records, &assembled, report, &mut errors),
        None => run_seam_differentials(&records, &assembled, None).0,
    };
    errors.extend(install_seam_outcomes(&mut assembled.coverage_rows, &seam));
    if !errors.is_empty() {
        // A partial, duplicate, unexpected, or internally inconsistent seam stream cannot back a
        // per-body evidence artifact. Abort even when no dump was requested so tracing and
        // publication share the same exact inventory contract.
        return failed_semantic_finalization(errors, prepared_publication, emit_target.as_ref());
    }

    // Trust (IR-1, design §3.2): append the Clean-origin trust-ir spellings —
    // AFTER the seam differentials (their population is the THIR records and
    // must not see appended rows) and BEHIND a fresh authority-tripwire run
    // (appended functions are claim-free by construction; this re-run is the
    // enforcement, not a formality). Ids stay dense: minted at push in
    // `clean_origin_join`.
    // Trust: the Clean call recorder receives only identities of bodies this
    // assembly actually spliced. A display name or a raw DefIndex is never a
    // substitute for the matching recorded definition and module-owned FuncId.
    let mut clean_rust_bodies = Vec::with_capacity(assembled.assigned.len());
    for &(def_index, func_id) in &assembled.assigned {
        let Ok(record_index) = records.binary_search_by_key(&def_index, |r| r.def_index) else {
            errors.push(format!(
                "Clean call binding has FuncId({}) for unrecorded Rust DefIndex({def_index})",
                func_id.index()
            ));
            continue;
        };
        let record = &records[record_index];
        clean_rust_bodies.push(crate::clean_origin_join::RustBodyIdentity {
            def_index,
            definition: record.definition,
            func_id,
            abi: record.abi,
            kind: record.kind,
            def_path: record.def_path.clone(),
        });
    }
    if !errors.is_empty() {
        return failed_semantic_finalization(errors, prepared_publication, emit_target.as_ref());
    }
    let prepared_clean_origin = clean_origin.map(|outcomes| {
        crate::clean_origin_join::prepare_clean_origin_with_rust_callees(
            &assembled.module,
            outcomes,
            &mut errors,
            &clean_rust_bodies,
            // Trust (WS5.2): the same declaration ledger the link below receives — a Clean
            // definition is published IN its Rust declaration's row (one symbol, one row).
            &assembled.decl_keys,
        )
    });
    let unrecorded_clean_origin = crate::clean_origin_join::CleanOriginJoinSummary::not_recorded();
    let prepared_clean_summary = prepared_clean_origin
        .as_ref()
        .map_or(&unrecorded_clean_origin, |prepared| prepared.summary());
    // The Clean join's historical overlap guard compared operational names. That is only a
    // display check: macro-expanded THIR definitions may now carry a stable collision suffix.
    // Source DefIndex is the shared identity in this same rustc crate, so enforce the bijection
    // here before any declaration edge is re-pointed.
    errors.extend(clean_origin_thir_overlap_errors(
        &assembled.assigned,
        &prepared_clean_summary.emitted,
    ));
    if !errors.is_empty() {
        return failed_semantic_finalization(errors, prepared_publication, emit_target.as_ref());
    }
    // Trust (IR-5, design §6.5): re-point the caller's fail-closed declaration
    // edges onto the appended Clean-origin definitions — post-append, per-edge
    // arity-guarded, and shape-certified per touched function by the same
    // EXECUTABLE remap certificate discipline pass 2 argues (the pass-3 writer
    // and its guards live in `clean_origin_join`; this frozen file only plumbs).
    // Trust: publish the prepared batch only after exact declaration linking
    // and whole-module validation of any pending Rust call plans succeeds.
    let mut clean_origin_summary = match prepared_clean_origin {
        Some(prepared) => crate::clean_origin_join::link_prepared_clean_origin(
            &mut assembled.module,
            prepared,
            &assembled.decl_keys,
            &mut errors,
        ),
        None => unrecorded_clean_origin,
    };
    errors.extend(direct_authority_inventory_errors(&assembled.module));
    if !errors.is_empty() {
        return failed_semantic_finalization(errors, prepared_publication, emit_target.as_ref());
    }
    // Trust (plan step 3.4, D37): the join hands over the authenticated published token of
    // every `gate` row; with the Clean def's exact definition identity it is this Session's
    // carrier ledger (`crate::AuthenticatedCleanRow`, plumbing only).
    let clean_ledger: Vec<crate::AuthenticatedCleanRow> = clean_origin_summary
        .take_gated()
        .into_iter()
        .map(|row| {
            let def_index = row.published.source_def_index();
            let definition = crate::lineage::DefinitionIdentity::from_def_id(
                tcx,
                rustc_span::def_id::DefId {
                    krate: LOCAL_CRATE,
                    index: rustc_span::def_id::DefIndex::from_u32(def_index),
                },
            );
            crate::AuthenticatedCleanRow::new(row.func_id, def_index, definition, row.published)
        })
        .collect();

    // Trust (Step 2/3, owner directive 2026-08-30): direct-lane obligation
    // birth — drain the session registry the lowering populated, install
    // Pending claim-free rows against the assembled module (dense FuncIds,
    // post clean-origin append so the pre-birth runs above stay meaningful),
    // then enforce the RECORDED tier over the result. Run 4 is the only run
    // that applies the recorded tier; runs 1-3 above stay pre-birth
    // zero-checks at both tiers.
    let direct_tier = DIRECT_OBLIGATION_CAPABILITY.tier();
    if direct_tier.admits_pending_obligation_rows() {
        let registry = tcx
            .sess
            .with_trust_compiler_state::<crate::direct_obligations::DirectObligationRegistry, _>(
                std::mem::take,
            );
        let outcome = crate::direct_obligations::install_direct_obligations(
            &mut assembled.module,
            &crate_name,
            &assembled.assigned,
            registry,
            &mut errors,
        );
        tracing::debug!(
            installed = outcome.installed,
            bodies_installed = outcome.bodies_installed,
            skipped_unspliced = outcome.bodies_skipped_unspliced,
            rows_without_range = outcome.rows_without_range,
            "trust-ir-lower: direct obligation install"
        );
    }
    errors.extend(crate::direct_obligations::inventory_errors_at_tier(
        &assembled.module,
        direct_tier,
    ));
    if !errors.is_empty() {
        return failed_semantic_finalization(errors, prepared_publication, emit_target.as_ref());
    }

    // Pending-const sentinels are invalid producer state even when the caller requested no
    // artifact. Keep this beside the unconditional validator so the semantic result cannot
    // depend on whether a dump path happened to be configured.
    let leftover_sentinels = count_const_sentinels(&assembled.module);
    if leftover_sentinels > 0 {
        errors.push(format!(
            "final Trust-IR module contains {leftover_sentinels} unpatched pending-const \
             sentinel(s)"
        ));
    }

    // Trust (v41 `RustAbiVararg`, v7/D3): the PRODUCER's own refusal for every
    // bodyless Rust-ABI declaration it could not sign — deliberately BEFORE the
    // validator below, and on the final module, so a user reading this failure is
    // told the cause (which callee, and why it has no signature) instead of only
    // the structural symptom `RustAbiVararg` reports about the row. Ordering is
    // the whole point: the validator's message names a FuncTy index on a
    // synthesized declaration name, which is not a place anyone can act on.
    // Every row signed by a later pass — the Clean-origin join signs the
    // declaration its appended definition shadows — is re-checked out of this
    // list against the module as emitted.
    // Trust (owner call 2026-09-17(b)): the ORDINARY case no longer reaches here — the bodies
    // that mint such an edge were refused before assembly, so their declaration was never
    // minted. What is left is the residue this function's doc enumerates, and the message says
    // which of the three it is.
    errors.extend(unsignable_declaration_refusals(
        &assembled.module,
        &assembled.unsignable_declarations,
        &clean_origin_local_defs,
    ));

    // Trust (v41 CODEGEN LICENSE): STAMP `Function.body_gate` on the assembled
    // module. THIS IS THE LAST MUTATION, and it must be here — above the
    // validator, above the F1 handoff clone, above artifact rendering and above
    // publication — because every one of those consumes the module and the
    // license is part of what they consume. Until this landed the v41 field
    // licensed NOTHING on the wire: `compute_codegen_license` computed the
    // answer and published it only as a side channel
    // (`PublishedCrateModule::codegen_inventory`), so every function this
    // producer emitted carried `body_gate: None` — "no licensing claim" — and a
    // consumer reading the artifact could not tell a direct-lane body from an
    // appended below-tier Clean-origin definition.
    //
    // `stamp_codegen_license` REFUSES MORE and ADMITS NOTHING NEW: it makes one
    // `compute_codegen_license` call, writes its answer into the module, and the
    // inventory is then read BACK off those stamps, so the claim and the
    // inventory cannot disagree. See that function for the three states and for
    // why an unlicensed body is affirmatively `ungated` rather than silent.
    // Trust (plan step 3.4, design §5.2): leg 4 per function. A ledger entry that no longer
    // authenticates its Function is a compiler self-disagreement, fatal like every carrier-gate
    // disagreement (`crate::clean_carrier_authenticated` decides; this file only plumbs).
    let clean_carrier =
        crate::clean_carrier_authenticated(&assembled.module, &clean_ledger, &mut errors);
    let codegen_license_refusal =
        stamp_codegen_license(&mut assembled.module, &assembled.assigned, &clean_carrier);
    // The ledger is exactly the rows the license kept stamped: a refused license (legs 1-4)
    // stamps every body `Ungated`, and an unstamped row is no ledger entry.
    let carrier_stamped = clean_carrier_stamps(&assembled.module);
    let mut clean_ledger = clean_ledger;
    clean_ledger.retain(|row| carrier_stamped.contains(&row.func_id()));
    {
        let (gated, ungated, no_claim) = license_stamp_census(&assembled.module);
        tracing::info!(
            crate_name = %crate_name,
            direct = assembled.assigned.len(),
            gated,
            ungated,
            no_claim,
            license_refused = codegen_license_refusal.is_some(),
            authority = TRUST_DIRECT_LANE_AUTHORITY,
            "trust-ir-lower: v41 codegen license stamped"
        );
    }

    // Trust (#181 completion gate): validate the exact final module after every append, relink,
    // disclosure, and obligation-birth step, and before either serialization or publication.
    // This runs even when no artifact was requested. An invalid producer result is a semantic
    // compilation failure, never a log-only scorecard row.
    errors.extend(final_module_validation_errors(&assembled.module));
    if !errors.is_empty() {
        return failed_semantic_finalization(errors, prepared_publication, emit_target.as_ref());
    }

    // Read-only diagnostic observer. This exact same-Session assignment map
    // connects borrowed MIR captures to the actual final module; display names
    // are never a join key. It changes no module, verdict, or coverage row.
    scalar_correspondence::observe(
        tcx, &assembled.module, &assembled.assigned, &records, &expected_body_indices,
    );

    // F1 HANDOFF (see `crate::AssembledCrateModuleForCodegen`): when the
    // trust-ir codegen frontend is active, store the assembled, call-linked
    // module AND its exact (DefIndex, DefinitionIdentity) -> FuncId index. A
    // display path is not identity: macro expansion can give multiple spliced
    // definitions the same path, and those functions were collision-renamed
    // above. Keeping `assigned` and the BodyRecord identity together is the
    // only handoff that can still select those bodies after renaming.
    //
    // The unconditional sentinel/module validation above and the checked
    // handoff constructor below ensure codegen never sees either an artifact
    // the producer would refuse or an id map that points at a declaration.
    if tcx.sess.trust_cg_frontend_is_trust_ir() {
        let mut bodies = Vec::with_capacity(assembled.assigned.len());
        for &(def_index, func_id) in &assembled.assigned {
            let Ok(record_index) = records.binary_search_by_key(&def_index, |r| r.def_index) else {
                errors.push(format!(
                    "assembled codegen handoff has FuncId({}) for unrecorded DefIndex({def_index})",
                    func_id.index()
                ));
                continue;
            };
            bodies.push((def_index, records[record_index].definition, func_id));
        }
        if !errors.is_empty() {
            return failed_semantic_finalization(
                errors,
                prepared_publication,
                emit_target.as_ref(),
            );
        }
        // Trust (plan step 3.4): the handoff indexes the authenticated Clean rows beside the
        // Rust bodies and keeps the ledger, bound to this Session.
        let handoff = match crate::AssembledCrateModuleForCodegen::checked_with_ledger(
            std::sync::Arc::new(assembled.module.clone()),
            bodies,
            clean_ledger,
            Some(crate::CleanLedgerSession::of(tcx.sess)),
        ).and_then(|handoff| handoff.retain_declarations(&assembled.codegen_declarations)) {
            Ok(handoff) => handoff,
            Err(error) => {
                errors.push(error);
                return failed_semantic_finalization(
                    errors,
                    prepared_publication,
                    emit_target.as_ref(),
                );
            }
        };
        tcx.sess.with_trust_compiler_state::<crate::AssembledCrateModuleForCodegen, _>(
            |slot| *slot = handoff,
        );
    }

    // Trust (B9-A): seam verdicts above are returned regardless of artifact
    // output. Dump and first-class emit targets share the exact same rendered
    // module, but each gets a target-specific, digest-bearing commit marker.
    let artifact_requested = dump_dir.is_some() || first_class_emit_requested;
    let mut publication_errors = publication_prepare_errors;
    let mut rendered = None;
    if artifact_requested {
        if publication_errors.is_empty() {
            match coverage_json(
                &crate_name,
                &assembled.coverage_rows,
                assembled.spliced,
                assembled.declarations,
                &clean_origin_summary,
            )
            .and_then(|coverage| {
                crate::source_static_readback::append_to_coverage(
                    coverage,
                    source_static_readback.as_deref(),
                )
            }) {
                Ok(coverage) => match render_publication_bytes(&assembled.module) {
                    Ok((bin, txt)) => rendered = Some((coverage, bin, txt)),
                    Err(error) => publication_errors.push(error),
                },
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

    // Trust (gap G2): PUBLISH the assembled module. Until now this function
    // RENDERED the crate module and then dropped it, so the one object the
    // two-language plan is built around existed for the length of this call and
    // was reachable by nobody. See the `PublishedCrateModule` block above for
    // the mechanism, the choice of Session state, and how the codegen license
    // discharges the "no ungated Clean-origin body becomes reachable" constraint.
    //
    // LAST. `publish_crate_module` owns both preconditions — `errors` empty and
    // zero leftover pending-const sentinels — so they cannot be lost by a later
    // edit to this seam. `publication_errors` (already moved into `dump`) is
    // deliberately NOT consulted: it reports the DISK transaction, and a failed
    // artifact write says nothing about the in-memory module.
    //
    // `assigned` is TAKEN rather than borrowed: `assembled.module` moves into
    // the publication, and taking the (small, `Copy`-element) assignment first
    // keeps the move and the read of a sibling field out of one expression.
    // Nothing below reads either field.
    let assigned = std::mem::take(&mut assembled.assigned);
    // ANCHOR-PUBLICATION-LAST (read by `crate_module_publication_order_tests`).
    // Keyed on this comment rather than on the call's spelling: the call took a
    // sixth argument when the v41 license stamp landed, which rustfmt then
    // wrapped, and a source-order test must not break on line wrapping.
    publish_crate_module(
        tcx.sess,
        &crate_name,
        assembled.module,
        &assigned,
        &errors,
        codegen_license_refusal,
        std::mem::take(&mut clean_origin_summary.pending_rust_calls),
    );

    FinalizeSummary { seam, refused_bodies, dump, errors, direct_obligations: DIRECT_OBLIGATION_CAPABILITY }
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
// Tool attributes are `Attribute::Tool` (`get_all_attrs` preserves them
// verbatim; built-ins are parsed+stripped), so a path match on `[trust, var|action]`
// plus `meta_item_list()` name=value extraction is the correct read idiom
// (mirrors `trust_verify::item_has_trust_attr`).
// Ownership walks stop at the nearest action Self: it is an explicit semantic
// machine boundary, so unrelated wrappers may embed it freely. Ambiguity before
// that boundary and any by-value path connecting two action owners fail closed.
// ---------------------------------------------------------------------------

/// Tool attributes carry their diagnostic span even after upstream removed
/// `AttrItem::id`. A span is not occurrence identity: a proc macro may assign
/// the same span to several different attributes.
fn tool_span(attr: &rustc_attr_ir::Attribute) -> Span {
    match attr {
        rustc_attr_ir::Attribute::Tool(item) => item.span,
        rustc_attr_ir::Attribute::Parsed(_) | rustc_attr_ir::Attribute::DeriveHelper(_) => {
            panic!("tool attributes are always `Attribute::Tool`")
        }
    }
}

/// Does this attribute's path equal `trust::<name>`?
fn is_trust_attr(attr: &rustc_attr_ir::Attribute, name: &str) -> bool {
    matches!(
        attr.path().as_slice(),
        [tool, n] if tool.as_str() == "trust" && n.as_str() == name
    )
}

/// Crate-wide placement accounting for the temporal tool attributes.
///
/// Traverse the same complete maps as `hir_walk_attributes`, retaining each
/// target's owner/local HIR ID and the ordinal in its full attribute slice.
/// Consumption reads that exact slice through `hir_attrs`, just as local
/// `get_all_attrs` does. Neither shared source spans nor another attribute on
/// the same target can cause an unsupported occurrence to appear consumed.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct TemporalAttributeOccurrence {
    target: rustc_hir::HirId,
    index: usize,
    name: &'static str,
}

#[derive(Default)]
struct TemporalAttributeAudit {
    occurrences: Vec<(TemporalAttributeOccurrence, Span)>,
    consumed: FxHashSet<TemporalAttributeOccurrence>,
}

impl TemporalAttributeAudit {
    fn collect(tcx: TyCtxt<'_>) -> Self {
        let mut audit = Self::default();
        for owner in tcx.hir_crate_items(()).owners() {
            for &(local_id, attrs) in tcx.hir_attr_map(owner).map.iter() {
                let target = rustc_hir::HirId { owner, local_id };
                for (index, attr) in attrs.iter().enumerate() {
                    for name in ["var", "action"] {
                        if is_trust_attr(attr, name) {
                            let occurrence = TemporalAttributeOccurrence { target, index, name };
                            audit.occurrences.push((occurrence, tool_span(attr)));
                        }
                    }
                }
            }
        }
        audit
    }

    fn consume(&mut self, tcx: TyCtxt<'_>, did: LocalDefId, name: &'static str) {
        let target = tcx.local_def_id_to_hir_id(did);
        self.consumed.extend(
            tcx.hir_attrs(target)
                .iter()
                .enumerate()
                .filter(|(_, attr)| is_trust_attr(attr, name))
                .map(|(index, _)| TemporalAttributeOccurrence { target, index, name }),
        );
    }

    fn reject_unconsumed(self, tcx: TyCtxt<'_>) -> Result<(), TemporalCarryError> {
        let Some((occurrence, span)) =
            self.occurrences.into_iter().find(|(key, _)| !self.consumed.contains(key))
        else {
            return Ok(());
        };
        let attribute = occurrence.name;
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

/// Trust (WS5.9, F-117): the `file:line:col: line:col` location of a span in the shape of
/// `SourceMap::span_to_diagnostic_string`, but with the file rendered
/// `prefer_remapped_unconditionally` — the ONE rendering every file string that reaches a
/// published module takes (`LowerCx::to_source_span` for `Module.files`, the identity lane
/// for obligation rows). This is the string a `SpecAnchor.span` carries.
///
/// Why not `span_to_diagnostic_string` (the pre-WS5.9 spelling): rustc documents it "Must not
/// be emitted to build artifacts as this may leak local file paths", and it follows the
/// DIAGNOSTICS component of `--remap-path-scope`. Under cargo's `trim-paths` default
/// (`object`) diagnostics are NOT in scope, so the anchor row of a `#[trust::action]` crate
/// embedded the checkout path while `Module.files` did not — one module, two renderings,
/// and G8 byte identity lost on exactly the crates that carry a temporal spec. The
/// run-make test `trust-ir-remap-path-prefix` pins this row under `--remap-path-scope=object`.
/// Without any `--remap-path-prefix` the rendering is the local name, so the string is
/// unchanged.
fn embeddable_span_string(tcx: TyCtxt<'_>, span: Span) -> String {
    let (source_file, lo_line, lo_col, hi_line, hi_col) =
        tcx.sess.source_map().span_to_location_info(span);
    match source_file {
        Some(sf) => format!(
            "{}:{lo_line}:{lo_col}: {hi_line}:{hi_col}",
            sf.name.prefer_remapped_unconditionally()
        ),
        None => "no-location".to_string(),
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
    attr: &rustc_attr_ir::Attribute,
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
    attrs: &[rustc_attr_ir::Attribute],
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

/// Trust (WS5.2): does the assembled row `function` corroborate a temporal action whose def path
/// is `def_path`?
///
/// Before WS5.2 the check was `!is_declaration() && name == def_path`, and a spliced body's name
/// WAS its def path — EXCEPT that pass 2 renamed every member of a display-path collision set to
/// `!trust_definition::<path>::<definition>`, so a def path two spliced bodies shared never
/// matched and the action was refused. `Function.name` is the link-time symbol now (injective,
/// so there is no rename to rely on) and the def path is `display_path`; this keeps BOTH halves:
/// the row is a definition displaying exactly `def_path`, AND no other body-bearing row displays
/// it. The rows this runs over are exactly the spliced Rust bodies (the Clean-origin join has not
/// appended anything yet), which is the set pass 2's collision count ranged over, so the check is
/// exactly as strong as it was.
fn temporal_action_row_corroborates(module: &Module, function: FuncId, def_path: &str) -> bool {
    let displays = |row: &Function| row.display_path.as_deref() == Some(def_path);
    module.function_by_id(function).is_some_and(|row| !row.is_declaration() && displays(row))
        && module.functions.iter().filter(|row| !row.is_declaration() && displays(row)).count() == 1
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
            attribute_audit.consume(tcx, field_def.did.expect_local(), "var");
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
        attribute_audit.consume(tcx, did.expect_local(), "action");
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
        // Trust (WS5.2): the def path is the DISPLAY identity now; `Function.name` is the
        // link-time symbol. The check is unchanged in strength — see
        // `temporal_action_row_corroborates`, which also keeps the refusal the pre-WS5.2
        // collision rename used to make.
        if !temporal_action_row_corroborates(assembled, function, &symbol) {
            return Err(TemporalCarryError::FunctionIdentityMismatch {
                action: name,
                symbol,
                function,
            });
        }
        // Trust (WS5.2): the anchor's `rust_symbol` is the bound row's NAME — its link-time
        // symbol — which trust-ir's spec link compares to `Function.name` (a mismatch is
        // `InvalidSpecAnchorFunction`). The def path it was spelled by before is that row's
        // display path, corroborated just above.
        let Some(rust_symbol) = assembled.function_by_id(function).map(|f| f.name.clone()) else {
            return Err(TemporalCarryError::FunctionIdentityMismatch {
                action: name,
                symbol,
                function,
            });
        };
        actions.push(TemporalActionDecl {
            owner,
            name,
            function,
            rust_symbol,
            span: embeddable_span_string(tcx, tcx.def_span(did)),
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
                // Trust (vtable slice 15): ANY length — a deferred local const of a
                // first-class scalar-element `[T; N>0]` (`Ty::Array(_, N)`) defers under the
                // same sentinel; the finalizer's Array arm decodes it. `Ty::Array(_, 0)` was
                // already here (B7).
                | Ty::Struct(_) | Ty::Tuple(_) | Ty::Enum(_) | Ty::Array(..)
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

/// Trust (WS5.2): fill [`BodyRecord::link_symbol`] and [`BodyRecord::callee_links`] for every
/// record assembly may splice — see `crate::link_symbol` for what each symbol is and why none is
/// ever guessed.
///
/// ONLY SPLICE CANDIDATES (`splice_ok`, read, never changed here). A declaration is minted only
/// from a spliced body's edge and only a spliced body is named, so nothing is asked of
/// `symbol_name` for a body that cannot reach the module — the finalizer stays inside the
/// population whose MIR it already forced — and a body `splice_ok` already refuses (a `symbolic`
/// generic body, a placeholder lane) keeps exactly its old coverage row. A candidate fn body with
/// no computable symbol — in practice a closure whose ENCLOSING item is generic — is REFUSED
/// here, by name ([`crate::link_symbol::no_link_symbol_reason`]), which makes `splice_ok` refuse
/// it through its ordinary first line; nothing downstream has to know a symbol can be missing.
///
/// Returns those refusals as [`RefusedBody`] rows, so `-Ztrust-ir-lower=strict` reports them at
/// the body's span exactly like the re-splice fixpoint's (a body the producer could not put in
/// the module is a body it did not fully lower).
fn stamp_link_symbols(tcx: TyCtxt<'_>, records: &mut [BodyRecord]) -> Vec<RefusedBody> {
    stamp_link_symbols_with(
        records,
        |def_index, def_path| {
            let index = rustc_span::def_id::DefIndex::from_u32(def_index);
            let def_id = DefId { krate: LOCAL_CRATE, index };
            crate::link_symbol::definition_link_symbol(tcx, def_id, def_path)
        },
        |callee| { let foreign_signature = crate::foreign_signature::read(tcx, callee);
            let foreign_source = foreign_signature.as_ref()
                .and_then(|_| crate::foreign_signature::ForeignSource::capture(tcx, callee));
            CalleeLink {
            symbol: crate::link_symbol::callee_link_symbol(tcx, callee),
            producer: crate::link_symbol::declaration_producer(tcx, callee.def_id),
            instance_lane_spelling: crate::link_symbol::keeps_instance_lane_spelling(tcx, callee),
            foreign_signature,
            foreign_source,
        } },
    )
}

/// The TyCtxt-free body of [`stamp_link_symbols`]: `definition_symbol(def_index, def_path)` is
/// `tcx.symbol_name` of a fn body's identity instance (or the named refusal), `callee_link` the
/// finalization facts of one ledgered callee. Split out so the property the frozen-files waiver
/// states — it NAMES splice candidates and only ever ADDS a refusal; `splice_ok` is read, never
/// widened — is executed by a unit test with a fixture symbol function.
fn stamp_link_symbols_with(
    records: &mut [BodyRecord],
    mut definition_symbol: impl FnMut(u32, &str) -> Result<String, String>,
    mut callee_link: impl FnMut(&crate::CalleeRef) -> CalleeLink,
) -> Vec<RefusedBody> {
    let candidates: Vec<usize> = {
        let view: &[BodyRecord] = records;
        (0..view.len())
            .filter(|&index| {
                view[index].function.is_some() && splice_refusal(&view[index], view).is_none()
            })
            .collect()
    };
    let mut refused = Vec::new();
    for index in candidates {
        let r = &mut records[index];
        match r.kind {
            BodyKind::Fn => match definition_symbol(r.def_index, &r.def_path) {
                Ok(symbol) => r.link_symbol = Some(symbol),
                Err(reason) => {
                    bump_unsupported(&mut r.unsupported, &reason);
                    refused.push(RefusedBody { def_index: r.def_index, reason });
                    continue;
                }
            },
            BodyKind::ConstInit | BodyKind::StaticInit => {
                r.link_symbol = Some(crate::link_symbol::initializer_symbol(r.definition));
            }
        }
        r.callee_links = r.callees.iter().map(&mut callee_link).collect();
    }
    refused
}

/// Trust (WS5.2): ATTRIBUTE every bodyless declaration whose link-time symbol another row of
/// the assembled module also holds to the spliced bodies that mint an edge to it, so the
/// producer refuses those bodies instead of publishing two rows under one symbol.
///
/// `Function.name` is the link-time symbol, so one symbol names at most one row
/// (`DuplicateFunctionSymbol`). A declaration row is keyed by its ledger identity plus the
/// observations the `|ret:` / `|nres:` splits add, so one callee instance CAN become two rows
/// with one symbol — two spellings of one function the producer cannot choose between. Every
/// row of such a set is refused for (never "the first one wins"), and a declaration sharing a
/// symbol with a DEFINITION is refused for too (the definition stays: it is the callee's own
/// body). Reserved never-linkable spellings (`!…`) are not symbols and are not considered.
///
/// Same shape and the same attribution as [`unsignable_minting_bodies`]: read off the assembled
/// IR (pass 2 writes a minted declaration's id into exactly the body that minted it), and a body
/// carrying an instruction shape the edge scan does not model is refused for every colliding row
/// — strictly more conservative. Returns `(def_index, reason)`, sorted and deduplicated.
fn symbol_collision_minting_bodies(assembled: &Assembled) -> Vec<(u32, String)> {
    let module = &assembled.module;
    let mut holders: BTreeMap<&str, Vec<&Function>> = BTreeMap::new();
    for function in &module.functions {
        holders.entry(function.name.as_str()).or_default().push(function);
    }
    // (declaration id, its symbol, its display, who else holds the symbol)
    let mut colliding: Vec<(u32, String, String, String)> = Vec::new();
    for (name, rows) in &holders {
        if rows.len() < 2 || name.starts_with('!') {
            continue;
        }
        for row in rows.iter().filter(|row| row.is_declaration()) {
            let holder = rows
                .iter()
                .filter(|other| other.id != row.id)
                .map(|other| {
                    format!(
                        "{} FuncId {} `{}`",
                        if other.is_declaration() { "declaration" } else { "definition" },
                        other.id.index(),
                        other.display_path.as_deref().unwrap_or(other.name.as_str()),
                    )
                })
                .collect::<Vec<_>>()
                .join(", ");
            colliding.push((
                row.id.index(),
                (*name).to_string(),
                row.display_path.clone().unwrap_or_else(|| row.name.clone()),
                holder,
            ));
        }
    }
    if colliding.is_empty() {
        return Vec::new();
    }
    let colliding_ids: BTreeSet<u32> = colliding.iter().map(|(id, ..)| *id).collect();
    let mut refusals: Vec<(u32, String)> = Vec::new();
    for function in &module.functions {
        let Some(&(def_index, func_id)) = assembled.assigned.get(function.id.index() as usize)
        else {
            continue;
        };
        if func_id != function.id {
            continue;
        }
        let mut named: BTreeSet<u32> = BTreeSet::new();
        let mut unmodelled = false;
        for node in function.blocks.iter().flat_map(|block| &block.body) {
            match inst_referenced_funcs(&node.inst) {
                Some(funcs) => named.extend(
                    funcs.into_iter().map(|f| f.index()).filter(|id| colliding_ids.contains(id)),
                ),
                None => unmodelled = true,
            }
        }
        for (id, symbol, display, holder) in &colliding {
            if !unmodelled && !named.contains(id) {
                continue;
            }
            refusals.push((
                def_index,
                crate::link_symbol::symbol_collision_reason(symbol, display, holder),
            ));
        }
    }
    refusals.sort();
    refusals.dedup();
    refusals
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
        // Trust (wave-SD): the LOCAL-STATIC leg — evaluate each deferred static's initializer
        // (safe here: `run_required_analyses` has forced `mir_built` for every body owner, so
        // the CTFE reachability set that cycles inside `mir_built` is fully built) and patch
        // the scalar global's `Constant::PhantomData` placeholder. Runs before the scalar/
        // composite loop for the same reason the str leg does: it patches a GLOBAL and must
        // never reach `eval_pending_const`'s shape tripwire. Fail-closed rows for: eval/decode
        // failure, a producer/finalizer shape disagreement (the re-derive cross-check), a
        // missing slot, and a patch conflict.
        for i in 0..r.pending_consts.len() {
            let pc = r.pending_consts[i].clone();
            let Some(gid) = pc.static_global else { continue };
            let rty = tcx.type_of(pc.def_id).skip_binder();
            let Some(g) = r.globals.get_mut(gid.as_usize()) else {
                bump_unsupported(&mut r.unsupported, "PendingStatic(global not found)");
                continue;
            };
            let Some(constant) = crate::eval_static_scalar_value(tcx, rty, &g.ty, pc.def_id)
            else {
                bump_unsupported(&mut r.unsupported, "PendingStatic(eval failed at finalize)");
                continue;
            };
            // Re-derive cross-check: the finalizer's view of the shape must match the
            // producer's recorded one (mirrors `eval_pending_const`'s width tripwire).
            let shape_ok = match (&constant, pc.is_bool) {
                (Constant::Bool(_), true) => true,
                (Constant::Int(_), false) => pc.bits > 0,
                // Trust (wave-SD2): a composite static decodes to an Aggregate; the record
                // carries composite=true with the scalar shape fields zeroed.
                (Constant::Aggregate(_), false) => pc.composite && pc.bits == 0 && !pc.signed,
                _ => false,
            };
            if !shape_ok {
                bump_unsupported(&mut r.unsupported, "PendingStatic(shape disagreement)");
                continue;
            }
            match &g.initializer {
                Some(Constant::PhantomData) => {
                    g.initializer = Some(constant);
                }
                Some(existing) if *existing == constant => {
                    // Benign repeated record for the same deduped global.
                }
                _ => {
                    bump_unsupported(&mut r.unsupported, "PendingStatic(global patch conflict)");
                }
            }
        }
        // Trust (wave-PC): the PROMOTED-LOCAL-CONST leg — evaluate each deferred const via the
        // SAME seam-safe path the generic loop uses (`eval_pending_const`; scalar rows need no
        // expected-ty context) and patch the global's `Constant::PhantomData` placeholder,
        // mirroring the wave-SD static leg row for row.
        for i in 0..r.pending_consts.len() {
            let pc = r.pending_consts[i].clone();
            let Some(gid) = pc.promoted_global else { continue };
            // Trust (wave-PC2): a composite row decodes against the GLOBAL's declared ty
            // (the mint-time `map_ty` spelling) + this body's registered tables — the B7 leg.
            let expected = r.globals.get(gid.as_usize()).map(|g| g.ty.clone());
            let Some(constant) =
                eval_pending_const(tcx, &pc, expected.as_ref(), &r.structs, &r.enums, &r.types)
            else {
                bump_unsupported(&mut r.unsupported, "PendingPromoted(eval failed at finalize)");
                continue;
            };
            let shape_ok = match (&constant, pc.is_bool, pc.is_float) {
                (Constant::Bool(_), true, false) => true,
                (Constant::Int(_), false, false) => pc.bits > 0,
                (Constant::Float(_), false, true) => pc.bits == 32 || pc.bits == 64,
                // Trust (wave-PC2, measured): the B7 leg decodes a TUPLE/STRUCT target to
                // `Aggregate` and a first-class ARRAY target to `Array` — accepting only the
                // former made every array const a `shape disagreement` (and, because the lane
                // intercepts before the pre-existing routes, REGRESSED bodies that used to
                // lower: `const B: u8 = (&A)[0]` went unsupported with an empty detail row,
                // which is what a seam `bump_unsupported` looks like from the coverage side).
                // v50: a uniform array decodes to its canonical `Constant::Splat` — the same
                // composite, in its one spelling.
                (
                    Constant::Aggregate(_) | Constant::Array(_) | Constant::Splat { .. },
                    false,
                    false,
                ) => pc.composite && pc.bits == 0,
                _ => false,
            };
            if !shape_ok {
                bump_unsupported(&mut r.unsupported, "PendingPromoted(shape disagreement)");
                continue;
            }
            let Some(g) = r.globals.get_mut(gid.as_usize()) else {
                bump_unsupported(&mut r.unsupported, "PendingPromoted(global not found)");
                continue;
            };
            match &g.initializer {
                Some(Constant::PhantomData) => {
                    g.initializer = Some(constant);
                }
                Some(existing) if *existing == constant => {}
                _ => {
                    bump_unsupported(&mut r.unsupported, "PendingPromoted(global patch conflict)");
                }
            }
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
            // Trust (wave-SC/SD): the str and static legs above already handled these records.
            if pc.str_global.is_some() || pc.static_global.is_some() || pc.promoted_global.is_some()
            {
                continue;
            }
            // Trust (B7): a composite pending const decodes against the PLACEHOLDER node's
            // mapped trust-ir type + this body's registered struct/enum tables (the same
            // per-body positional id space the node's Ty::Struct/Enum ids reference). A
            // missing placeholder yields None expected-ty and the eval fails closed; the
            // patch below then also reports the precise placeholder-not-found tag.
            let expected_ty = placeholder_ty(r.function.as_ref(), pc.value);
            match eval_pending_const(tcx, pc, expected_ty.as_ref(), &r.structs, &r.enums, &r.types) {
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
        // Trust (wave-SD): the static twin of the str ledger, and REQUIRED for the same
        // reason: an unpatched `Constant::PhantomData` initializer is not an instruction, so
        // the sentinel scan cannot see it, and a placeholder global must never splice as a
        // real value. Every record CLAIMING a static global must have produced a patched one.
        check_static_global_ledger(&r.globals, &r.pending_consts, &mut r.unsupported);
        check_promoted_global_ledger(&r.globals, &r.pending_consts, &mut r.unsupported);
    }
}

/// Trust (wave-SD): has `g` been rewritten from the `Constant::PhantomData` placeholder into a
/// REAL scalar initializer? Positive predicate, mirroring `str_global_patched`.
fn static_global_patched(g: &Global) -> bool {
    matches!(
        &g.initializer,
        Some(Constant::Bool(_)) | Some(Constant::Int(_)) | Some(Constant::Aggregate(_))
    )
}

/// Trust (wave-PC): the positive-LEDGER tripwire for promoted-local-const globals — the
/// wave-SD discipline verbatim: every record claiming one must have produced a patched,
/// real initializer (an unpatched `PhantomData` placeholder must never splice silently).
fn check_promoted_global_ledger(
    globals: &[Global],
    pending: &[PendingConst],
    unsupported: &mut Vec<(String, u64)>,
) {
    for pc in pending {
        let Some(gid) = pc.promoted_global else { continue };
        let ok = globals.get(gid.as_usize()).is_some_and(|g| {
            matches!(
                &g.initializer,
                Some(Constant::Bool(_))
                    | Some(Constant::Int(_))
                    | Some(Constant::Float(_))
                    | Some(Constant::Aggregate(_))
                    | Some(Constant::Array(_))
                    // v50: the canonical spelling of a uniform array initializer.
                    | Some(Constant::Splat { .. })
            )
        });
        if !ok {
            bump_unsupported(unsupported, "PendingPromoted(global not patched)");
        }
    }
}

/// Trust (wave-SD): the positive-LEDGER tripwire for deferred-static globals — every
/// `PendingConst` that claims one must have produced a patched, real-scalar initializer.
fn check_static_global_ledger(
    globals: &[Global],
    pending: &[PendingConst],
    unsupported: &mut Vec<(String, u64)>,
) {
    for pc in pending {
        let Some(gid) = pc.static_global else { continue };
        let ok = globals.get(gid.as_usize()).is_some_and(static_global_patched);
        if !ok {
            bump_unsupported(unsupported, "PendingStatic(global not patched)");
        }
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
    ) || matches!(
        // v50: a uniform byte payload (`"aa"`) is patched in its canonical `Splat` spelling.
        (&g.ty, &g.initializer),
        (Ty::Array(_, n), Some(Constant::Splat { len, .. })) if *n > 0 && n == len
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
    // v50 §3.1: the ONE canonical spelling (a uniform payload such as `"aa"` is a `Splat`),
    // built by trust-ir's constructor exactly as the producer's `emit_bytes_global` builds it.
    let init = Constant::array(bytes.iter().map(|b| Constant::Int(i128::from(*b))).collect());
    match (&g.ty, &g.initializer) {
        // The untouched placeholder.
        (Ty::Array(tid, 0), Some(Constant::Array(elems))) if elems.is_empty() => {
            let tid = *tid;
            g.ty = Ty::Array(tid, bytes.len() as u64);
            g.initializer = Some(init);
            true
        }
        // Already patched by an earlier record for the SAME deduped const — idempotent iff the
        // bytes agree (compared in the canonical spelling both records build), a conflict
        // otherwise.
        (Ty::Array(_, n), Some(existing))
            if *n as usize == bytes.len()
                && matches!(existing, Constant::Array(_) | Constant::Splat { .. })
                && *existing == init =>
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
    if crate::is_type_const(tcx, pc.def_id) {
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
    let uv = ty::AliasConst::new(tcx, crate::alias_const_kind_from_def_id(tcx, pc.def_id), args);
    let uv = tcx.erase_and_anonymize_regions(uv);
    let typing_env = ty::TypingEnv::fully_monomorphized();
    let valtree = match crate::quiet_const_valtree(tcx, typing_env, uv, pc.span) {
        Some(v) => v,
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
/// The hook stored no `GenericArgs` (tcx-interned); `identity_for_item` + region erasure
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
    // Trust (vtable slice 15): the body's pended types table — resolves the element of a
    // first-class `Ty::Array(TyId, N>0)` placeholder (the scalar-element array spelling).
    types: &[Ty],
) -> Option<Constant> {
    // An mgca `type const` must never be CTFE'd here (the observed ICE class); the hook's
    // deferral gate already refuses them — checked again, not assumed.
    if crate::is_type_const(tcx, pc.def_id) {
        return None;
    }
    // Trust (wave-IC): an INLINE const's identity args carry a SYNTHETIC type param
    // (`InlineConstArgs` appends the const's own type), so the all-regions test below can
    // never pass for one, and `type_of(inline).instantiate_identity()` is generic. Both are
    // REBUILT instead: the type from the flags the hook recorded off the use-site expression
    // (`pointer_width` disambiguates `usize`/`u64`; `char` was refused at the hook because
    // its encoding collides with `u32`), and the args as
    // `InlineConstArgs::new(parent-identity, ty)` — sound because the hook admitted only a
    // non-generic parent (its identity args all-region, re-checked here, not assumed).
    // Composite inline constants instead carry exact encoded site args and
    // use the shared reconstruction path below, including their result type.
    let (args, rty) = if crate::is_inline_const(tcx, pc.def_id) && pc.site_args.is_none() {
        if pc.composite {
            return None;
        }
        let parent = tcx.typeck_root_def_id(pc.def_id);
        let parent_args = ty::GenericArgs::identity_for_item(tcx, parent);
        if !parent_args.iter().all(|a| a.as_region().is_some()) {
            return None;
        }
        let rebuilt = if pc.is_bool {
            tcx.types.bool
        } else if pc.is_float {
            match pc.bits {
                32 => tcx.types.f32,
                64 => tcx.types.f64,
                _ => return None,
            }
        } else if pc.pointer_width {
            if pc.signed { tcx.types.isize } else { tcx.types.usize }
        } else {
            match (pc.signed, pc.bits) {
                (true, 8) => tcx.types.i8,
                (true, 16) => tcx.types.i16,
                (true, 32) => tcx.types.i32,
                (true, 64) => tcx.types.i64,
                (true, 128) => tcx.types.i128,
                (false, 8) => tcx.types.u8,
                (false, 16) => tcx.types.u16,
                (false, 32) => tcx.types.u32,
                (false, 64) => tcx.types.u64,
                (false, 128) => tcx.types.u128,
                _ => return None,
            }
        };
        (
            ty::InlineConstArgs::new(
                tcx,
                ty::InlineConstArgsParts { parent_args: parent_args.as_slice(), ty: rebuilt },
            )
            .args,
            rebuilt,
        )
    } else if let Some(enc) = &pc.site_args {
        // Trust (wave-GC): the encoded use-site args — rebuilt intern-equal
        // (`rebuild_site_args`'s own contract). The const's type is instantiated AT that
        // rebuild; any residual param means the encoding did not fully determine the
        // instantiation, and the placeholder keeps failing closed.
        let args = crate::to_mir::rebuild_site_args(tcx, enc)?;
        let rty = if crate::is_inline_const(tcx, pc.def_id) {
            // NonTypeSystemInline has no standalone type_of query. Its type
            // is the trailing synthetic argument (InlineConstArgs::ty).
            // Keep malformed metadata fallible instead of using expect_ty.
            args.into_iter().last()?.as_type()?
        } else {
            tcx.type_of(pc.def_id).instantiate(tcx, args).skip_normalization()
        };
        {
            use rustc_middle::ty::TypeVisitableExt as _;
            if rty.has_non_region_param() || rty.has_non_region_infer() {
                return None;
            }
        }
        (args, rty)
    } else {
        let args = ty::GenericArgs::identity_for_item(tcx, pc.def_id);
        if !args.iter().all(|a| a.as_region().is_some()) {
            return None;
        }
        // Shape tripwire: the const's declared type must match what the hook recorded off the
        // use-site expression type (same tcx, so a mismatch means a real bug — fail closed).
        // Trust: rust 1.99 — `EarlyBinder::instantiate_identity` returns `Unnormalized<T>`;
        // unwrap with `.skip_normalization()` (compiler-idiomatic; the shape check below is
        // structural and the valtree decode path never normalized here before either).
        (args, tcx.type_of(pc.def_id).instantiate_identity().skip_normalization())
    };
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
    let uv = ty::AliasConst::new(tcx, crate::alias_const_kind_from_def_id(tcx, pc.def_id), args);
    let uv = tcx.erase_and_anonymize_regions(uv);
    let typing_env = ty::TypingEnv::fully_monomorphized();
    let valtree = match crate::quiet_const_valtree(tcx, typing_env, uv, pc.span) {
        Some(v) => v,
        // Non-valtree'able, too generic, reported error, or TOO BIG (`quiet_const_valtree`)
        // all fail closed — never a guessed value.
        _ => return None,
    };
    // Trust (B7): the composite leg — recursive branch-valtree decode against the
    // placeholder's mapped type + the body's registered tables. Fail-closed on any
    // level the decoder cannot prove faithful (the caller records the precise
    // PendingConst tag). Scalars keep the exact pre-B7 tail below.
    if pc.composite {
        return finalize_valtree_to_constant(tcx, rty, valtree, expected_ty?, structs, enums, types, 0);
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
/// through the body's registered struct/enum tables and — Trust (vtable slice 15) — its pended
/// types table). Mirrors `map_ty`'s value model exactly:
/// tuples and AGGREGATE-element `[T; N > 0]` arrays are `Constant::Aggregate` under `Ty::Tuple`;
/// `[T; 0]` and (slice 15) SCALAR-element `[T; N > 0]` are `Constant::Array` under the
/// first-class `Ty::Array`; structs are field-ordered `Aggregate`s; enums are the
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
    types: &[Ty],
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
                out.push(finalize_branch_elem(tcx, c, frty, fex, structs, enums, types, depth + 1)?);
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
                out.push(finalize_branch_elem(tcx, c, *elem_rty, fex, structs, enums, types, depth + 1)?);
            }
            Some(Constant::Aggregate(out))
        }
        (ty::Array(..), Ty::Array(_, 0)) => {
            let branch = valtree.try_to_branch()?;
            branch.is_empty().then(|| Constant::Array(Vec::new()))
        }
        // Trust (vtable slice 15): a FIRST-CLASS scalar-element `[T; N>0]` placeholder — the
        // expected element type resolves through the body's pended types table (the same
        // positional id space the placeholder's `Ty::Array(TyId, _)` references), and the
        // decoded value takes the `Constant::Array` VARIANT (the interpreter's
        // `(Ty::Array, Constant::Array)` pairing). Double-keyed like every other arm: a length
        // mismatch, an unresolvable element id, or an element that fails its own pairing fails
        // the whole decode closed.
        (ty::Array(elem_rty, _), Ty::Array(tid, n)) => {
            let elem_ex = types.get(tid.as_usize())?;
            let branch = valtree.try_to_branch()?;
            if branch.len() as u64 != *n || branch.is_empty() {
                return None;
            }
            let mut out = Vec::with_capacity(branch.len());
            for c in branch.iter() {
                out.push(finalize_branch_elem(
                    tcx, c, *elem_rty, elem_ex, structs, enums, types, depth + 1,
                )?);
            }
            // v50 §3.1: the canonical spelling (a uniform decode is a `Splat`).
            Some(Constant::array(out))
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
                let frty = f.ty(tcx, *adt_args).skip_normalization();
                out.push(finalize_branch_elem(tcx, c, frty, &fd.ty, structs, enums, types, depth + 1)?);
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
                let frty = f.ty(tcx, *adt_args).skip_normalization();
                // Trust (B3-2c E5, the FINALIZER twin of the eager decoder's arm —
                // the paired-gate rule): a Unit-typed def field (the admission
                // invariant: drop-free ZST) finalizes as the canonical PhantomData;
                // recursing would produce Aggregate([]) which has no interpreter
                // pair under Ty::Unit (a trap = manufactured divergence).
                if matches!(fex, Ty::Unit) {
                    out.push(Constant::PhantomData);
                    continue;
                }
                out.push(finalize_branch_elem(tcx, *c, frty, fex, structs, enums, types, depth + 1)?);
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
    types: &[Ty],
    depth: usize,
) -> Option<Constant> {
    let ty::ConstKind::Value(v) = c.kind() else { return None };
    if v.ty != expected_rty {
        return None;
    }
    finalize_valtree_to_constant(tcx, v.ty, v.valtree, expected, structs, enums, types, depth)
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

/// Trust (B8 step 1): the CLOSED taxonomy of reasons `resolve_callee` refuses to link a callee
/// and mints a bodyless declaration instead.
///
/// # What this replaced, and what the anonymity cost
///
/// These five classes already existed — as five `format!` literals inside `resolve_callee`,
/// whose only job was to keep a local path from dedup-merging with an extern one. What did NOT
/// exist was any way to ask, of an assembled module, WHICH class a given declaration came from:
/// [`decl_id`] consumes the key for interning and drops it, so by the time
/// [`run_seam_differentials`] step 2 met a bodyless callee the sole surviving fact was
/// `Function::is_declaration()` — a bool.
///
/// So step 2 pushed one string for all five, and the scorecard folded the lot into a single
/// `clean-skip-extern-callee` class. Measured on `postbuild-slice20-control`: **983 clean rows
/// (919 MODELLED + 64 OPAQUE-COLLAPSE) across 577 files** — the largest single non-verdict class
/// in the corpus, and 50.0% of the MODELLED→Agreed gap, carried as one anonymous label that
/// names exactly one of the five things it holds. (How much of it is actually
/// [`Extern`](DeclKind::Extern) was not measurable until this slice; that is the point.)
///
/// A class that large with no internal structure cannot be ranked against, because its members
/// are retired by unrelated work: a [`LocalUnlowered`](DeclKind::LocalUnlowered) blocker falls
/// out of ordinary clean-rate waves with nobody aiming at it, a [`Havoc`](DeclKind::Havoc)
/// blocker needs monomorphization, and an [`Extern`](DeclKind::Extern) blocker needs foreign
/// callees modelled or the path proven dead. Naming them is the whole of this slice.
///
/// # Why an enum and not a prefix table
///
/// Making the taxonomy a type is what CLOSES the set. `resolve_callee` can no longer mint a
/// sixth class by writing a new `format!` — every key is built by [`decl_key`], and
/// [`DeclKind::from_key`] round-trips every variant (`decl_kind_round_trips`). A key that does
/// not parse is reported as `unclassified` and never folded into a neighbour: a residue means
/// this taxonomy has drifted from its producer, which is exactly the failure the split exists to
/// make visible.
///
/// # Variant order is TRACTABILITY, least tractable first
///
/// [`DeclKind::ALL`]'s order is load-bearing, and the variants are declared to match it. A body
/// whose closure carries several classes is attributed to the FIRST one present, so no class is
/// ever credited with a body that retiring it alone would not unblock. Each per-class count is
/// therefore a lower bound on what that class is worth — the honest direction for a number that
/// decides whether to spend a campaign. The scorecard reports `sole_blocker` alongside it, which
/// is the count to actually rank against.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
enum DeclKind {
    /// A genuinely foreign callee: one ledger identity, not local. No body exists anywhere in
    /// this crate to link, so nothing short of modelling the callee (or proving the call site
    /// dead — see [`row1_dead_path_probe`]) retires it.
    Extern,
    /// No ledger entry at all behind the emitted `FuncId` (`r.callees` has no row for it), so
    /// there is not even site evidence to type a return with. A producer instrumentation gap
    /// rather than a property of the program.
    Unknown,
    /// A FORCED-HAVOC edge — a generic call site, which declares even when its `DefIndex` has a
    /// perfectly clean local body (wave-20). Retired by monomorphization (B8 proper), never by
    /// clean-rate work.
    Havoc,
    /// Two or more distinct identities behind one body-local `FuncId`: malformed/legacy ledger
    /// input for the current dense allocator. Which body to link is a guess, so it declares.
    Ambiguous,
    /// A real local fn whose OWN body did not lower cleanly, so there was no spliced target to
    /// point at. CLEAN-RATE-COUPLED: the one class ordinary producer waves retire as a side
    /// effect. It has never had a bucket in any prediction this campaign has made.
    LocalUnlowered,
}

impl DeclKind {
    /// Every variant, in tractability order (see the type docs). The census reports in this
    /// order and the dominant-blocker rule takes the first present.
    const ALL: [DeclKind; 5] = [
        DeclKind::Extern,
        DeclKind::Unknown,
        DeclKind::Havoc,
        DeclKind::Ambiguous,
        DeclKind::LocalUnlowered,
    ];

    /// The dedup-key prefix. These strings are LOAD-BEARING for declaration identity —
    /// [`decl_id`] interns on the whole key, so changing one silently re-partitions the module's
    /// declarations and moves real IR. They are the pre-existing spellings byte for byte, which
    /// `decl_key_is_byte_identical_to_legacy_spelling` pins.
    fn prefix(self) -> &'static str {
        match self {
            DeclKind::Extern => "extern",
            DeclKind::Unknown => "unknown",
            DeclKind::Havoc => "havoc",
            DeclKind::Ambiguous => "ambiguous",
            DeclKind::LocalUnlowered => "local-unlowered",
        }
    }

    /// Recover the class from a minted key. `None` for anything this taxonomy does not know —
    /// the caller reports that as `unclassified`, never as a neighbouring class.
    ///
    /// Splitting on the FIRST `:` is safe in both directions: no prefix contains a `:`, and the
    /// remainder is free to (a `def_path` is `foo::bar`, and the call site may append
    /// `|nres:{n}`).
    fn from_key(key: &str) -> Option<DeclKind> {
        let (prefix, _) = key.split_once(':')?;
        DeclKind::ALL.into_iter().find(|k| k.prefix() == prefix)
    }
}

/// Build a class-prefixed declaration dedup key. The ONLY way one is minted.
fn decl_key(kind: DeclKind, rest: impl std::fmt::Display) -> String {
    format!("{}:{}", kind.prefix(), rest)
}

fn stable_text_hex(text: &str) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(text.len() * 2);
    for byte in text.bytes() {
        out.push(HEX[(byte >> 4) as usize] as char);
        out.push(HEX[(byte & 0x0f) as usize] as char);
    }
    out
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
    Decl {
        key: String,
        name: String,
        is_extern: bool,
        ret: Option<Ty>,
        /// Trust (v41): the callee's RECOVERED parameter types — ground truth from
        /// `tcx.fn_sig` carried on the ledger record, never a site observation (see
        /// [`crate::CalleeRef::params`]) — together with the STICKY WITHDRAWAL, in
        /// one value. `ParamSignature::Withdrawn` says a contributing `CalleeRef`
        /// recorded a short-arity call, so this declaration must stay unsigned
        /// across every body; it carries no parameter list, so "withdrawn but
        /// signed" is not a state this field can hold.
        params: crate::ParamSignature,
        abi: crate::calling_convention::FunctionAbi,
        /// Stable definition + concrete instance are declaration identity. `None` is reserved
        /// for the genuinely unknown/ambiguous synthetic lanes; neither signature nor display
        /// name substitutes for these fields.
        definition: Option<crate::lineage::DefinitionIdentity>,
        concrete_key: Option<crate::lineage::ConcreteCalleeKey>,
        /// Same-compilation source identity for a local-unlowered declaration. This is carried
        /// to the Clean-origin join; display paths are not linking authority.
        local_def_index: Option<u32>,
        /// Trust (WS5.2): the callee's link-time symbol and real producer, from crate
        /// finalization (`stamp_link_symbols`). `name` above stays the DISPLAY identity.
        link: CalleeLink,
    },
}

#[derive(Clone, Debug)]
struct DeclRecord {
    key: String,
    id: FuncId,
    name: String,
    ret: Option<Ty>,
    /// Sticky refusal state for the RESULT TYPE. Trust (wave-RETSPLIT): no longer the ordinary
    /// outcome of two bodies spelling one type differently — `decl_id` gives such an observation
    /// its own `|ret:`-suffixed row. It remains the FLOOR for the one thing that split cannot
    /// separate: two distinct `Ty`s sharing a `Debug` spelling.
    ret_conflict: bool,
    /// Trust (v41): the callee's RECOVERED parameter types (ground truth from
    /// `tcx.fn_sig`, carried on the ledger record — NOT a site observation), and
    /// its sticky poison. `None` means this producer cannot sign the declaration.
    /// Trust (v41 coherence): the parameter list AND the STICKY withdrawal, in one
    /// value, because they are one fact — see [`crate::ParamSignature`].
    ///
    /// The withdrawal is `ParamSignature::Withdrawn`, reached only through
    /// `withdraw()`, with no operation leading out and no parameter list attached.
    /// Both halves used to be prose: a `params_withdrawn: bool` beside an
    /// `Option<Vec<Ty>>`, whose "set by any contributing body … and NEVER CLEARED"
    /// was established by grepping every assignment in this 13,600-line module,
    /// and whose incoherent combination (withdrawn AND signed) was kept out by
    /// three `param_tys_poisoned` membership guards over in `lib.rs`. rustc
    /// carries both now: `= false` has no field to name, and the pair has no
    /// fourth state.
    ///
    /// STILL DISTINCT from `params_conflict`, which means two bodies DISAGREED
    /// about the parameters rather than one of them declining to state any — and
    /// which is deliberately left a separate `bool`, so that a row that
    /// contradicted first and was withdrawn later still counts in BOTH census
    /// buckets exactly as before.
    params: crate::ParamSignature,
    params_conflict: bool,
    abi: crate::calling_convention::FunctionAbi,
    definition: Option<crate::lineage::DefinitionIdentity>,
    concrete_key: Option<crate::lineage::ConcreteCalleeKey>,
    /// `Some` exactly for a local-unlowered declaration, and matched against the Clean-origin
    /// emitted row before any edge can be re-pointed.
    local_def_index: Option<u32>,
    signature: DeclSigState,
    /// Trust (WS5.2): the link-time symbol this row is NAMED by (`Function.name`) and the real
    /// producer it is stamped with. A checked fact like `name`/ABI: two observations of one row
    /// that disagree about it poison the row rather than pick a writer.
    link: CalleeLink,
}

#[derive(Clone, Debug)]
enum DeclSigState {
    /// No reified FnDef has supplied an exact signature. Direct calls are neutral observations.
    Unknown,
    Exact(FuncTy),
    /// Sticky contradiction between exact FnDef observations for one concrete key. A later exact
    /// observation must never resurrect this row.
    Conflict,
}

/// Trust (v41 `RustAbiVararg`): one appended declaration that ended assembly
/// carrying the UNKNOWN-signature encoding (`CallingConv::Rust` + `is_vararg`),
/// with what the producer knows about WHY.
///
/// Recorded at append and refused at finalization rather than refused on the
/// spot, because assembly is not the last pass that can sign a row: the
/// Clean-origin join gives a declaration its appended definition's own typed
/// signature, and a refusal minted before that ran would be a false statement
/// about the module that is actually emitted. `id` is therefore the whole
/// linkage — the refusal re-reads the FINAL module through it.
#[derive(Clone, Debug)]
struct UnsignableDeclaration {
    /// Dense id of the declaration row, stable from append to finalization.
    id: FuncId,
    /// Was this row minted for a CONCRETE GENERIC instance? That is a different
    /// cause from "the callee's parameters are outside the recordable fragment",
    /// and the two need different fix options.
    has_generic_args: bool,
    /// The instance's generic arguments as rustc spells them (`[u32]`), when
    /// they are exactly renderable. See `ConcreteCalleeKey::render_generic_args`.
    instance_args: Option<String>,
    /// Trust (owner call 2026-09-17(b)): the declaration's exact same-compilation source
    /// `DefIndex`, `Some` exactly for a `local-unlowered` row (`DeclRecord::local_def_index`).
    ///
    /// Carried because it is the ONLY thing that distinguishes a row the Clean-origin join may
    /// still sign from one nothing later can. `link_clean_origin_edges` matches a declaration to
    /// an appended Clean definition on exactly this field against `EmittedRow::def_index`; a row
    /// whose `local_def_index` names a Clean-origin def is therefore EXEMPT from per-body
    /// refusal, because refusing its callers would delete the very edges IR-5 exists to
    /// re-point. See [`unsignable_minting_bodies`].
    local_def_index: Option<u32>,
}

/// Choose the NAME and the DISPLAY PATH of one bodyless declaration.
///
/// Trust (WS5.2, F-087): `Function.name` is the LINK-TIME SYMBOL (trust-ir v41, SPEC §1.1).
///
/// * A row whose single ledger identity has a computable symbol is named by it — the name the
///   callee's object file exports, so a declaration and the definition in another crate finally
///   agree by symbol. Its def path moves to `display_path`. The symbol is NOT collision-renamed
///   here: two rows claiming one symbol is a producer inconsistency the per-body refusal
///   (`symbol_collision_minting_bodies`) removes before publication, and anything it cannot
///   remove reaches `DuplicateFunctionSymbol`, never a silently renamed row.
/// * A single-identity row with NO computable symbol gets the reserved, never-linkable
///   [`crate::link_symbol::unlinked_declaration_name`]; `display_path` still says what it is.
/// * The identity-less rows (`!unknown_callee_N`, `!ambiguous_callee_N`) keep their reserved
///   spellings and the injective collision fallback below; they have no def path to display.
/// * RESIDUAL (`docs/DECISION_QUEUE.md` D17-DECL-SYMBOL-1) — the one place `Function.name` is not
///   yet the link-time symbol: a declaration of a generic instance the frozen D17 instance lane
///   appends ([`CalleeLink::instance_lane_spelling`]) keeps its PRE-WS5.2 name and no display
///   path ([`instance_lane_decl_name`]), so that lane behaves as at the pin.
///
/// FuncIds remain the semantic call-edge identity, but a few downstream consumers resolve a
/// known function pointer through [`Module::function_by_name`]. That lookup is first-match, so a
/// reserved name sharing a spelling with any other row must receive an injective one instead of
/// leaving resolution order-dependent.
fn emitted_decl_name(
    module: &Module,
    decls: &[DeclRecord],
    decl: &DeclRecord,
) -> (String, Option<String>) {
    if decl.definition.is_some() && decl.link.instance_lane_spelling {
        return (instance_lane_decl_name(module, decls, decl), None);
    }
    if decl.definition.is_some() {
        let display = Some(decl.name.clone());
        return match &decl.link.symbol {
            Some(symbol) => (symbol.clone(), display),
            None => (
                crate::link_symbol::unlinked_declaration_name(&decl.key, decl.definition),
                display,
            ),
        };
    }
    let collides_with_definition = module
        .functions
        .iter()
        .any(|function| function.name == decl.name);
    let collides_with_declaration = decls.iter().any(|other| {
        other.id != decl.id
            && other.name == decl.name
            && (other.definition != decl.definition
                || other.concrete_key != decl.concrete_key
                || other.local_def_index != decl.local_def_index
                || other.key != decl.key)
    });
    if !collides_with_definition && !collides_with_declaration {
        return (decl.name.clone(), None);
    }
    (bodyless_instance_name(decl), None)
}

/// The injective `!trust_bodyless_instance::<path>::<definition>-<hex(key)>` spelling of a
/// declaration whose display path is shared — the form `instance_admission::
/// declaration_name_matches` checks in full.
///
/// `decl.key` carries class/locality plus the canonical concrete key when one exists.
/// `definition` is included separately for legacy concrete-key-less rows whose key was built
/// before stable definition identity existed. Both encodings are full-width and injective;
/// neither Debug text nor a truncated hash becomes identity.
fn bodyless_instance_name(decl: &DeclRecord) -> String {
    let definition = decl
        .definition
        .map(crate::lineage::DefinitionIdentity::symbol_suffix)
        .unwrap_or_else(|| "unknown".to_string());
    let suffix = format!("{definition}-{}", stable_text_hex(&decl.key));
    format!("!trust_bodyless_instance::{}::{suffix}", decl.name)
}

/// Trust (WS5.2 NARROWED — RESIDUAL, `docs/DECISION_QUEUE.md` D17-DECL-SYMBOL-1): the PRE-WS5.2
/// name of a declaration of a generic instance the frozen D17 instance lane appends — its display
/// path, or [`bodyless_instance_name`] when that path is shared.
///
/// THE ONE PLACE `Function.name` IS NOT YET THE LINK-TIME SYMBOL. The lane (owner ruling D17,
/// `instance_assembly.rs` + `instance_admission.rs`, BYTE-IDENTICAL in `scripts/frozen-files.txt`)
/// appends the instance body under its symbol and refuses when another row already holds that
/// name, and its relink accepts a host declaration only by display path or this collision form
/// (`instance_admission::declaration_names_instance`). A symbol-named declaration would turn both
/// into refusals; the fix that lets it carry the symbol widens a frozen file, which is the
/// owner's call, so until then this row is spelled exactly as before WS5.2.
///
/// "Shared" is the pin's test, read on the WS5.2 module: at the pin a definition was NAMED by its
/// display path, so a definition whose `display_path` is this row's path collides as well as one
/// whose name is; another declaration collides when it displays the same path under a different
/// identity (the pin's check, unchanged) or will be emitted under a symbol that spells it. Each
/// extra conjunct can only move a row from the bare path to the collision form, which the lane's
/// relink accepts too (checked in full: path, definition and concrete key).
fn instance_lane_decl_name(module: &Module, decls: &[DeclRecord], decl: &DeclRecord) -> String {
    let path = decl.name.as_str();
    let collides_with_definition = module
        .functions
        .iter()
        .any(|function| function.name == path || function.display_path.as_deref() == Some(path));
    let collides_with_declaration = decls.iter().any(|other| {
        other.id != decl.id
            && ((other.name == decl.name
                && (other.definition != decl.definition
                    || other.concrete_key != decl.concrete_key
                    || other.local_def_index != decl.local_def_index
                    || other.key != decl.key))
                || other.link.symbol.as_deref() == Some(path))
    });
    if !collides_with_definition && !collides_with_declaration {
        return decl.name.clone();
    }
    bodyless_instance_name(decl)
}

/// Append every declaration row while preserving the dense FuncId table even for contradicted
/// observations. A conflict is a fatal producer error, but SKIPPING its row is not fail-closed:
/// a later Clean-origin append would reuse the absent ID and silently retarget existing edges.
fn append_declarations(
    module: &mut Module,
    decls: &[DeclRecord],
    unsignable: &mut Vec<UnsignableDeclaration>,
) -> Vec<String> {
    report_declaration_signing_census(decls);
    let mut errors = Vec::new();
    for decl in decls {
        let conflict = decl.ret_conflict || matches!(decl.signature, DeclSigState::Conflict);
        if conflict {
            // Trust (wave-RETSPLIT): NAME the contradicted fact. The message used to say only
            // that "observations" conflicted, and the two sources are retired by unrelated work
            // — a result-type contradiction is a `Ty` SPELLING divergence between two bodies
            // (now split rather than poisoned, so this half is the residual floor), while a
            // signature contradiction is two exact `Constant::FnDef` observations, or a name /
            // ABI / exact-source-identity mismatch, for one concrete key. Diagnosing which
            // otherwise needs a compiler rebuild.
            let which = match (decl.ret_conflict, &decl.signature) {
                (true, DeclSigState::Conflict) => "result type and signature",
                (true, _) => "result type",
                (false, _) => "signature",
            };
            errors.push(format!(
                "conflicting bodyless declaration observations ({which}) for FuncId {} key {:?} name {:?}",
                decl.id.index(),
                decl.key,
                decl.name,
            ));
        }

        // A conflict placeholder asserts no signature fact. It exists only to occupy the exact
        // ID all rewritten edges already name; finalization aborts on `errors` before any consumer
        // or join can observe it. Non-conflicting rows retain their exact/unknown policy.
        //
        // Trust (v41): spelled `is_vararg: false`, NOT `true`. The two are equally
        // unobservable here — the module never leaves finalization — but
        // `CallingConv::Rust` with `is_vararg: true` is exactly the
        // unknown-signature smuggling pattern trust-ir v41 refuses
        // (`validate_rust_abi_is_not_variadic`), and a placeholder is the last
        // place that spelling should survive as a habit. `params: []` +
        // `is_vararg: false` is a positive claim of "takes no arguments", which
        // is equally untrue of the contradicted callee — but this row is
        // guaranteed dead, and the honest reading of a dead row is the one the
        // validator can still check rather than the one it cannot.
        let exact_foreign = checked_foreign_declaration_signature(decl);
        if let Err(why) = &exact_foreign {
            errors.push(format!("bodyless declaration FuncId {}: {why}", decl.id.index()));
        }
        let sig = if conflict || exact_foreign.is_err() {
            intern_func_ty(
                module,
                FuncTy { params: Vec::new(), returns: Vec::new(), is_vararg: false, abi: None },
            )
        } else if let Ok(Some(signature)) = exact_foreign {
            intern_func_ty(module, signature)
        } else {
            match &decl.signature {
                DeclSigState::Exact(ft) => intern_func_ty(module, ft.clone()),
                // Trust (v41 `RustAbiVararg`): a RECOVERED parameter list signs the
                // declaration; `is_vararg` is then `false` and the validator's arity
                // test and arg/param zip both become real checks instead of the
                // vacuous `actual < 0` the placeholder produced.
                //
                // An UNSIGNABLE declaration keeps the old spelling for now — the
                // residue is 82.6% of unknown-signature rows (measured: 403
                // unknown, 70 signed) and every one of them is still refused by
                // v41. Closing that residue means widening the type reader past
                // the table-free scalar fragment and then repairing the three
                // argument-dropping lanes, which is the rest of the campaign in
                // `reports/2026-09-14-rust-abi-vararg-producer-half.md`. What
                // this arm does today is strictly fewer refusals, never more.
                DeclSigState::Unknown => match decl.params.signature() {
                    Some(params) => intern_func_ty(
                        module,
                        FuncTy {
                            params: params.clone(),
                            returns: decl.ret.clone().into_iter().collect(),
                            is_vararg: false,
                            abi: None,
                        },
                    ),
                    None => intern_func_ty(
                        module,
                        FuncTy {
                            params: Vec::new(),
                            returns: decl.ret.clone().into_iter().collect(),
                            is_vararg: true,
                            abi: None,
                        },
                    ),
                },
                DeclSigState::Conflict => unreachable!("handled by conflict arm"),
            }
        };
        // Trust (trust-ir D1b): a full signature table is a fatal assembly error, like a
        // conflict; finalization aborts on `errors` before anything reads the module, so the
        // skipped row's id is never observed.
        let sig = match sig {
            Ok(sig) => sig,
            Err(refusal) => {
                errors.push(format!(
                    "bodyless declaration FuncId {} could not be signed: {refusal}",
                    decl.id.index(),
                ));
                continue;
            }
        };
        let (emitted_name, display_path) = if conflict {
            (
                format!(
                    "!trust_conflicting_declaration::{}::{}",
                    decl.id.index(),
                    stable_text_hex(&decl.key),
                ),
                None,
            )
        } else {
            emitted_decl_name(module, decls, decl)
        };
        // Trust (v41 `RustAbiVararg`): RECORD every Rust-ABI row that still carries the
        // unknown-signature encoding. This is the population the validator refuses, read
        // back off the interned signature rather than re-derived from the match above, so
        // a future arm cannot quietly leave the spelling behind. It is only a record:
        // finalization re-checks the FINAL module (the Clean-origin join signs some of
        // these) and refuses the survivors by name. The conflict placeholder is spelled
        // `is_vararg: false` and so never enters here.
        if decl.abi.is_rust_convention()
            && module
                .func_types
                .get(sig.index() as usize)
                .is_some_and(|ft| ft.is_vararg)
        {
            unsignable.push(UnsignableDeclaration {
                id: decl.id,
                has_generic_args: decl
                    .concrete_key
                    .as_ref()
                    .is_some_and(crate::lineage::ConcreteCalleeKey::has_generic_args),
                instance_args: decl
                    .concrete_key
                    .as_ref()
                    .and_then(crate::lineage::ConcreteCalleeKey::render_generic_args),
                local_def_index: decl.local_def_index,
            });
        }
        // Trust (WS5.2): the callee's REAL producer — `Clean` for a Clean-origin def (local, or
        // a dependency's `trust_clean_origin_exports`), `TRust` for this crate's own Rust item,
        // `None` (unrecorded) for everything else. Every declaration used to be stamped `TRust`,
        // which was false for a Clean export and a guess for any other dependency.
        let mut function = Function::new(decl.id, emitted_name, sig, BlockId::new(0));
        function.producer = decl.link.producer.clone();
        function.display_path = display_path;
        function.linkage = Linkage::External;
        match decl.abi.calling_conv() {
            Ok(convention) => function.calling_conv = convention,
            Err(why) => errors.push(format!("bodyless declaration FuncId {}: {why}", decl.id.index())),
        }
        if let Err(refusal) = module.try_add_function(function) {
            errors.push(format!("bodyless declaration FuncId {}: {refusal}", decl.id.index()));
        }
    }
    errors
}

/// A recorded source prototype refines only a coherent observation. It must
/// never resurrect a withdrawn/contradicted argument list or overwrite an
/// independently reified FnDef signature with different carriers.
fn checked_foreign_declaration_signature(decl: &DeclRecord) -> Result<Option<FuncTy>, String> {
    let Some(source) = &decl.link.foreign_signature else { return Ok(None); };
    if decl.params.is_withdrawn() || decl.params_conflict || decl.ret_conflict
        || matches!(decl.signature, DeclSigState::Conflict)
    {
        return Err("original foreign prototype contradicts a withdrawn/conflicting call observation".into());
    }
    if decl.params.signature().is_some_and(|params| *params != source.params)
        || decl.ret.as_ref().is_some_and(|ret| source.returns.as_slice() != [ret.clone()])
    {
        return Err("original foreign prototype disagrees with recorded call types".into());
    }
    crate::foreign_signature::check_observation(source, decl.abi, &decl.params,
        decl.ret.as_ref(), decl.ret_conflict, true).map_err(str::to_string)?;
    if let DeclSigState::Exact(observed) = &decl.signature {
        if observed.params != source.params || observed.returns != source.returns
            || observed.is_vararg != source.is_vararg
            || observed.abi.as_ref().is_some_and(|abi| Some(abi) != source.abi.as_ref())
        {
            return Err("original foreign prototype disagrees with reified FnDef signature".into());
        }
        // A reified function pointer has its own callable type. This change
        // adds no physical adapter for that type; preserve the existing
        // Rust/plain-C nonvariadic profile instead of attaching a descriptor
        // solely to its target and contradicting the pointer's type identity.
        if observed.abi.is_none() {
            return Ok(None);
        }
    }
    Ok(Some(source.clone()))
}

/// Trust (v41 `RustAbiVararg`, v7/D3): WHY this declaration could not be signed.
///
/// Extracted so the CRATE-level refusal ([`unsignable_declaration_refusals`]) and the PER-BODY
/// refusal ([`unsignable_minting_bodies`]) state one cause, not two paraphrases of it. A reader
/// comparing a coverage row against a compiler error must see the same sentence in both.
fn unsignable_declaration_cause(row: &UnsignableDeclaration) -> String {
    if row.has_generic_args {
        let carried = match &row.instance_args {
            Some(args) => format!("the instance carries generic arguments `{args}`"),
            None => "the instance carries generic arguments".to_string(),
        };
        format!(
            "{carried}, but crate assembly keys every body on its `DefIndex` and lowers \
             the body pre-monomorphization, so this instance has neither a lowered body \
             to link nor an instantiated signature to record"
        )
    } else {
        "the callee's declared parameter types are outside the fragment this producer can \
         record table-free (scalars, thin pointers, `&str`, shared `&[scalar]`, tuples of \
         those, or an aggregate this body already registered), or its def kind has no \
         `tcx.fn_sig` at all (a closure, a coroutine, a ctor, a virtual `dyn` entry)"
            .to_string()
    }
}

/// What the outlawed encoding would mean, and why the producer will not write it. Shared prose:
/// see [`unsignable_declaration_cause`].
const UNSIGNABLE_DECLARATION_ENCODING: &str =
    "Emitting it as `params: []` + `is_vararg: true` is the unknown-signature encoding trust-ir \
     v41 refuses (`validate_rust_abi_is_not_variadic`) — that combination makes the arity test \
     `actual < 0` and the arg/param zip run zero times, so every call on the edge would be \
     vacuously well-typed — so this producer states nothing instead of stating something false.";

/// Trust (owner call 2026-09-17(b)): the coverage-row TAG every per-body unsignable-edge
/// refusal starts with. It is read back as data — by `run_seam_differentials`, to keep the
/// pending-const skip population it does not belong to clean — so it is a constant, not a
/// spelling repeated at two sites.
const UNSIGNABLE_BODY_REASON_TAG: &str = "UnsignableRustAbiDeclaration(";

/// The v7/D3 OPTIONS. Shared prose: see [`unsignable_declaration_cause`].
const UNSIGNABLE_DECLARATION_OPTIONS: &str =
    "Options: (1) `-Ztrust-verify=off` — the only lane where `-Ztrust-ir-lower` is a choice \
     (verification ON runs this producer unconditionally, `trust_ir_lower_enabled_by_flags`); \
     with it off and neither `-Ztrust-ir-lower` nor `-Ztrust-cg-frontend=trust-ir` given, \
     monomorphization precedes codegen and no bodyless Rust declaration is minted for this call; \
     (2) give the callee a signature recordable at this identity — a non-generic callee, or \
     parameters this producer can spell table-free (scalars, thin pointers, `&str`, tuples of \
     those, or an aggregate this body already registered); (3) key crate-assembly body records \
     on the concrete INSTANCE, so a generic callee links to its own instantiated body and \
     signature instead of to a declaration";

/// Trust (v41 `RustAbiVararg`): the recorded rows that STILL carry the unknown-signature
/// encoding in `module`, paired with the emitted function they name.
///
/// RE-CHECKED, never replayed. A later pass can sign a row (the Clean-origin join does exactly
/// that for a declaration its appended definition shadows), and a statement about a declaration
/// that is signed in the emitted module would be a false statement about that module. This is
/// the single predicate both the per-body refusal and the crate-level refusal read, so the two
/// can never disagree about which rows are still unsignable.
fn surviving_unsignable_declarations<'a>(
    module: &'a Module,
    recorded: &'a [UnsignableDeclaration],
) -> Vec<(&'a UnsignableDeclaration, &'a Function)> {
    let mut survivors = Vec::new();
    for row in recorded {
        let Some(function) = module.functions.iter().find(|f| f.id == row.id) else {
            continue;
        };
        if !function.is_declaration()
            || !matches!(function.calling_conv, trust_ir::CallingConv::Rust | trust_ir::CallingConv::RustCold)
        {
            continue;
        }
        if !module
            .func_types
            .get(function.ty.index() as usize)
            .is_some_and(|ft| ft.is_vararg)
        {
            continue;
        }
        survivors.push((row, function));
    }
    survivors
}

/// Trust (owner call 2026-09-17(b)): does `function` name `id` through any edge shape a SPLICED
/// body can carry — and can this walk answer at all?
///
/// `splice_ok` is what makes the answer exact. It admits exactly the instruction variants
/// [`inst_embedded_tys`] models, refuses `Inst::Invoke` by name, requires every non-`FnDef`
/// `Inst::Const` payload and every `Inst::Switch` case value to be [`constant_funcid_free`], and
/// gives `Inst::CallIndirect` no `FuncId` at all. So in a spliced body the ONLY `FuncId`
/// positions are `Inst::Call { callee }` and `Inst::Const { value: Constant::FnDef(_) }` — the
/// same two shapes `clean_origin_join::function_references` rewrites, and the same two pass 2
/// mints declarations from.
///
/// It is still written as an ALLOW-LIST with an `Unmodeled` answer rather than a `_ => false`
/// deny-list: a future `Inst` variant carrying a `FuncId` must make this walk say "I cannot
/// rule it out" (the caller then refuses the body — strictly more conservative) instead of
/// silently reporting "no edge" and leaving the declaration in the emitted module.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum DeclarationEdge {
    /// No instruction in the body names the declaration.
    Absent,
    /// At least one `Inst::Call` callee or reified `Constant::FnDef` names it.
    Named,
    /// The body carries an instruction shape this walk does not model, so the absence of a
    /// named edge is not evidence of absence.
    Unmodeled,
}

/// Every `FuncId` one instruction names, or `None` for a shape this walk does not model.
/// Allow-list; see [`DeclarationEdge`] for why the unmodeled answer is not `false`.
fn inst_referenced_funcs(inst: &Inst) -> Option<Vec<FuncId>> {
    Some(match inst {
        Inst::Call { callee, .. } => vec![*callee],
        Inst::MakeClosure { func, .. } => vec![*func],
        Inst::Const { value, .. } => match value {
            Constant::FnDef(fid) => vec![*fid],
            // `splice_ok` proved every other payload `FuncId`-free; re-check rather than assume.
            other if constant_funcid_free(other) => Vec::new(),
            _ => return None,
        },
        Inst::Switch { cases, .. } => {
            if cases.iter().all(|case| constant_funcid_free(&case.value)) {
                Vec::new()
            } else {
                return None;
            }
        }
        // The rest of the set `inst_embedded_tys` models — none of them carries a `FuncId`
        // (`CallIndirect` calls through a VALUE; `Br`/`CondBr` carry `BlockId`s; `GlobalAddr`
        // carries a `GlobalId`).
        Inst::BinOp { .. }
        | Inst::UnOp { .. }
        | Inst::Overflow { .. }
        | Inst::ICmp { .. }
        | Inst::FCmp { .. }
        | Inst::Load { .. }
        | Inst::Store { .. }
        | Inst::Alloca { .. }
        | Inst::ExtractField { .. }
        | Inst::InsertField { .. }
        | Inst::ExtractElement { .. }
        | Inst::InsertElement { .. }
        // v50 `[value; n]`: a type and a register, no `FuncId`.
        | Inst::ArraySplat { .. }
        | Inst::Undef { .. }
        | Inst::Copy { .. }
        | Inst::Select { .. }
        | Inst::Cast { .. }
        | Inst::GEP { .. }
        | Inst::PtrData { .. }
        | Inst::PtrMetadata { .. }
        | Inst::PtrFromParts { .. }
        | Inst::Br { .. }
        | Inst::CondBr { .. }
        | Inst::CallIndirect { .. }
        | Inst::Return { .. }
        | Inst::Assume { .. }
        | Inst::Assert { .. }
        | Inst::Unreachable
        | Inst::GlobalAddr { .. }
        | Inst::NullPtr
        // Trust (step 2 increment 4b, owner ruling D18 OD-1): a v47 drop names a type and a
        // pointer register, no `FuncId` (it becomes a call only when increment 4c resolves it to
        // drop glue at the codegen seam). In lockstep with `inst_embedded_tys`, which admits it.
        | Inst::Drop { .. } => Vec::new(),
        // `Inst::Invoke`/`Inst::SeqMap` carry a `FuncId` this producer never emits (`splice_ok`
        // refuses both), and anything added later is unknown.
        _ => return None,
    })
}

/// See [`DeclarationEdge`].
fn declaration_edge(function: &Function, id: FuncId) -> DeclarationEdge {
    let mut edge = DeclarationEdge::Absent;
    for node in function.blocks.iter().flat_map(|block| &block.body) {
        match inst_referenced_funcs(&node.inst) {
            Some(funcs) => {
                if funcs.contains(&id) {
                    return DeclarationEdge::Named;
                }
            }
            None => edge = DeclarationEdge::Unmodeled,
        }
    }
    edge
}

/// Trust (owner call 2026-09-17(b)): the per-body reason string. Same cause, same encoding
/// sentence, same options as the crate-level refusal — see [`unsignable_declaration_cause`].
fn unsignable_minting_body_reason(
    callee: &str,
    row: &UnsignableDeclaration,
    certain: bool,
) -> String {
    let edge = if certain {
        format!("this body mints a call edge to bodyless declaration `{callee}`")
    } else {
        format!(
            "this body carries an instruction shape the edge scan does not model, so a call \
             edge to bodyless declaration `{callee}` cannot be ruled out"
        )
    };
    format!(
        "{UNSIGNABLE_BODY_REASON_TAG}{callee}): {edge}, which declares the Rust calling \
         convention and which this producer has no signature to give: {}. {} The BODY is \
         refused — lowered for coverage, never spliced — so the rest of the crate module is \
         assembled and validated instead of the whole crate failing on this one edge. {}",
        unsignable_declaration_cause(row),
        UNSIGNABLE_DECLARATION_ENCODING,
        UNSIGNABLE_DECLARATION_OPTIONS,
    )
}

/// Trust (owner call 2026-09-17(b), report `2026-09-14-rust-abi-vararg-producer-half.md` move
/// (b)): ATTRIBUTE every surviving unsignable Rust-ABI declaration to the bodies that mint an
/// edge to it, so the PRODUCER can refuse those bodies instead of refusing the whole crate.
///
/// WHAT REPLACED WHAT. Until this landed, one unsignable edge anywhere refused the entire
/// module at finalization, so a crate carrying it produced nothing at all. The owner chose
/// option (b) of that report: trade the coverage those bodies carried for honest per-body
/// refusals and a module that still assembles and validates.
///
/// THE ATTRIBUTION IS READ OFF THE LOWERED IR, not threaded through the lowering walk, and that
/// is exact here: pass 2 mints a declaration only while rewriting some spliced body's own call
/// edge, and it writes the minted `FuncId` into that body's function. So the bodies naming the
/// declaration in the assembled module ARE the bodies that minted it. `assigned` inverts a
/// spliced function's dense `FuncId` back to its `DefIndex` (`assigned[i].1 == FuncId(i)`).
///
/// THE CLEAN-ORIGIN EXEMPTION, and why it is not a hole. `link_clean_origin_edges` signs a
/// declaration exactly when the appended Clean definition FULLY SHADOWS it — every edge
/// re-pointed, nothing left naming it. Refusing the bodies holding those edges would delete the
/// edges IR-5 exists to re-point, which is a capability loss, so a row whose `local_def_index`
/// names a Clean-origin def the join may emit is left alone. That set is a SUPERSET of what the
/// join actually signs (the join additionally needs matching calling conventions, unique source
/// identity and a clean per-edge repoint), so the exemption can only preserve today's behaviour
/// — the crate-level refusal below, unchanged — never admit a row the validator would refuse.
///
/// Returns `(def_index, reason)` pairs, deterministically ordered and deduplicated. A survivor
/// with NO attributable body is deliberately absent from the result: it is a producer defect,
/// not a user-facing refusal, and [`unsignable_declaration_refusals`] keeps failing the crate
/// on it and says which case it is.
fn unsignable_minting_bodies(
    assembled: &Assembled,
    clean_origin_local_defs: &std::collections::BTreeSet<u32>,
) -> Vec<(u32, String)> {
    // The survivors this pass may refuse for, indexed by their dense FuncId. Built first so the
    // module is walked ONCE per round rather than once per survivor: a crate can carry hundreds
    // of unsignable rows and thousands of spliced bodies, and the quadratic shape of the
    // obvious loop is a real cost on exactly the crates this change exists for.
    let mut survivors: Vec<(u32, &UnsignableDeclaration, &str)> = Vec::new();
    for (row, declaration) in
        surviving_unsignable_declarations(&assembled.module, &assembled.unsignable_declarations)
    {
        if row.local_def_index.is_some_and(|def| clean_origin_local_defs.contains(&def)) {
            continue;
        }
        // Trust (WS5.2): the reader is told the callee's DEF PATH — its display path — since
        // the declaration's name is a link-time symbol (or a reserved unlinked spelling).
        survivors.push((
            row.id.index(),
            row,
            declaration.display_path.as_deref().unwrap_or(declaration.name.as_str()),
        ));
    }
    if survivors.is_empty() {
        return Vec::new();
    }
    let survivor_ids: std::collections::BTreeSet<u32> =
        survivors.iter().map(|(id, _, _)| *id).collect();

    let mut refusals: Vec<(u32, String)> = Vec::new();
    for function in &assembled.module.functions {
        // Only a PASS-1 spliced body has an `assigned` entry, and `assigned[i].1 == FuncId(i)`
        // is the assembler's own invariant — checked here, never assumed, so an appended row
        // can never be mis-attributed to some body's `DefIndex`.
        let Some(&(def_index, func_id)) = assembled.assigned.get(function.id.index() as usize)
        else {
            continue;
        };
        if func_id != function.id {
            continue;
        }
        let mut named: std::collections::BTreeSet<u32> = std::collections::BTreeSet::new();
        let mut unmodelled = false;
        for node in function.blocks.iter().flat_map(|block| &block.body) {
            match inst_referenced_funcs(&node.inst) {
                Some(funcs) => named.extend(
                    funcs.into_iter().map(|f| f.index()).filter(|id| survivor_ids.contains(id)),
                ),
                // Not "no edge": see `DeclarationEdge`. The body cannot be cleared of ANY
                // survivor, so it is refused for all of them — strictly more conservative.
                None => unmodelled = true,
            }
        }
        for &(id, row, name) in &survivors {
            if !unmodelled && !named.contains(&id) {
                continue;
            }
            refusals.push((
                def_index,
                unsignable_minting_body_reason(name, row, named.contains(&id)),
            ));
        }
    }
    refusals.sort();
    refusals.dedup();
    refusals
}

/// Trust (v41 `RustAbiVararg`, v7/D3): refuse — by name, with the cause and the
/// fix options — every bodyless Rust-ABI declaration the producer could not sign
/// AND could not remove by refusing the body that minted it.
///
/// WHY A REFUSAL AND NOT A SIGNATURE. In v41 a `CallingConv::Rust` declaration
/// can honestly be SIGNED or CONTRADICTED, and `FuncTy` has no third spelling:
/// `params: [] + is_vararg: true` is not an under-specification but an
/// off-switch, and `Ty::Error` is deliberately un-emittable, which is the format
/// saying its answer to "unknown" is REFUSE rather than ENCODE. Where a
/// signature CAN be derived the producer derives it — `recover_callee_param_tys`
/// reads a non-local callee's `tcx.fn_sig`, instantiated at its resolved
/// instance, and the Clean-origin join gives a shadowed declaration its appended
/// definition's own typed signature. What reaches here is the residue, and for
/// it the only honest move left is to say so.
///
/// WHY HERE. This runs on the FINAL module, immediately before
/// `final_module_validation_errors`, so (a) every pass that can still sign a row
/// has run, and (b) the CAUSE is reported ahead of the validator's symptom
/// instead of behind it. Both are kept: a producer defect and the validation
/// result it produces are two facts, and hiding the second would make the
/// refusal unfalsifiable. The population is exactly `RustAbiVararg`'s, so this
/// can only re-describe an already-fatal module, never fail a passing one.
///
/// WHAT STILL REACHES IT, since the owner call of 2026-09-17 made the ordinary case a per-body
/// refusal ([`unsignable_minting_bodies`]). Exactly three, and the message NAMES which:
///  1. a row whose `local_def_index` names a Clean-origin def, left for the join to sign,
///     which the join then did not fully shadow — the disposition the exemption buys, and the
///     `linked:` disclosure rows carry the per-edge refusal that left it referenced;
///  2. a row still NAMED by a body in the emitted module — a producer defect, because the
///     per-body refusal should have removed that body before assembly;
///  3. a row nothing names — a dead declaration no pass signed or retired, also a producer
///     defect.
/// Cases 2 and 3 are not user-facing refusals and say so.
fn unsignable_declaration_refusals(
    module: &Module,
    recorded: &[UnsignableDeclaration],
    clean_origin_local_defs: &std::collections::BTreeSet<u32>,
) -> Vec<String> {
    let mut refusals = Vec::new();
    for (row, function) in surviving_unsignable_declarations(module, recorded) {
        let referencing = module
            .functions
            .iter()
            .filter(|f| !f.is_declaration() && declaration_edge(f, row.id) != DeclarationEdge::Absent)
            .count();
        let disposition = if row
            .local_def_index
            .is_some_and(|def| clean_origin_local_defs.contains(&def))
        {
            format!(
                " This row names a Clean-origin definition in this crate (DefIndex {}), so the \
                 bodies that call it were deliberately NOT refused: the IR-5 Clean-origin link \
                 exists to re-point exactly those edges onto the appended definition, and \
                 refusing their bodies would delete the edges it needs. The join did not fully \
                 shadow this declaration, so the row reached the validator unsigned — read the \
                 `linked:` rows of the Clean-origin disclosure for the per-edge refusal that \
                 left it referenced.",
                row.local_def_index.unwrap_or_default(),
            )
        } else if referencing > 0 {
            format!(
                " PRODUCER DEFECT, not a user-facing refusal: {referencing} function(s) in the \
                 emitted module still name this declaration, so the per-body refusal that \
                 removes such bodies before assembly did not identify them. Report this."
            )
        } else {
            " PRODUCER DEFECT, not a user-facing refusal: no function in the emitted module \
             names this row, so there was no body to refuse — the producer minted a declaration \
             the module does not need and no later pass signed or retired it. Report this."
                .to_string()
        };
        refusals.push(format!(
            "trust-ir producer refusal [unsignable-rust-abi-declaration]: bodyless declaration \
             `{}` declares the Rust calling convention and this producer has no signature to \
             give it: {}. {} {}{disposition}",
            // Trust (WS5.2): the def path the user wrote, not the link-time symbol.
            function.display_path.as_deref().unwrap_or(function.name.as_str()),
            unsignable_declaration_cause(row),
            UNSIGNABLE_DECLARATION_ENCODING,
            UNSIGNABLE_DECLARATION_OPTIONS,
        ));
    }
    refusals
}

/// Non-admitting source facts, constructed only by this canonical finalizer.
/// The handoff checks their complete declaration image before retaining them.
pub(crate) struct CodegenDeclarationRecord {
    origin: std::sync::Arc<Module>,
    key: String,
    definition: Option<crate::lineage::DefinitionIdentity>,
    concrete_key: Option<crate::lineage::ConcreteCalleeKey>,
    function: Function,
    signature: FuncTy,
    foreign_source: Option<crate::foreign_signature::ForeignSource>,
}

impl CodegenDeclarationRecord {
    pub(crate) fn origin(&self) -> &std::sync::Arc<Module> { &self.origin }
    pub(crate) fn key(&self) -> &str { &self.key }
    pub(crate) fn definition(&self) -> Option<crate::lineage::DefinitionIdentity> { self.definition }
    pub(crate) fn concrete_key(&self) -> Option<&crate::lineage::ConcreteCalleeKey> { self.concrete_key.as_ref() }
    pub(crate) fn function(&self) -> &Function { &self.function }
    pub(crate) fn signature(&self) -> &FuncTy { &self.signature }
    pub(crate) fn foreign_source(&self) -> Option<&crate::foreign_signature::ForeignSource> {
        self.foreign_source.as_ref()
    }
}

fn retain_codegen_declarations(
    module: &Module,
    declarations: &[DeclRecord],
) -> Result<Vec<CodegenDeclarationRecord>, String> {
    let origin = std::sync::Arc::new(module.clone());
    declarations.iter().map(|decl| {
        let function = module.function_by_id(decl.id)
            .filter(|f| f.is_declaration())
            .ok_or_else(|| format!("retained declaration FuncId({}) is absent or a body", decl.id.index()))?;
        let signature = module.func_type(function.ty)
            .ok_or_else(|| format!("retained declaration FuncId({}) has no signature", decl.id.index()))?;
        Ok(CodegenDeclarationRecord {
            origin: std::sync::Arc::clone(&origin),
            key: decl.key.clone(),
            definition: decl.definition,
            concrete_key: decl.concrete_key.clone(),
            function: function.clone(),
            signature: signature.clone(),
            foreign_source: decl.link.foreign_source.clone(),
        })
    }).collect()
}

struct Assembled {
    module: Module,
    /// Contradictory declaration observations detected while materializing the dense function
    /// table. Every conflicting row is still emitted as a reserved placeholder so its FuncId can
    /// never be reused by a later append; finalization consumes these errors before any join.
    errors: Vec<String>,
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
    /// Trust (B8 step 1): the module's bodyless declarations in mint order — the same key/id
    /// identities [`decl_id`] interned, plus the exact local source `DefIndex` where applicable,
    /// carried past assembly instead of being dropped with the local `decls` vector.
    ///
    /// This has to be carried because it cannot be re-derived at the point it is needed.
    /// [`run_seam_differentials`] receives `&[BodyRecord] + &Assembled`, and the `FuncId` it holds
    /// at the declaration gate is a REWRITTEN declaration id — it is not any `CalleeRef::func_id`
    /// and cannot be mapped back to one: the ledger is keyed on the body-local PRE-rewrite id,
    /// and one declaration deliberately coalesces an arbitrary number of those across every body
    /// in the crate (that coalescing is [`decl_id`]'s entire purpose). Re-deriving the class at
    /// the gate is therefore not merely expensive, it is not well-defined; carrying it is.
    decl_keys: Vec<crate::clean_origin_join::DeclarationLinkIdentity>,
    /// Actual typed ordinary callee identity plus its complete declaration image.
    /// Read-only projection only; retaining a row never admits a body.
    codegen_declarations: Vec<CodegenDeclarationRecord>,
    /// Trust (v41 `RustAbiVararg`): the declarations assembly could not sign.
    /// Carried — not refused here — because the Clean-origin join still signs
    /// some of them; see [`unsignable_declaration_refusals`].
    unsignable_declarations: Vec<UnsignableDeclaration>,
}

/// Trust: the coverage/marker spelling of a body's kind (see `BodyRecord::kind`).
fn kind_str(kind: BodyKind) -> &'static str {
    match kind {
        BodyKind::Fn => "fn",
        BodyKind::ConstInit => "const-init",
        BodyKind::StaticInit => "static-init",
    }
}

fn definition_base_name(record: &BodyRecord) -> String {
    match record.kind {
        BodyKind::Fn => record.def_path.clone(),
        BodyKind::ConstInit => format!("{}::{{const-init}}", record.def_path),
        BodyKind::StaticInit => format!("{}::{{static-init}}", record.def_path),
    }
}


/// Trust (2026-09-27): WHY a body that LOWERED is not a function of the assembled crate module.
///
/// Every refusal between "lowered clean" and "spliced" is one of these, and it reaches the body's
/// coverage row as `"splice_refusal"`. Before this type, pass 1 dropped a lowered body through
/// `splice_ok`'s `return false`s, `prepare_body_tables`' `None`s, the remap certificate, the
/// three fixpoint predicates and the re-assembly veto, and every one of them reached the artifact
/// as the same bare `"lowered": true, "spliced": false` — a body lost with nothing saying which
/// wall it hit. MEASURED 2026-09-27 on origin/main `5ab8dcccfc`: `thread_local! { static C:
/// RefCell<Option<(u64, u64)>> }` (and `Cell<Option<fn(u32) -> u32>>`, with no tuple anywhere)
/// lost `__rust_std_internal_init_fn` that way — R2 read the WITHHELD layout of
/// `UnsafeCell<Option<..>>` as an identity spelling — and the crystal lane's missing
/// `clean_kernel` bodies carried no diagnostic at all.
///
/// THE INVARIANT, enforced where the row is rendered (`coverage_json`): a lowered row that is not
/// spliced names exactly one refusal; a spliced row and an unlowered row name none (an unlowered
/// row's reasons are its `unsupported` tags, which already say why). A new drop path that forgets
/// to name itself fails the artifact rather than publishing a silent loss.
///
/// NOT a strict-mode diagnostic: `-Ztrust-ir-lower=strict` reports bodies the producer could not
/// LOWER (`RefusedBody`); a splice refusal is a coverage-only skip of a body that did lower, and
/// promoting every one of them to a compile error is a policy decision this type does not make.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SpliceRefusal {
    /// `unsupported` is non-empty: never reaches a row (an unlowered row names no refusal).
    NotLowered,
    /// `BodyRecord::generated_ungated`.
    GeneratedUngated,
    /// `BodyRecord::symbolic` — value-less symbolic carriers.
    Symbolic,
    /// `BodyRecord::union_lane`.
    UnionLane,
    /// `BodyRecord::storage_value_traffic`.
    StorageValueTraffic,
    /// `BodyRecord::enum_param_lane`.
    EnumParamLane,
    /// `BodyRecord::zst_closure_arg`.
    ZstClosureArg,
    /// `BodyRecord::coroutine_frame_ptr`.
    CoroutineFramePtr,
    /// `BodyRecord::fnptr_adapter`.
    FnptrAdapter,
    ClosureAdapter,
    /// No function or no signature in the record.
    NoFunctionBody,
    /// The enum table is not positional, or a variant field does not resolve.
    EnumTable,
    /// The struct table is not positional / nested-first, or a field is not spliceable.
    StructTable,
    /// A types-table entry is not spliceable.
    TypesTable,
    /// A closure type's signature or capture is not table-free.
    ClosureTable,
    /// A global outside `global_spliceable`'s allow-list.
    GlobalShape,
    /// A signature type is not spliceable.
    SignatureType,
    /// A block parameter type is not spliceable.
    BlockParamType,
    /// An instruction-embedded type is not spliceable.
    InstructionType,
    /// An instruction variant `inst_embedded_tys` does not model.
    UnmodeledInstruction,
    /// An `Inst::Invoke` (never emitted; not rewritten by pass 2).
    Invoke,
    /// An indirect call's signature id does not resolve (`body_sig_ok`).
    IndirectCallSignature,
    /// A reified fn-pointer constant fails its sig / ledger / target-signature checks.
    FnPtrConstant,
    /// A non-`FnDef` constant carries a `FuncId`.
    ConstantFuncId,
    /// A `Switch` case constant carries a `FuncId`.
    SwitchFuncId,
    /// `prepare_body_tables`: `static_globals::validate_origins` refused the record.
    StaticGlobalOrigin,
    /// `prepare_body_tables`: the enum/struct DAG has a cycle or an out-of-range reference.
    DefTableGraph,
    /// `prepare_body_tables`: an enum/struct def did not remap.
    DefTableRemap,
    /// `prepare_body_tables`: a types-table entry did not remap.
    TypeTableRemap,
    /// `prepare_body_tables`: a closure type did not remap.
    ClosureTableRemap,
    /// Source closure frames are malformed, conflict, or cannot follow their type mapping.
    ClosureLayout,
    /// `prepare_body_tables`: `tuple_layout::merge` refused the body's declared tuple layouts.
    TupleLayout,
    /// `prepare_body_tables`: a global failed its remap or its static-identity intern.
    GlobalRemap,
    /// `prepare_body_tables`: the function or its signature did not remap.
    FunctionRemap,
    /// `prepare_body_tables`: a table door of the assembled module refused (trust-ir D1b: its id
    /// space is exhausted), so the body's tables could not be interned.
    ModuleTable,
    /// `remap_certificate::certify_remap_shape` refused the remapped function.
    RemapCertificate,
    /// Fixpoint: a call binds a result its callee's declaration cannot carry
    /// (`call_result_arity_incoherent`).
    CallResultArity,
    /// Fixpoint: a place-path value carrier reaches a live local callee with real params
    /// (`place_carrier_reaches_real_params`).
    PlaceCarrier,
    /// Fixpoint (R2): the signature reaches a struct row with no layout
    /// (`signature_reaches_unlaid_struct`) — an identity / unrevealed spelling, or a layout the
    /// producer withheld; neither is a monomorphic claim the assembled module can carry.
    UnlaidSignatureStruct,
    /// Pass 2 found no prepared body for an admitted `DefIndex`. Unreachable by construction
    /// (`assigned` and `prepared` are pushed together); named so it cannot be silent.
    PreparedBodyMissing,
    /// Held out by the re-assembly monotonicity veto (`spliced_veto`) with no earlier typed
    /// refusal on record — the earlier round refused it through `global_refusals`.
    Vetoed,
}

impl SpliceRefusal {
    /// Stable spelling written to `coverage.json` (`"splice_refusal"`), in the `Class(detail)`
    /// shape of the `unsupported` tags.
    fn marker(self) -> &'static str {
        match self {
            SpliceRefusal::NotLowered => "Splice(not lowered)",
            SpliceRefusal::GeneratedUngated => "Splice(generated body ungated)",
            SpliceRefusal::Symbolic => "Splice(symbolic body)",
            SpliceRefusal::UnionLane => "Splice(union placeholder lane)",
            SpliceRefusal::StorageValueTraffic => "Splice(storage value traffic)",
            SpliceRefusal::EnumParamLane => "Splice(enum param placeholder lane)",
            SpliceRefusal::ZstClosureArg => "Splice(zst callable stand-in argument)",
            SpliceRefusal::CoroutineFramePtr => "Splice(coroutine frame-pointer convention)",
            SpliceRefusal::ClosureAdapter => "Splice(closure adapter)",
            SpliceRefusal::FnptrAdapter => "Splice(synthesized fn-pointer adapter)",
            SpliceRefusal::NoFunctionBody => "Splice(no function body)",
            SpliceRefusal::EnumTable => "Splice(enum table not spliceable)",
            SpliceRefusal::StructTable => "Splice(struct table not spliceable)",
            SpliceRefusal::TypesTable => "Splice(types table not spliceable)",
            SpliceRefusal::ClosureTable => "Splice(closure table not table-free)",
            SpliceRefusal::GlobalShape => "Splice(global shape not spliceable)",
            SpliceRefusal::SignatureType => "Splice(signature type not spliceable)",
            SpliceRefusal::BlockParamType => "Splice(block param type not spliceable)",
            SpliceRefusal::InstructionType => "Splice(instruction type not spliceable)",
            SpliceRefusal::UnmodeledInstruction => "Splice(unmodeled instruction)",
            SpliceRefusal::Invoke => "Splice(invoke)",
            SpliceRefusal::IndirectCallSignature => "Splice(indirect call signature)",
            SpliceRefusal::FnPtrConstant => "Splice(fn-pointer constant)",
            SpliceRefusal::ConstantFuncId => "Splice(constant carries a FuncId)",
            SpliceRefusal::SwitchFuncId => "Splice(switch case carries a FuncId)",
            SpliceRefusal::StaticGlobalOrigin => "Splice(static global origin)",
            SpliceRefusal::DefTableGraph => "Splice(def table cycle or dangling reference)",
            SpliceRefusal::DefTableRemap => "Splice(def table remap)",
            SpliceRefusal::TypeTableRemap => "Splice(types table remap)",
            SpliceRefusal::ClosureTableRemap => "Splice(closure table remap)",
            SpliceRefusal::ClosureLayout => "Splice(closure layout merge)",
            SpliceRefusal::TupleLayout => "Splice(tuple layout merge)",
            SpliceRefusal::GlobalRemap => "Splice(global remap)",
            SpliceRefusal::FunctionRemap => "Splice(function remap)",
            SpliceRefusal::ModuleTable => "Splice(assembled module table refused)",
            SpliceRefusal::RemapCertificate => "Splice(remap certificate)",
            SpliceRefusal::CallResultArity => "Splice(call result arity)",
            SpliceRefusal::PlaceCarrier => "Splice(place carrier reaches real params)",
            SpliceRefusal::UnlaidSignatureStruct => "Splice(signature reaches a layout-less struct)",
            SpliceRefusal::PreparedBodyMissing => "Splice(prepared body missing)",
            SpliceRefusal::Vetoed => "Splice(vetoed by an earlier assembly round)",
        }
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
    /// Trust (2026-09-27): why a LOWERED body is not spliced — `Some` exactly when
    /// `lowered && !spliced` (see [`SpliceRefusal`]; `coverage_json` enforces it).
    splice_refusal: Option<SpliceRefusal>,
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

/// Trust (2026-09-27): remember, per body, the first NON-veto splice refusal any assembly round
/// recorded. `SpliceRefusal::Vetoed` only says an earlier round left the body out; the earlier
/// round's own reason is the one worth publishing.
fn record_first_refusals(rows: &[CoverageRow], first: &mut BTreeMap<u32, SpliceRefusal>) {
    for row in rows {
        match row.splice_refusal {
            Some(SpliceRefusal::Vetoed) | None => {}
            Some(refusal) => {
                first.entry(row.def_index).or_insert(refusal);
            }
        }
    }
}

/// Trust (2026-09-27): replace each published `SpliceRefusal::Vetoed` with the refusal that
/// first kept that body out (`record_first_refusals`). A body the earlier round left out through
/// `global_refusals` has no typed refusal on record and keeps `Vetoed`, which is still a name.
fn restore_vetoed_refusals(rows: &mut [CoverageRow], first: &BTreeMap<u32, SpliceRefusal>) {
    for row in rows {
        if row.splice_refusal == Some(SpliceRefusal::Vetoed) {
            if let Some(refusal) = first.get(&row.def_index) {
                row.splice_refusal = Some(*refusal);
            }
        }
    }
}

/// `spliced_veto` — Trust (owner call 2026-09-17(b)): `DefIndex`es that must not be spliced in
/// THIS assembly whatever `splice_ok` says about them, because an EARLIER assembly of the same
/// crate already left them un-spliced.
///
/// It exists for one reason, and it is a measured non-monotonicity, not belt-and-braces. The
/// unsignable-edge refusal below re-assembles after marking bodies unsupported, and pass 1's own
/// fixpoint is not monotone in the LIVE set: `place_carrier_reaches_real_params` refuses a caller
/// only while its callee is a live LOCAL target with parameters, so refusing that callee would
/// let the caller splice in the NEXT round when it did not splice in this one. A refusal pass
/// that ADMITS a body nothing admitted before is not a refusal, so the veto forbids it by
/// construction rather than by an argument about which predicates happen to be monotone today.
/// Empty for a single-shot assembly, which is every call outside that loop.
fn assemble(
    crate_name: &str,
    records: &[BodyRecord],
    spliced_veto: &std::collections::BTreeSet<u32>,
) -> Assembled {
    // ---- Pass 1: dense FuncId assignment for every spliceable body, in DefIndex order. ----
    // (records are already sorted + deduped by def_index.)
    //
    // Trust: pass 1 ALSO interns each admitted body's enum/struct/type tables into the assembled
    // module and pre-remaps every embedded `EnumId`/`StructId`/`TyId` in the body's function +
    // signature (`prepare_body_tables`) — all fallibility lives HERE, before a `FuncId` is assigned, so
    // pass 2 can never desync the dense id space by refusing late. `splice_ok` validated every
    // remap precondition (resolvability, positional ids, nested-first ordering), so an `Err`
    // from `prepare_body_tables` is a defensive tripwire (body simply not admitted, recorded in
    // coverage as un-spliced WITH its typed `SpliceRefusal`), never a silent mis-emit.
    //
    // Trust (#197 item 1): pass 1 is THREE steps, not one — collect candidates, refuse the
    // result-arity-incoherent ones TO A FIXPOINT, then assign dense ids. The refusal has to be
    // here for the reason stated above: it is only sound before a `FuncId` exists. Pass 2 is the
    // intuitive site (it already rewrites callees) and is WRONG — a late refusal punches a hole in
    // the dense id space, mis-numbers the declarations minted at `assigned.len() + decls.len()`,
    // and dangles every `Local` edge, trading 66 arity errors for a worse dangling-callee class.
    let mut module = Module::new(crate_name.to_string());
    let mut static_globals = static_globals::StaticGlobals::default();
    let mut global_refusals = BTreeMap::new();
    let mut assigned: Vec<(u32, FuncId)> = Vec::new();
    let mut prepared: Vec<(u32, Function, FuncTy, BodyMaps)> = Vec::new();
    let mut candidates: Vec<(usize, u32, Function, FuncTy, BodyMaps)> = Vec::new();
    // Trust (2026-09-27): the typed reason for every LOWERED body pass 1 leaves out — each
    // `continue` below and each fixpoint refusal records one, and pass 2 copies it onto the
    // body's coverage row. Before this map these drops reached the artifact as a bare
    // `"spliced": false`; see `SpliceRefusal`. (`global_refusals` stays the channel for the
    // static-identity refusals: those un-lower the row, and name themselves in `unsupported`.)
    let mut splice_refusals: BTreeMap<u32, SpliceRefusal> = BTreeMap::new();
    for (record_index, r) in records.iter().enumerate() {
        // Trust (owner call 2026-09-17(b)): the earliest sound point to drop a body — before a
        // `FuncId` exists for it, exactly as the pass-1 comment above requires of every refusal.
        if spliced_veto.contains(&r.def_index) {
            splice_refusals.insert(r.def_index, SpliceRefusal::Vetoed);
            continue;
        }
        if let Err(reason) = static_globals::validate_origins(r) {
            global_refusals.insert(r.def_index, reason);
            static_globals.poison_record(r);
            continue;
        }
        if let Some(refusal) = splice_refusal(r, records) {
            splice_refusals.insert(r.def_index, refusal);
            continue;
        }
        match prepare_body_tables(r, &mut module, &mut static_globals) {
            Err(refusal) => {
                splice_refusals.insert(r.def_index, refusal);
            }
            Ok((func, func_ty, maps)) => {
                // Trust (L1, artifact-lineage attestation): the CANONICAL-REMAPPING certificate,
                // structure half — `crate::remap_certificate`. The lineage digest makes the
                // artifact row and the flip event name ONE pre-assembly object; it says nothing
                // about whether the function that object BECAME still has that object's shape.
                // The remap is allowed to rewrite ids, `Ty`s and span file ids, and nothing
                // else, so the block set, the instruction sequence, the SSA numbering, the
                // opcodes, the proof annotations and the source line/column must survive it
                // exactly. A body whose remap moved any of those is REFUSED here — not
                // spliced, and recorded in coverage as un-spliced, exactly like an `Err` from
                // `prepare_body_tables` above.
                //
                // It runs HERE, in pass 1, for the reason this pass exists: refusal is only
                // sound before a `FuncId` is assigned (see the pass-1 comment above). Pass 2
                // writes only through `*callee` / `*sig` / `*fid` / `*ty` bindings taken from
                // `match &mut node.inst` arms — it never assigns a `node.inst` or a `Vec` — so
                // it cannot violate what is certified here. That argument is the whole of
                // pass 2's coverage; if it stops holding, this certificate must be re-sited.
                //
                // `r.function` is the pre-assembly function (`Some`, since `splice_ok` passed).
                if let Some(before) = r.function.as_ref() {
                    if crate::remap_certificate::certify_remap_shape(before, &func).is_err() {
                        splice_refusals.insert(r.def_index, SpliceRefusal::RemapCertificate);
                        continue;
                    }
                }
                candidates.push((record_index, r.def_index, func, func_ty, maps));
            }
        }
    }
    // A late conflicting claimant cannot leave the first claimant spliced.
    // This precedes both the call-edge fixpoint and dense FuncId assignment.
    for r in records {
        if static_globals.conflicts(r) {
            global_refusals.entry(r.def_index).or_insert("StaticGlobal(identity conflict)");
        }
    }
    // Trust (#197 item 1): refuse to splice a body that binds a call result the callee's
    // DECLARATION cannot carry. FIXPOINT, because refusal is contagious: dropping body B turns
    // every `CalleeResolution::Local(B)` edge into a `local-unlowered:` Decl, whose `decl_ret`
    // can newly be `None` — so a caller that was coherent against the spliced B can become
    // incoherent against the declared B. One pass would leave those behind.
    let mut live: Vec<bool> = candidates
        .iter()
        .map(|candidate| !global_refusals.contains_key(&candidate.1))
        .collect();
    loop {
        let live_defs: std::collections::BTreeSet<u32> = candidates
            .iter()
            .zip(live.iter())
            .filter(|(_, keep)| **keep)
            .map(|(c, _)| c.1)
            .collect();
        // Only Some-ness is read by the predicate (a `Local` edge links to a spliced body, whose
        // signature carries a real return type), so a placeholder id is exact here.
        let probe = |def_index: u32| -> Option<FuncId> {
            live_defs.contains(&def_index).then(|| FuncId::new(0))
        };
        // Declared param count of a LIVE candidate, by def_index. A refused body is not spliced,
        // so it declares nothing — `0` is the honest answer for it, and it is also what keeps the
        // two predicates converging together in one fixpoint rather than fighting.
        //
        // SNAPSHOTTED, not computed on demand: the refusal loop below mutates `live`, so a closure
        // that read it would hold an immutable borrow across the mutation. Both this map and
        // `live_defs` are therefore taken from the SAME start-of-iteration state, which is also
        // what makes the iteration well-defined — every predicate in one round sees one world.
        let live_params: std::collections::BTreeMap<u32, usize> = candidates
            .iter()
            .zip(live.iter())
            .filter(|(_, keep)| **keep)
            .map(|(c, _)| (c.1, c.3.params.len()))
            .collect();
        let params_of = |def_index: u32| -> usize { live_params.get(&def_index).copied().unwrap_or(0) };
        let mut changed = false;
        for i in 0..candidates.len() {
            if !live[i] {
                continue;
            }
            let (record_index, _, func, _, maps) = &candidates[i];
            let r = &records[*record_index];
            // Trust (2026-09-27): the same three predicates, in the same order, now each naming
            // itself. R2 reads the BODY's own tables (`signature_reaches_unlaid_struct`).
            // Ratification review 2026-09-28: every layout-less row refuses, as at the pin; a
            // row the producer's withheld-layout ledger names is refused too, and only NAMED so
            // in the debug record.
            let refusal = if call_result_arity_incoherent(r, func, maps, &probe)
                || r.adapters.iter().any(|adapter| call_result_arity_incoherent(r, adapter, maps, &probe))
            {
                Some(SpliceRefusal::CallResultArity)
            } else if place_carrier_reaches_real_params(r, func, maps, &probe, &params_of) {
                Some(SpliceRefusal::PlaceCarrier)
            } else if signature_reaches_unlaid_struct(r) {
                if !r.layout_withheld_structs.is_empty() {
                    tracing::debug!(
                        def_path = %r.def_path,
                        withheld = ?r.layout_withheld_structs,
                        "trust-ir crate assembly: R2 refuses a signature over a layout-less row; \
                         the producer withheld layouts in this body, which admits nothing"
                    );
                }
                Some(SpliceRefusal::UnlaidSignatureStruct)
            } else {
                None
            };
            if let Some(refusal) = refusal {
                splice_refusals.insert(r.def_index, refusal);
                live[i] = false;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    for (i, c) in candidates.into_iter().enumerate() {
        if !live[i] {
            continue;
        }
        // `records` is sorted+deduped by def_index and candidates preserve that order, so
        // `assigned` stays sorted and the `binary_search_by_key` lookups below remain valid.
        assigned.push((c.1, FuncId::new(assigned.len() as u32)));
        prepared.push((c.1, c.2, c.3, c.4));
    }
    let lookup = |def_index: u32| -> Option<FuncId> {
        assigned.binary_search_by_key(&def_index, |(d, _)| *d).ok().map(|i| assigned[i].1)
    };

    // Adapters are real functions in a disjoint dense suffix. Reserve every
    // slot before declarations are minted; source bodies retain their row IDs.
    let mut adapter_ids = BTreeMap::new();
    for r in records.iter().filter(|r| lookup(r.def_index).is_some()) {
        for adapter in &r.adapters {
            let id = FuncId::new((assigned.len() + adapter_ids.len()) as u32);
            adapter_ids.insert((r.def_index, adapter.id), id);
        }
    }
    let function_slots = assigned.len() + adapter_ids.len();
    let mut assembled_adapters = Vec::new();

    // Trust (WS5.2): no display-path collision set any more. rustc display paths are
    // deterministic but not injective (macro-generated const-eval bodies were measured with six
    // spliced definitions sharing one), which is exactly why they are no longer the NAME: a
    // spliced body is named by its link-time symbol (injective by construction — the mangler is
    // a function of the def) and its display path moves to `display_path`, which trust-ir
    // validates for usability only, never for uniqueness.
    let mut errors: Vec<String> = Vec::new();

    // ---- Pass 2: splice functions, rewriting intra-crate callee FuncIds. ----
    // Fail-closed declarations, first-encounter order. `DeclRecord` separates IDENTITY (stable
    // definition + optional concrete instance key) from checked facts (signature, ABI, display
    // name). A direct call contributes no full signature and is neutral: when an FnDef edge to
    // the SAME concrete key supplies one, the final validator checks that exact signature against
    // every direct instruction too. Two contradictory exact observations sticky-poison the row
    // and are refused by final validation; signature never splits or merges identities.
    let mut decls: Vec<DeclRecord> = Vec::new();
    let mut rows: Vec<CoverageRow> = Vec::new();
    // Trust (trust-ir D1b): a table door of the assembled module that refuses in pass 2 is a
    // fatal assembly error (appended to the declarations' errors below), never a panic and never
    // a late splice refusal: pass 1 owns every per-body refusal so the dense ids cannot desync.
    let mut table_refusals: Vec<String> = Vec::new();

    for r in records {
        let lowered = r.function.is_some() && r.unsupported.is_empty();
        let mut row = CoverageRow {
            def_path: r.def_path.clone(),
            def_index: r.def_index,
            kind: kind_str(r.kind),
            lowered,
            symbolic: r.symbolic,
            spliced: false,
            splice_refusal: None,
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
        if let Some(reason) = global_refusals.get(&r.def_index) {
            row.lowered = false;
            bump_unsupported(&mut row.unsupported, reason);
        }
        let Some(new_id) = lookup(r.def_index) else {
            // Trust (2026-09-27): a LOWERED body that is not spliced names why. An unlowered row
            // names nothing here — its `unsupported` tags already do.
            if row.lowered {
                row.splice_refusal = splice_refusals.get(&r.def_index).copied();
            }
            rows.push(row);
            continue;
        };
        // Pass 1 admitted this body, so its pre-remapped function + signature are present
        // (assigned and prepared are pushed together, same keys, same order).
        let Ok(pi) = prepared.binary_search_by_key(&r.def_index, |(d, _, _, _)| *d) else {
            if row.lowered {
                row.splice_refusal = Some(SpliceRefusal::PreparedBodyMissing);
            }
            rows.push(row);
            continue;
        };
        let (_, func, func_ty, body_maps) = &prepared[pi];

        let mut f = func.clone();
        f.id = new_id;
        // Trust (WS5.2, F-087): `Function.name` IS the link-time symbol (trust-ir v41, SPEC
        // §1.1) — `tcx.symbol_name` of the body's identity instance, stamped at finalization by
        // `stamp_link_symbols`, or the reserved `__trust_init_<hex>` spelling for an initializer,
        // which nothing links to and which is therefore `Linkage::Internal`. The human def path
        // (with the `{const-init}` / `{static-init}` marker, since `Function` has no kind field)
        // moves to `display_path`. Call resolution stays by body-local `FuncId` plus the exact
        // identity ledger; neither spelling is ever a join key.
        match &r.link_symbol {
            Some(symbol) => f.name = symbol.clone(),
            None => {
                // `stamp_link_symbols` names or refuses every splice candidate, so this is a
                // producer defect. Fatal (`Assembled::errors`), never a guessed name: the
                // placeholder below is unobservable because finalization aborts on it.
                errors.push(format!(
                    "trust-ir producer defect [missing-link-symbol]: body `{}` (DefIndex {}) \
                     reached the splice without a link-time symbol; crate finalization must name \
                     or refuse every splice candidate before assembly. Report this.",
                    r.def_path, r.def_index
                ));
                f.name =
                    crate::link_symbol::unlinked_declaration_name(&r.def_path, Some(r.definition));
            }
        }
        f.display_path = Some(definition_base_name(r));
        if matches!(r.kind, BodyKind::ConstInit | BodyKind::StaticInit) {
            f.linkage = Linkage::Internal;
        }
        f.ty = intern_func_ty(&mut module, func_ty.clone()).unwrap_or_else(|refusal| {
            table_refusals.push(format!("signature of FuncId {}: {refusal}", new_id.index()));
            f.ty
        });
        // Trust (#180): a SPLICED body carries its REAL ABI. `Function::new` defaults
        // `calling_conv` to `C`, and leaving it there would make every call from this body to a
        // now-correctly-Rust-ABI declaration read as a CROSS-CONVENTION CALL EDGE
        // (`Module::first_ffi_boundary`'s second scan) — trading one false FFI boundary for
        // another. The declaration and definition halves have to move together.
        // Trust (wave-FC): "is a Rust function, so say so" was a false claim for a spliced
        // LOCAL `extern "C"` body; the record now carries the ground truth.
        match r.abi.calling_conv() {
            Ok(convention) => f.calling_conv = convention,
            Err(why) => table_refusals.push(format!("body FuncId {}: {why}", new_id.index())),
        }
        // (EnumDefs/StructDefs/types were interned and every embedded `EnumId`/`StructId`/`TyId`
        // remapped in pass 1 — `prepare_body_tables`; `f`/`func_ty` here are the pre-remapped
        // clones.)

        let mut adapters = Vec::with_capacity(r.adapters.len());
        for original in &r.adapters {
            let Some(shape) = crate::closure_adapter::inspect(original, &r.closure_types, &r.func_types) else {
                table_refusals.push("validated closure adapter lost its shape".to_owned());
                continue;
            };
            let closure = body_maps.closure_map[shape.closure.as_usize()];
            let ct = &module.closure_types[closure.as_usize()];
            let apparent = module.func_types[ct.func.as_usize()].clone();
            let physical = crate::closure_adapter::physical_signature(ct, &apparent).unwrap();
            let signature = match intern_func_ty(&mut module, physical) {
                Ok(signature) => signature,
                Err(error) => { table_refusals.push(format!("closure adapter signature: {error}")); continue; }
            };
            let ct = &module.closure_types[closure.as_usize()];
            let name = format!("{}__trust_closure_adapter_{}", f.name, original.id.index());
            let mut adapter = crate::closure_adapter::build(original.id, signature, name,
                crate::closure_adapter::Shape { closure, body: shape.body }, ct, &apparent).unwrap();
            // Keep original IDs through the common operand rewrite below.
            adapter.id = adapter_ids[&(r.def_index, original.id)];
            adapters.push(adapter);
        }
        for function in std::iter::once(&mut f).chain(adapters.iter_mut()) {
        for block in &mut function.blocks {
            for node in &mut block.body {
                // Trust (#197b): the arity THIS instruction declares. MANDATORY companion to
                // #197a, not a refinement of it. `validate_instruction_result_arities` compares
                // the callee declaration's `returns.len()` against `node.results.len()`, so a
                // declaration minted from a site binding a DIFFERENT number of results must not
                // carry a return type — and must key separately, exactly as `ret_key` already
                // splits by TYPE.
                //
                // The hazard is measured, not hypothetical. In
                // tests/ui/threads-sendsync/task-comm-6.rs one `FuncId` covers `Result::unwrap`
                // at two instantiations: `Result<(), SendError<isize>>::unwrap()` (4 sites, bind
                // 0 results) and `Result<isize, RecvError>::unwrap()` (4 sites, bind 1). Because
                // `emit_call` returns early on `is_never()`/unit BEFORE its recording block while
                // the value site still writes back to every entry sharing the `func_id`, the unit
                // entry ends up carrying `Some(Isize)` — order-dependently. Keying on unanimity
                // ALONE would therefore move those 4 errors to their mirror rather than clear
                // them. Corpus census: 178 `expected 0` errors, exactly 2 mixed-arity decls,
                // 5 occurrences.
                let nres = node.results.len();
                match &mut node.inst {
                    Inst::MakeClosure { func, .. } => {
                        if let Some(id) = adapter_ids.get(&(r.def_index, *func)) {
                            *func = *id;
                        } else {
                            table_refusals.push("closure constructor lost its adapter target".to_owned());
                        }
                    }
                    Inst::Call { callee, .. } => {
                        match resolve_callee(r, *callee, &lookup, body_maps) {
                            CalleeResolution::Local(id) => {
                                *callee = id;
                                row.calls_resolved += 1;
                            }
                            CalleeResolution::Decl {
                                key,
                                name,
                                is_extern,
                                ret,
                                params,
                                abi,
                                definition,
                                concrete_key,
                                local_def_index,
                                link,
                            } => {
                                // A declaration's `returns` must agree with what THIS site binds.
                                // Disagreement splits the declaration rather than silently picking
                                // one site's view; `nres` joins the key so the split is stable.
                                // `(None, 1)` is the UNFIXABLE case — an opaque/RPIT/async return
                                // `map_ty` declined, so the decl honestly has no type while the site
                                // binds one. Splitting its key would change nothing, so leave those
                                // byte-identical; only a decl that DOES carry a type and meets a site
                                // that binds a different count needs the split.
                                let (key, ret) = match (&ret, nres) {
                                    (Some(_), n) if n != 1 => (format!("{key}|nres:{n}"), None),
                                    _ => (key, ret),
                                };
                                *callee = decl_id(
                                    &mut decls,
                                    function_slots,
                                    key,
                                    name,
                                    ret,
                                    abi,
                                    definition,
                                    concrete_key.as_ref(),
                                    local_def_index,
                                    None,
                                    params,
                                    link,
                                );
                                if is_extern {
                                    row.calls_extern += 1;
                                } else {
                                    row.calls_unresolved += 1;
                                }
                            }
                        }
                    },
                    // Trust: re-intern the indirect-call signature from the body's snapshot
                    // table into the assembled module. `splice_ok` held in pass 1 on this same
                    // immutable record (`body_sig_ok`), so the lookup succeeds; the guard is
                    // shape-preserving, never a default.
                    Inst::CallIndirect { sig, .. } => {
                        // Trust (#184 follow-on): REMAP the body-table signature before interning
                        // it. It used to be re-interned raw, which was sound only because
                        // `body_sig_ok` required every param/return to be table-free — the same
                        // wall that confined declaration returns. With `BodyMaps` in hand the
                        // signature can carry `Ty::Struct`/`Ty::Enum` correctly, so the wall comes
                        // down. A `None` (dangling or not-yet-interned id) declines the body.
                        if let Some(ft) = r.func_types.get(sig.as_usize()).cloned() {
                            let Some(ft) = remap_func_ty(&ft, body_maps) else {
                                continue;
                            };
                            *sig = intern_func_ty(&mut module, ft).unwrap_or_else(|refusal| {
                                table_refusals.push(format!("indirect-call signature: {refusal}"));
                                *sig
                            });
                        }
                    }
                    // Trust: a reified fn-pointer constant — remap its `Ty::Func` sig id the
                    // same way, and rewrite the target `FuncId` through the ledger EXACTLY
                    // like a Call callee (it is a call-graph edge; counted in the same
                    // coverage buckets). `splice_ok` proved the sig resolvable and the ledger
                    // identity unique.
                    Inst::Const { ty, value } => {
                        if let Constant::FnDef(fid) = value {
                            let mut fndef_full: Option<FuncTy> = None;
                            if let Ty::Func(sig) = ty {
                                // Trust (#184 follow-on): same remap as the CallIndirect arm — a
                                // reified fn-pointer constant's signature was also re-interned raw.
                                if let Some(ft) = r.func_types.get(sig.as_usize()).cloned() {
                                    let Some(ft) = remap_func_ty(&ft, body_maps) else {
                                        continue;
                                    };
                                    // Trust (wave-CTOR): this IS the fndef's declared signature in
                                    // module numbering — the observation the declaration must
                                    // match for the edge to type.
                                    fndef_full = Some(ft.clone());
                                    *sig =
                                        intern_func_ty(&mut module, ft).unwrap_or_else(|refusal| {
                                            table_refusals
                                                .push(format!("fn-pointer signature: {refusal}"));
                                            *sig
                                        });
                                }
                            }
                            match resolve_callee(r, *fid, &lookup, body_maps) {
                                CalleeResolution::Local(id) => {
                                    *fid = id;
                                    row.calls_resolved += 1;
                                }
                                CalleeResolution::Decl {
                                    key,
                                    name,
                                    is_extern,
                                    ret,
                                    params,
                                    abi,
                                    definition,
                                    concrete_key,
                                    local_def_index,
                                    link,
                                } => {
                                    *fid = decl_id(
                                        &mut decls,
                                        function_slots,
                                        key,
                                        name,
                                        ret,
                                        abi,
                                        definition,
                                        concrete_key.as_ref(),
                                        local_def_index,
                                        fndef_full.as_ref(),
                                        params,
                                        link,
                                    );
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

        }
        assembled_adapters.extend(adapters);

        row.spliced = true;
        // Trust (L1): record WHERE this body landed in the assembled module. Declarations are
        // appended after this loop, so `new_id.index()` is a stable index into
        // `module.functions` for the whole artifact.
        row.func_id = Some(new_id.index());
        if let Err(refusal) = module.try_add_function(f) {
            table_refusals.push(format!("FuncId {}: {refusal}", new_id.index()));
        }
        rows.push(row);
    }

    for adapter in assembled_adapters {
        if let Err(refusal) = module.try_add_function(adapter) {
            table_refusals.push(format!("closure adapter: {refusal}"));
        }
    }

    // Declarations LAST so `module.functions[i].id == i` stays true end to end. Exact FnDef
    // observations carry exact signatures; unresolved observations retain the vararg/unknown
    // spelling. Even contradicted rows occupy their IDs and return fatal assembly errors — a gap
    // here would let a later append silently retarget already-rewritten edges.
    let mut unsignable_declarations = Vec::new();
    let mut assembly_errors = errors;
    assembly_errors.extend(append_declarations(&mut module, &decls, &mut unsignable_declarations));
    assembly_errors.extend(
        table_refusals
            .into_iter()
            .map(|refusal| format!("assembled module table refused: {refusal}")),
    );

    // trust-ir v50: every constant array the bodies spelled as a uniform list takes its one
    // canonical spelling, now that the module is whole and before anything binds to it.
    crate::uniform_array_spelling::respell_uniform_arrays(&mut module);

    let lowered = rows.iter().filter(|r| r.lowered).count();
    let spliced = rows.iter().filter(|r| r.spliced).count();

    // Trust (B8 step 1): keep each declaration's FuncId/key plus exact local source identity.
    // `decls` is about to go out of scope with the only record of WHY each declaration exists;
    // the seam and Clean-origin link gates need exactly that.
    let decl_keys = decls
        .iter()
        .map(|decl| crate::clean_origin_join::DeclarationLinkIdentity {
            func_id: decl.id,
            key: decl.key.clone(),
            local_def_index: decl.local_def_index,
        })
        .collect();

    let codegen_declarations = match retain_codegen_declarations(&module, &decls) {
        Ok(records) => records,
        Err(error) => {
            assembly_errors.push(error);
            Vec::new()
        }
    };
    Assembled {
        module,
        errors: assembly_errors,
        coverage_rows: rows,
        lowered,
        spliced,
        declarations: decls.len(),
        assigned,
        decl_keys,
        codegen_declarations,
        unsignable_declarations,
    }
}

/// Trust (#197 item 3b, R2): does `ty` reach a struct row of body `r` that has no layout?
///
/// A `StructDef` with no `size`/`align` is one `map_ty` declined to lay out, or one whose layout
/// the producer WITHHELD (`a032dc214b`, `0372fdcaeb`). When R2 landed the first was the only
/// case: an IDENTITY or UNREVEALED spelling — `S<T>` before instantiation, `Foo<<Bar as
/// Trait>::Assoc>` before the projection is revealed. Its concrete twin is a SEPARATE
/// `StructDef` with a real layout, because `map_ty` interns per SPELLING: `S<T>` is `struct.1`
/// and `S<i32>` is `struct.3`, and nothing in the module records that they denote one type.
/// Both cases refuse; see [`signature_reaches_unlaid_struct`] for why the withheld case does too.
///
/// Walked over the BODY's own tables (`r.structs`, body-local ids). The assembled module's rows
/// are these rows re-interned by content (`Module::add_struct_def`), layout fields included, so
/// the answer is the one the assembled module would give — the pin walked that module.
///
/// Recursive with a visited set: the outer struct is the one that lacks a layout in every
/// measured case, but a layout-less struct can also sit behind a reference or inside another
/// struct's fields, and a self-referential `Box` shape would otherwise loop.
fn ty_reaches_unlaid_struct(
    r: &BodyRecord,
    ty: &Ty,
    seen: &mut std::collections::BTreeSet<u32>,
) -> bool {
    match ty {
        Ty::Struct(sid) => {
            if !seen.insert(sid.index()) {
                return false;
            }
            let Some(sd) = r.structs.iter().find(|s| s.id == *sid) else {
                // Unresolvable id: not this predicate's question — `splice_ok`'s remap
                // preconditions already refuse a body with a dangling struct reference.
                return false;
            };
            if sd.size.is_none() || sd.align.is_none() {
                return true;
            }
            sd.fields.iter().any(|f| ty_reaches_unlaid_struct(r, &f.ty, seen))
        }
        Ty::Ref(inner) | Ty::RefMut(inner) | Ty::PtrConst(inner) | Ty::PtrMut(inner)
        | Ty::Rc(inner) => ty_reaches_unlaid_struct(r, inner, seen),
        Ty::Array(_, _) | Ty::Tuple(_) => false,
        _ => false,
    }
}

/// Trust (#197 item 3b, R2): is this body's signature an IDENTITY spelling rather than a
/// monomorphic claim?
///
/// THE DEFECT. A spliced `Function`'s signature is a claim about a concrete callable. When the
/// body was lowered at its IDENTITY instantiation the signature carries the generic spelling,
/// and a monomorphic caller then passes the CONCRETE one — two `StructId`s for one type:
///
///   CallArgTypeMismatch { callee: "twice", expected: "struct.1", actual: "struct.3" }
///   struct @S<T>   { struct.0 }                id=1   (no size — identity)
///   struct @S<i32> { struct.2 } size=0 align=0 id=3   (concrete)
///
/// and the same shape unrevealed-vs-revealed for TAIT:
///
///   ReturnTypeMismatch { expected: "struct.1", actual: "struct.3" }
///   struct @Foo<<Bar as Trait>::Assoc> { .. }           id=1   (no size — unrevealed)
///   struct @Foo<()>                    { .. } size=0    id=3   (revealed)
///
/// Measured: 7 CATM + 4 RTM, the entire residue after items 1 and 3.
///
/// THIS IS WAVE-20's RULE, one step further out. wave-20 already refuses to LINK a forced-havoc
/// (generic) call site — "linking a polymorphic call to the callee's identity-lowered body is an
/// identity lie". These edges are the ones that rule misses: the SITE is concrete, so nothing
/// marks it havoc, but the CALLEE's spliced signature is still identity-spelled. Refusing the
/// callee turns the edge into an honest declaration whose return comes from the ledger at the
/// concrete site.
///
/// A WITHHELD LAYOUT REFUSES TOO — ratification review 2026-09-28. `a032dc214b` and
/// `0372fdcaeb` (2026-09-23/25) made the producer WITHHOLD a layout rustc computed when a
/// field's emitted spelling cannot carry rustc's bytes (a declined `Option` riding the
/// `Ty::Bool` flag lane, a thin `&mut dyn`), and `881a7e964a` (2026-09-27) exempted every row
/// the producer's ledger (`BodyRecord::layout_withheld_structs`) named. That exemption ADMITTED
/// bodies the pin refused — the thread-local init body returning `RefCell<Option<(u64, u64)>>`
/// by value over a 1-byte model of rustc's 24 bytes, calling the foreign `RefCell::new` with a
/// `bool` where rustc passes the `Option` — and the witness that decided it lives in the
/// producer (`lib.rs`), outside this frozen file, so nothing in the oracle checked it. A body
/// whose signature carries a row the producer could not lay out is not a callable definition
/// the assembled module can honestly carry, whatever the reason the layout is absent; the honest
/// state is "declared, not defined", exactly as for an identity spelling. Pinned by
/// `crate_module/splice_refusal_tests.rs`.
///
/// THE REAL FIX IS B8. Per-Instance lowering makes the callee's signature concrete at each
/// instantiation and the two spellings become one; this predicate then stops firing on its own
/// for identity spellings. A withheld layout closes only when the producer can carry rustc's
/// bytes for it.
fn signature_reaches_unlaid_struct(r: &BodyRecord) -> bool {
    let Some(func_ty) = r.func_ty.as_ref() else {
        // No signature: `splice_ok` refuses the body before it can become a candidate.
        return false;
    };
    let mut seen = std::collections::BTreeSet::new();
    func_ty
        .params
        .iter()
        .chain(func_ty.returns.iter())
        .any(|t| ty_reaches_unlaid_struct(r, t, &mut seen))
}

/// Trust (#197 item 3): does this body hand a place-path VALUE to a call edge whose callee is a
/// spliced local with REAL declared params? If so the body must not be spliced.
///
/// THE DEFECT. `place_path_carrier` is set by the wave-RS/wave-MC lanes when they substitute a
/// receiver PLACE VALUE for the pointer the callee's parameter declares. The producer already
/// knows this is a deliberate spelling mismatch — `run_seam_differentials` withholds such a body
/// from linked interpretation for exactly this reason, in its own words: *"the carrier arg is a
/// VALUE standing in for the callee's pointer param, so linked interpretation manufactures a
/// signature-mismatch THIR-defect verdict out of a deliberate spelling."* But it still SPLICES
/// the body, and the assembled module then carries that value across the edge, which is
/// `CallArgTypeMismatch { expected: "ptr", actual: "struct.N" }`. Measured: 24 occurrences.
///
/// This is the SAME hazard as `zst_closure_arg` one type over, and `splice_ok` already refuses
/// that one with the matching argument — "the ASSEMBLED module would carry it across a call edge
/// whose callee declares a real closure type, with nothing in the module recording that the two
/// denote the same value". The carrier lane was withheld from the seam but never from the splice;
/// this closes that asymmetry.
///
/// WHY NOT COMPARE THE TYPES DIRECTLY. The exact predicate is the validator's — zip the args
/// against `callee_ty.params` and compare each `Ty`. Reproducing that here means reimplementing
/// `validate.rs`'s value-type map (`value_type` / `infer_result_type`) in a second crate with no
/// shared code, and a predicate that drifts from the checker it guards refuses the WRONG bodies.
/// The right long-term fix is to make the validator's typing public and call the one
/// implementation (the discipline `pin_enum_tag_lane` already follows: "deliberately the same
/// function and not a mirrored twin"). Until then this uses the producer's own flag, which is set
/// at the exact site that creates the mismatch and cannot drift from it.
///
/// DELIBERATELY AN OVER-APPROXIMATION, and narrowed to keep it small. The flag is per-BODY, not
/// per-call, so a body carrying at one edge and calling a real-param local at another is refused
/// too. The `Local`-with-params conjunct is what keeps that from being the whole carrier lane:
/// a carrier whose callee is a BODYLESS declaration is vacuously valid today, because
/// `validate.rs` zips args against `callee_ty.params`, which is EMPTY under the bodyless
/// `params: [], is_vararg: true` encoding — so every forced-havoc / extern / symbolic-callee
/// carrier site validates and must keep splicing. Refusing on the bare flag would demote that
/// entire lane for no validity gain.
fn place_carrier_reaches_real_params(
    r: &BodyRecord,
    func: &Function,
    maps: &BodyMaps,
    lookup: &dyn Fn(u32) -> Option<FuncId>,
    params_of: &dyn Fn(u32) -> usize,
) -> bool {
    if !r.place_path_carrier {
        return false;
    }
    for block in &func.blocks {
        for node in &block.body {
            let Inst::Call { callee, .. } = &node.inst else {
                continue;
            };
            if !matches!(resolve_callee(r, *callee, lookup, maps), CalleeResolution::Local(_)) {
                continue;
            }
            // `Local` means `resolve_callee` found exactly one local ledger identity for this
            // `FuncId` (its own `[c] if c.is_local` arm), so this re-filter names the same entry.
            if let Some(c) = r.callees.iter().find(|c| c.func_id == *callee && c.is_local) {
                if params_of(c.def_index) > 0 {
                    return true;
                }
            }
        }
    }
    false
}

/// Trust (#197 item 1): does this prepared body bind a call result its callee's DECLARATION
/// cannot carry? If so the body must not be spliced — pass 1 refuses it, before any `FuncId`
/// exists.
///
/// THE DEFECT THIS CLOSES. `emit_call` binds an SSA result whenever the call is non-unit and
/// non-diverging, but a DECLARATION's return type comes from the ledger and is `Option<Ty>` —
/// `None` means "this site could not be typed" (an opaque/RPIT/async return `map_ty` declined),
/// which the assembler writes as `returns: []`, a positive claim that the callee returns
/// NOTHING. `validate_instruction_result_arities` then compares `returns.len()` against
/// `node.results.len()` and reports `InstrResultArityMismatch`. Measured: 66 occurrences over
/// 37 files, the largest ill-formed-module class.
///
/// It cannot be fixed where it is observed. Pass 2's declaration arm already splits a decl whose
/// type disagrees with a site's binding count, and its own comment names the residue exactly:
/// *"`(None, 1)` is the UNFIXABLE case — the decl honestly has no type while the site binds
/// one."* Unfixable THERE is right: pass 2 may not refuse a body without desyncing the dense id
/// space. So the answer is to refuse earlier, which is what this predicate is for.
///
/// THE PREDICATE MIRRORS THE VALIDATOR, not a paraphrase of it: it reproduces pass 2's own
/// `(Some(_), n) if n != 1 => None` adjustment first, then compares the resulting `returns.len()`
/// against the site's `results.len()`. Keeping the two in one shape is deliberate — a predicate
/// that drifts from the emitter it guards refuses the wrong bodies.
///
/// SCOPE, deliberately narrow on both sides:
/// * `Inst::Call` ONLY. `Inst::Const`/`Constant::FnDef` is EXCLUDED even though it is also a
///   call-graph edge that pass 2 rewrites through `resolve_callee`: the bridge takes a Const's
///   arity from its own `ty`, never from the callee's `returns`, so including it would refuse
///   bodies that have no arity error at all. `Inst::Invoke` is likewise absent — the producer
///   emits none (measured: zero in `lib.rs`), and pass 2 does not rewrite Invoke callees either,
///   so teaching this predicate about it ALONE would make the two disagree.
/// * A call binding ZERO results is untouched. `call @decl(...)` with no result is the
///   overwhelmingly common valid shape and validates today; dropping the count comparison and
///   refusing on `ret.is_none()` alone would be mass loss.
///
/// WHAT NOT TO DO INSTEAD. Two cheaper-looking shortcuts are both unsound. Emitting a 0-result
/// `Call` at the dead `let _ = f()` sites is order-dependent: `emit_call`'s `(None, Some(t))` arm
/// has no retro-poison, so a later typed site leaves the decl `-> (t)` and produces the mismatch
/// in the OPPOSITE direction. And simply dropping the unused result binding leaves `returns: []`
/// asserting "returns nothing" about a callee that returns a real value — laundering a detected
/// defect into a silent ABI lie, which is the #189 family.
fn call_result_arity_incoherent(
    r: &BodyRecord,
    func: &Function,
    maps: &BodyMaps,
    lookup: &dyn Fn(u32) -> Option<FuncId>,
) -> bool {
    for block in &func.blocks {
        for node in &block.body {
            let Inst::Call { callee, .. } = &node.inst else {
                continue;
            };
            let CalleeResolution::Decl { ret, .. } = resolve_callee(r, *callee, lookup, maps)
            else {
                // A `Local` edge links to a spliced body whose signature carries a real return
                // type; the arity question is answered by that signature, not by a declaration.
                continue;
            };
            let nres = node.results.len();
            let ret = match (&ret, nres) {
                (Some(_), n) if n != 1 => None,
                _ => ret,
            };
            if usize::from(ret.is_some()) != nres {
                return true;
            }
        }
    }
    false
}

/// Resolve one emitted callee `FuncId` through the body's identity ledger. Fail-closed: only a
/// single unambiguous LOCAL identity whose own body was spliced resolves; everything else becomes
/// a declaration.
fn concrete_decl(
    kind: DeclKind,
    c: &CalleeRef,
    link: Option<&CalleeLink>,
    maps: &BodyMaps,
    is_extern: bool,
) -> CalleeResolution {
    // A concrete key is the complete declaration identity, so call-site return observations do
    // not join the dedup key HERE. They remain checked facts: an exact FnDef signature, when
    // present, is validated against every direct call. Legacy unresolved edges keep the return
    // suffix because they have no stronger identity and no full signature to validate against.
    // Trust (wave-RETSPLIT): `decl_id` appends the same `|ret:` suffix at INTERN time, and only
    // to an observation whose spelling contradicts the row it would otherwise join — one source
    // type spelled as two module types (the RMW-degraded vs faithful struct registration) is two
    // IR types, and one declaration cannot carry both. See that function for why the alternative
    // (weakening to `returns: []`) is a claim, not an unknown.
    let rest = match &c.concrete_key {
        Some(key) => format!("{}|concrete-v1:{}", c.def_path, key.symbol_suffix()),
        None => format!("{}{}", c.def_path, ret_key(c, maps)),
    };
    CalleeResolution::Decl {
        key: decl_key(kind, rest),
        name: c.def_path.clone(),
        is_extern,
        ret: decl_ret(c, maps),
        params: decl_params(c, maps),
        abi: c.abi,
        definition: Some(c.definition),
        concrete_key: c.concrete_key.clone(),
        local_def_index: (kind == DeclKind::LocalUnlowered).then_some(c.def_index),
        // No finalization stamp (a TyCtxt-free fixture, or a record that never reached
        // `stamp_link_symbols`) is the fail-closed reading: no symbol, producer unrecorded.
        link: link.cloned().unwrap_or_default(),
    }
}

fn resolve_callee(
    r: &BodyRecord,
    callee: FuncId,
    lookup: &dyn Fn(u32) -> Option<FuncId>,
    maps: &BodyMaps,
) -> CalleeResolution {
    let idents: Vec<&CalleeRef> = r.callees.iter().filter(|c| c.func_id == callee).collect();
    // Trust (WS5.2): the finalization link facts of a SINGLE ledger identity. `callee_links` is
    // index-aligned with `callees`; an unstamped record yields `None` (no symbol, unrecorded).
    let single_link = match idents.as_slice() {
        [_] => r
            .callees
            .iter()
            .position(|c| c.func_id == callee)
            .and_then(|index| r.callee_links.get(index)),
        _ => None,
    };
    match idents.as_slice() {
        // Trust (wave-20): a FORCED-HAVOC edge (a generic call site) declares — NEVER links — even
        // when its `DefIndex` has a clean local body. Linking a polymorphic call to the callee's
        // identity-lowered body is an identity lie AND re-opens the wave-19 fat/thin DST hole at a
        // generic site. The distinct `havoc:` key prefix keeps it from coalescing with any real
        // `local:`/`extern:` edge to the same symbol; it counts in the honest can't-resolve bucket.
        [c] if c.force_havoc
            || c.concrete_key
                .as_ref()
                .is_some_and(|key| key.has_generic_args()) =>
        {
            // Defense in depth: a concrete generic has no per-instance BodyRecord yet, so even
            // if admission forgot the sticky force flag it must never collapse through
            // `lookup(def_index)` onto the identity-lowered body.
            concrete_decl(DeclKind::Havoc, c, single_link, maps, false)
        }
        [c] if c.is_local => match lookup(c.def_index) {
            Some(id) => CalleeResolution::Local(id),
            // A real local fn, but its own body did not lower cleanly — declare, don't link.
            None => concrete_decl(DeclKind::LocalUnlowered, c, single_link, maps, false),
        },
        [c] => concrete_decl(DeclKind::Extern, c, single_link, maps, true),
        // No ledger entry at all — there is no site evidence to type a return with.
        [] => CalleeResolution::Decl {
            key: decl_key(DeclKind::Unknown, callee.index()),
            name: format!("!unknown_callee_{}", callee.index()),
            is_extern: false,
            ret: None,
            // No ledger entry, so no recovered signature either — and nothing has
            // withdrawn one, which `ParamSignature::Unsigned` says in one value.
            params: crate::ParamSignature::Unsigned,
            // No ABI authority exists; finalization must refuse instead of inventing C.
            abi: crate::calling_convention::FunctionAbi::UNKNOWN,
            definition: None,
            concrete_key: None,
            local_def_index: None,
            // No identity, so no symbol and no producer: a reserved never-linkable row.
            link: CalleeLink::default(),
        },
        // Two identities behind one body-local FuncId. The current producer's full-identity
        // interning plus dense allocation cannot create this set, but a malformed/legacy record
        // must still fail closed: which BODY to link is a guess, so declare.
        //
        // Trust (#197a): the RESULT TYPE is a separate question, and this arm used to answer it
        // `None` under the claim that "their return types are not jointly attributable". The
        // LEDGER has already answered it: `emit_call` writes `ret_ty` to EVERY entry sharing the
        // `func_id` and poisons the whole set on the first disagreement, so a genuine conflict is
        // already `ret_ty_conflict` before this runs. What the old arm discarded was the ledger's
        // own UNANIMOUS verdict — `size_of::<A>()` and `size_of::<B>()` both return `usize`, yet
        // adding the second instantiation turned a valid `(...) -> (usize)` declaration into
        // `(...) -> ()` and minted two errors. Measured: 116 `InstrResultArityMismatch`.
        _ => {
            let ret = unanimous_ret(&idents, maps);
            // Trust (#197a follow-up): the ABI must come from the ledger too, by the SAME
            // unanimity rule as the return type. This arm used to hardcode `false` and call it
            // "the conservative foreign default" — but `false` is not conservative, it is a
            // CLAIM: it says these callees use the C ABI, and `is_foreign_abi_boundary` then
            // holds `repr(Rust)` structs to FFI repr rules (#190 is the same mistake one level
            // out). It was inert only while `ret` was always `None`, because the repr check has
            // nothing to inspect without a type. Giving the declaration a real return type made
            // the latent lie observable: +2 `FfiStructReprUnpinned` on
            // tests/ui/threads-sendsync/task-comm-16.rs, where every identity behind
            // `!ambiguous_callee_12363` is an ordinary Rust `Result::unwrap`.
            let abi = idents.first().map(|c| c.abi)
                .filter(|abi| idents.iter().all(|c| c.abi == *abi))
                .unwrap_or(crate::calling_convention::FunctionAbi::CONFLICT);
            CalleeResolution::Decl {
                key: decl_key(
                    DeclKind::Ambiguous,
                    format!("{}{}", callee.index(), ret_suffix(&ret)),
                ),
                name: format!("!ambiguous_callee_{}", callee.index()),
                is_extern: false,
                ret,
                // Trust (v41): unanimity or nothing, on the same rule the `ret`
                // above and `abi` below already use. Two identities behind
                // one body-local `FuncId` that disagree about their parameters
                // cannot be signed with either one's — picking a side here would
                // be a guess in exactly the place this arm exists to refuse.
                //
                // ANY identity behind this id having called short withdraws the
                // whole row, and it is tested FIRST: the arm already refuses to
                // pick a side between two identities, and a short call is a
                // stronger reason still. The old spelling computed the unanimity
                // and the withdrawal into two independent fields; that they could
                // not disagree rested on `poison_callee_param_tys` clearing
                // `param_tys` on EVERY entry sharing the `func_id` — exactly the
                // set iterated here — so unanimity was `None` whenever anything
                // was withdrawn. True, and unstated anywhere. The single value
                // cannot express the disagreement at all.
                params: if idents.iter().any(|c| c.params.is_withdrawn()) {
                    crate::ParamSignature::Withdrawn
                } else {
                    idents
                        .first()
                        .and_then(|first| first.params.signature().cloned())
                        .filter(|p| idents.iter().all(|c| c.params.signature() == Some(p)))
                        .map_or(crate::ParamSignature::Unsigned, crate::ParamSignature::Signed)
                },
                abi,
                definition: None,
                concrete_key: None,
                local_def_index: None,
                // Two identities: which symbol this row stands for is a guess, so none.
                link: CalleeLink::default(),
            }
        }
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
    // Trust (#180, v36): the target is now stamped UNCONDITIONALLY. The old gate stamped only
    // when the `struct_passing` claim was VACUOUS — no by-value aggregate crossing any call edge —
    // because both policy values assert `byval`/`sret` `ParamAttrs` this producer never emits, and
    // asserting one would have been a false ABI claim carried into `Module::stable_digest`.
    //
    // trust-ir v36 adds `StructPassingPolicy::Unclassified`, which says exactly what is true here:
    // this producer performs no aggregate classification. With an honest value available the gate
    // is no longer needed — `triple`/`pointer_size`/`endianness` were always plain facts about the
    // compilation target, and withholding them bought nothing but `TargetInfoRequired`.
    let aggregate_at_a_boundary = module.func_types.iter().any(|ft| {
        ft.params.iter().chain(ft.returns.iter()).any(crosses_by_value_aggregate)
    });
    let _ = aggregate_at_a_boundary; // retained: the scan is the honesty argument's evidence.
    module.target_info = Some(source_target_info(tcx));
}

/// Physical target facts with no unearned aggregate ABI classification.
pub(crate) fn source_target_info(tcx: TyCtxt<'_>) -> trust_ir::TargetInfo {
    let target = &tcx.sess.target;
    trust_ir::TargetInfo {
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
        // Trust (#180, v36): the truthful value. NOT `default()` (`NativeC`) — that would claim
        // native-C classification the producer does not perform. A consumer needing a
        // classification must refuse the module rather than infer one; see the variant's docs.
        struct_passing: trust_ir::StructPassingPolicy::Unclassified,
    }
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
    //
    // Ratification review 2026-09-28: WITHOUT the fn-pointer map. `5e29156632` threaded
    // `func_map` through `BodyMaps::remap` to sign fn-pointer PARAMETERS (`decl_params`); through
    // this function it also began answering a fn-pointer RETURN, so a call binding a `Ty::Func`
    // result stopped tripping `call_result_arity_incoherent` — a body the pin refused was
    // spliced, which that commit's own "every existing caller behaves exactly as before" denied.
    // The return side keeps the pin's answer: a `Ty::Func` return does not remap.
    remap_ty(
        c.ret_ty.as_ref()?,
        &maps.enum_map,
        &maps.struct_map,
        &maps.ty_map,
        &maps.closure_map,
    )
}

/// Trust (v41): the callee's recovered parameter types, REMAPPED from the body's
/// numbering into the assembled module's — the params twin of [`decl_ret`].
///
/// Same reason and same failure mode: the ledger records a body-local `Ty`, a
/// declaration lives in the ASSEMBLED module, and a `Ty::Struct(sid)` carried
/// across raw would name a different type. Table-free types remap to
/// themselves, so the scalar lane that shipped first is byte-identical.
///
/// ALL-OR-NOTHING. One parameter that will not remap (an out-of-range or
/// not-yet-interned id) makes the whole signature `None` and the declaration
/// keeps the old unsigned spelling, because a partially remapped parameter list
/// is a FALSE signature rather than a shorter one.
fn decl_params(c: &crate::CalleeRef, maps: &BodyMaps) -> crate::ParamSignature {
    // No poison flag here, unlike `decl_ret`. `ret_ty` is MERGED across call
    // sites into one ledger row and so needs sticky contradiction; the parameter
    // signature is filled from the same saved `fn_sig` at admission or after
    // argument types are registered, never from call operands. Disagreement
    // between two rows is caught where it can actually arise —
    // `DeclRecord::params_conflict` when two rows merge into one declaration,
    // and the unanimity requirement in the ambiguous-callee arm.
    //
    // A WITHDRAWAL TRAVELS FIRST and unconditionally: it is the one state whose
    // meaning does not depend on whether the remap below succeeds, and carrying
    // it in the return value is what makes `concrete_decl` a single field write
    // instead of two that have to agree.
    if c.params.is_withdrawn() {
        return crate::ParamSignature::Withdrawn;
    }
    let Some(recorded) = c.params.signature() else {
        return crate::ParamSignature::Unsigned;
    };
    let mut out = Vec::with_capacity(recorded.len());
    for ty in recorded {
        // ALL-OR-NOTHING, as the doc above says: one parameter that will not remap
        // leaves the declaration UNSIGNED rather than shorter.
        let Some(mapped) = maps.remap(ty) else {
            return crate::ParamSignature::Unsigned;
        };
        out.push(mapped);
    }
    crate::ParamSignature::Signed(out)
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

/// Trust (#197a): the return type EVERY identity behind one ambiguous `FuncId` agrees on.
///
/// `None` — any entry unknown, poisoned by `ret_ty_conflict`, or un-remappable — keeps the honest
/// empty `returns`. This does NOT decide which body to link; it only declines to throw away a
/// verdict the ledger already reached.
fn unanimous_ret(idents: &[&crate::CalleeRef], maps: &BodyMaps) -> Option<Ty> {
    let first = decl_ret(idents.first()?, maps)?;
    idents
        .iter()
        .all(|c| decl_ret(c, maps).as_ref() == Some(&first))
        .then_some(first)
}

/// Trust (#197a): `ret_key`'s twin for an already-computed `Option<Ty>` (the ambiguous arm has
/// no single `CalleeRef` to key on). Same spelling, so the two agree by construction.
fn ret_suffix(ret: &Option<Ty>) -> String {
    match ret {
        Some(t) => format!("|ret:{t:?}"),
        None => String::new(),
    }
}

/// Trust (v41): print the signing census when the gate is on. A lane that never
/// fired and a lane that gained nothing both report zero signed, so the
/// POPULATION is the control and is printed beside the gain.
fn report_declaration_signing_census(decls: &[DeclRecord]) {
    // Behind its OWN env var, never printed unconditionally. The census writes
    // to stderr, and `tests/ui` DIFFS stderr — measured 2026-09-14, printing it
    // by default turned 72 fixtures red on the census line alone and buried the
    // real delta (+18 passing) under an instrument artifact. A probe that
    // changes the thing it measures is not a probe.
    if std::env::var_os("TRUST_SIGN_DECL_CENSUS").is_none() {
        return;
    }
    let total = decls.len();
    let unknown = decls.iter().filter(|d| matches!(d.signature, DeclSigState::Unknown)).count();
    let signed = decls
        .iter()
        .filter(|d| matches!(d.signature, DeclSigState::Unknown) && d.params.signature().is_some())
        .count();
    let poisoned = decls.iter().filter(|d| d.params_conflict).count();
    let withdrawn = decls.iter().filter(|d| d.params.is_withdrawn()).count();
    eprintln!(
        "[SIGN_DECL] declarations={total} unknown-signature={unknown} \
         signed={signed} unsignable={} params-conflict={poisoned} \
         params-withdrawn={withdrawn}",
        unknown - signed
    );
}

/// Trust: mint-or-reuse a fail-closed declaration `FuncId` (`defined` = count of pass-1
/// defined functions; declarations take the ids after them, first-encounter order). Shared by
/// the `Inst::Call` callee rewrite and the `Constant::FnDef` rewrite.
fn decl_id(
    decls: &mut Vec<DeclRecord>,
    defined: usize,
    key: String,
    name: String,
    ret: Option<Ty>,
    abi: crate::calling_convention::FunctionAbi,
    definition: Option<crate::lineage::DefinitionIdentity>,
    concrete_key: Option<&crate::lineage::ConcreteCalleeKey>,
    local_def_index: Option<u32>,
    full_sig: Option<&FuncTy>,
    params: crate::ParamSignature,
    link: CalleeLink,
) -> FuncId {
    // Trust (wave-RETSPLIT): an observation whose RESULT TYPE contradicts the row's does NOT
    // poison the row — it gets a row of its OWN, keyed by the spelling it observed.
    //
    // WHAT IS ACTUALLY BEING OBSERVED TWICE. `ret` is a MODULE-numbered `Ty` (`decl_ret` remaps
    // the body-numbered one). Two bodies can spell ONE source type as two different module types:
    // `struct_ty_rmw_opaque` registers the struct with `Ty::Unit` PLACEHOLDER siblings for every
    // non-pure lane while `map_ty`'s Adt arm registers it faithfully, `register_struct` dedups
    // only per body by `(DefId, GenericArgs)` — so each body keeps whichever builder ran first —
    // and `Module::add_struct_def` dedups STRUCTURALLY, so the two field lists land on two
    // distinct `StructId`s crate-wide.
    //
    // The trigger is that the struct is reached THROUGH THE RMW/OPAQUE BUILDER anywhere in a body
    // BEFORE the call, not that it is written: that builder serves the field WRITE
    // (`written_field: Some(i)`) and the whole-struct/field READ through a reference
    // (`written_field: None`) alike, and only a body that never routes through it keeps `map_ty`'s
    // faithful spelling. Measured on seal trust-dac08891 with `-Ztrust-verify=off
    // -Ztrust-ir-lower=on`, one `-> S` callee plus one body that only reads it:
    //
    //   `fn f(p: &S)      -> u32 { let _ = p.a; let s = make(); s.a }`  1 error (SHARED read)
    //   `fn f(p: &mut S)  -> u32 { p.a = 1;     let s = make(); s.a }`  1 error (write)
    //   `fn f(p: &mut S)  -> u32 { let s = make(); let _ = p.a; s.a }`  0 errors (after the call)
    //   `fn f(mut p: S)   -> u32 { p.a = 1;     let s = make(); s.a }`  0 errors (by value)
    //
    // and a near-miss module that validates clean dumps the two spellings side by side:
    // `struct @S { u32, struct.8 } size=32 align=8 id=9` against `struct @S { u32, () } id=10`
    // (the layout is dropped by `register_struct`'s coherence gate) — one source type, two
    // `Ty::Struct` ids, in ONE module.
    //
    // WHY SPLIT AND NOT WEAKEN. There is no weaker observation to record. A declaration's
    // "unknown" spelling is `returns: []` (`is_vararg` covers only the params side), and that is a
    // POSITIVE claim of "returns nothing" — the #189 family — which every site binding a result
    // then contradicts (`InstrResultArityMismatch`), trading one fatal error for another while
    // laundering a detected defect into an ABI lie. Splitting keeps every declaration's signature
    // in agreement with EVERY instruction that names it, and two bodyless declarations for one
    // callee are strictly WEAKER than either merged signature: a consumer models two independent
    // uninterpreted functions where one would do, which can only lose facts, never invent them.
    // Resolution is by `FuncId` (names are display identity only, and `emitted_decl_name` already
    // mints reserved injective names for exactly this collision), and the Clean-origin join
    // already strips `|ret:`/`|nres:` split suffixes when it matches a `local-unlowered:` key
    // against its emitted row, so both rows link to the one definition.
    //
    // THE OTHER FAIL-CLOSED SHAPE, considered and rejected: decline the BODY that registered the
    // degraded spelling. It is the producer's own idiom, and it would remove the fabricated
    // `{u32, ()}` type as well as the edge — but it is not reachable from here (this is crate
    // assembly, long after body lowering, and the row cannot tell which of its observers is the
    // degraded one), and it pays for declaration agreement with SILENT coverage loss: a body the
    // producer could lower is dropped from the module, and the degraded spelling is as likely to
    // be the FIRST registration as the second, so the rule would drop arbitrary bodies. Splitting
    // keeps every body and every edge and adds no claim that some module does not already publish
    // (a single-caller module publishes exactly this degraded `-> struct` signature today, and
    // validates).
    //
    // The suffix is `ret_key`'s spelling, and it is appended ONLY on the contradicting
    // observation, so a module with no contradiction keeps byte-identical keys. That spelling is
    // module-numbering dependent (`Struct(StructId(14))`), and this key is hashed into
    // `emitted_decl_name` and copied into the Clean-origin disclosure, so the suffixed row's
    // symbol and `decl_key` move with unrelated registration-order changes. Accepted because the
    // suffix appears only where the crate previously ABORTED: no key that exists today changes.
    // `ret_conflict` below stays as the floor: if two distinct `Ty`s ever share a `Debug`
    // spelling they merge here and poison there, which is fatal, not silent.
    //
    // SPLIT ONLY ON THE RESULT TYPE. The predicate re-checks name, ABI and `local_def_index`
    // for equality, so an observation that contradicts the row on IDENTITY as well never takes
    // this path: it falls through to the merge below and trips the `DeclSigState::Conflict`
    // tripwire there. Without those three conjuncts the split would divert exactly the
    // observations that check is for, and `local_def_index` is the LINKING authority for
    // `link_clean_origin_edges` (display paths explicitly are not) — two rows carrying two
    // def_indexes would link to two different Clean definitions instead of aborting.
    let key = match &ret {
        Some(observed)
            if decls.iter().any(|decl| {
                decl.key == key
                    && decl.definition == definition
                    && decl.concrete_key.as_ref() == concrete_key
                    && decl.name == name
                    && decl.abi == abi
                    && decl.local_def_index == local_def_index
                    && decl.link == link
                    && decl.ret.as_ref().is_some_and(|previous| previous != observed)
            }) =>
        {
            format!("{key}|ret:{observed:?}")
        }
        _ => key,
    };
    match decls.iter_mut().find(|decl| {
        decl.key == key
            && decl.definition == definition
            && decl.concrete_key.as_ref() == concrete_key
    }) {
        Some(decl) => {
            // Direct observations carry no full signature and are NEUTRAL. Once an FnDef gives
            // this exact identity a signature, final validation checks every direct instruction
            // against it. Exact contradictions are sticky and can never be resurrected.
            if let Some(observed) = full_sig {
                decl.signature = match &decl.signature {
                    DeclSigState::Unknown => DeclSigState::Exact(observed.clone()),
                    DeclSigState::Exact(previous) if previous == observed => {
                        DeclSigState::Exact(previous.clone())
                    }
                    DeclSigState::Exact(_) | DeclSigState::Conflict => DeclSigState::Conflict,
                };
            }
            // Trust (v41): the recovered signature is ground truth about the callee,
            // so two rows for one identity must agree. Disagreement is STICKY, on the
            // same rule as `ret_conflict`: without it a third observation could
            // resurrect a parameter list two earlier ones had already contradicted.
            // Trust (v41 coherence): WITHDRAWAL IS STICKY AND CROSSES BODIES.
            // A `None` params contribution is neutral here by design — most
            // bodies simply cannot state a signature — so a body that called
            // this callee SHORT has to say so positively, or the next body's
            // fully-lowered call signs the declaration and the short call then
            // meets a real arity (measured: `CallArgCountMismatch` on
            // `std::io::_print`, expected 1, actual 0, across two `println!`
            // shapes in two functions of one crate).
            // ONE transition, not two field writes that have to agree: `withdraw`
            // discards any signature on record and records the withdrawal in the
            // same value, and nothing leads back out of it.
            if params.is_withdrawn() {
                decl.params.withdraw();
            }
            if let Some(observed) = params.signature() {
                if decl.params_conflict || decl.params.is_withdrawn() {
                    // Sticky: contradicted or withdrawn stays so. `sign` below would
                    // refuse a withdrawal on its own; the explicit test is kept because
                    // `params_conflict` is a separate `bool` the type knows nothing about.
                } else {
                    let contradicts =
                        decl.params.signature().is_some_and(|previous| previous != observed);
                    let unsigned = decl.params.signature().is_none();
                    if contradicts {
                        decl.params.unsign();
                        decl.params_conflict = true;
                    } else if unsigned {
                        decl.params.sign(observed.clone());
                    }
                }
            }
            if let Some(observed) = ret {
                if decl.ret_conflict {
                    // Sticky: a later agreeing observation cannot resurrect a contradicted type.
                } else if let Some(previous) = &decl.ret {
                    if *previous != observed {
                        decl.ret = None;
                        decl.ret_conflict = true;
                    }
                } else {
                    decl.ret = Some(observed);
                }
            }
            if decl.name != name
                || decl.abi != abi
                || decl.local_def_index != local_def_index
                || decl.link != link
            {
                // Name, ABI, and exact local source identity are checked facts. A contradiction
                // is retained as an explicit refusal state instead of choosing first- or
                // last-writer wins.
                decl.signature = DeclSigState::Conflict;
            }
            decl.id
        }
        None => {
            let id = FuncId::new((defined + decls.len()) as u32);
            decls.push(DeclRecord {
                key,
                id,
                name,
                ret,
                ret_conflict: false,
                // The `if withdrawn { None }` this replaces was the field pair keeping
                // itself coherent by hand. `ParamSignature::Withdrawn` carries no
                // parameter list, so the fresh row simply IS the contribution.
                params,
                params_conflict: false,
                abi,
                definition,
                concrete_key: concrete_key.cloned(),
                local_def_index,
                signature: full_sig
                    .cloned()
                    .map_or(DeclSigState::Unknown, DeclSigState::Exact),
                link,
            });
            id
        }
    }
}

/// Trust (#184 follow-on): remap every param/return of a BODY-numbered `FuncTy` into the
/// assembled module's numbering. `None` (fail-closed) if any component does not remap — the
/// caller skips the instruction's rewrite, which leaves the body un-spliceable rather than
/// carrying a dangling id.
fn remap_func_ty(ft: &FuncTy, maps: &BodyMaps) -> Option<FuncTy> {
    // trust-ir v60: the ABI record names no table id, so the remap carries it unchanged.
    let mut out = FuncTy {
        params: Vec::new(),
        returns: Vec::new(),
        is_vararg: ft.is_vararg,
        abi: ft.abi.clone(),
    };
    for p in &ft.params {
        out.params.push(maps.remap(p)?);
    }
    for r in &ft.returns {
        out.returns.push(maps.remap(r)?);
    }
    Some(out)
}

/// Equality-interning into `Module::func_types` (`add_func_type` itself never dedups). A full
/// table is a refusal (trust-ir D1b), never a panic.
fn intern_func_ty(module: &mut Module, ft: FuncTy) -> Result<FuncTyId, trust_ir::IdSpaceExhausted> {
    match module.func_types.iter().position(|existing| *existing == ft) {
        Some(i) => Ok(FuncTyId::new(i as u32)),
        None => module.add_func_type(ft),
    }
}

/// Can this body be spliced into the crate module as a defined function? Fail-closed structural
/// tripwires on top of "lowered clean" — see the module docs.
///
/// Trust (2026-09-27): answers WHY NOT, typed — the FIRST tripwire the body trips, as a
/// [`SpliceRefusal`] that reaches the body's coverage row; `None` means spliceable. It used to
/// answer `bool`, which is how every refusal below reached the artifact as a bare
/// `"spliced": false` with no reason attached.
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
fn splice_refusal(r: &BodyRecord, records: &[BodyRecord]) -> Option<SpliceRefusal> {
    if r.generated_ungated {
        return Some(SpliceRefusal::GeneratedUngated);
    }
    if !r.unsupported.is_empty() {
        return Some(SpliceRefusal::NotLowered);
    }
    // Trust (totality Batch C): a symbolic body's module carries value-less
    // extern-immutable globals — lowered-for-coverage, never spliced.
    if r.symbolic {
        return Some(SpliceRefusal::Symbolic);
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
        return Some(SpliceRefusal::UnionLane);
    }
    // Trust (storage value traffic): a checked `MaybeUninit` or geometry-proved union is spelled
    // `Ty::Storage` (060a4cd7ff), which is addressable geometry and never an SSA value. The
    // shared trust-ir validator refuses value-position storage for the WHOLE module, so a body
    // that carries it -- or mints a declaration that would -- must be refused HERE, by its own
    // predicate, before it can turn the crate module invalid. Addressable uses (a field read
    // through `&Parent`, an `Alloca`/`GEP` of the geometry) carry no violation and still splice.
    if r.storage_value_traffic {
        return Some(SpliceRefusal::StorageValueTraffic);
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
        return Some(SpliceRefusal::EnumParamLane);
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
        return Some(SpliceRefusal::ZstClosureArg);
    }
    // Trust (B5 stage 2): a YIELDING coroutine lowered with the frame-POINTER convention.
    // Param 0 is the caller-owned frame pointer and the entry block dispatches on
    // `frame[0]`, but a caller lowered elsewhere passes the coroutine BY VALUE — splicing
    // this function would put an ABI lie in the assembled module. Refused on the flag alone,
    // never by scanning for `CoroSuspend`: the hazard is the SIGNATURE, which no instruction
    // scan can see. Design of record:
    // docs/design/2026-08-30-b5-stage2-yield-to-corosuspend.md.
    if r.coroutine_frame_ptr {
        return Some(SpliceRefusal::CoroutineFramePtr);
    }
    // Trust (fn-ptr adapter lane): the body's mini-module carried a PRODUCER-SYNTHESIZED
    // closure→fn-pointer adapter. That older protocol remains quarantined;
    // retaining typed FnOnce adapters does not admit fn-pointer shims.
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
        return Some(SpliceRefusal::FnptrAdapter);
    }
    let mut adapter_ids = std::collections::BTreeSet::new();
    for adapter in &r.adapters {
        let Some(shape) = crate::closure_adapter::inspect(adapter, &r.closure_types, &r.func_types) else {
            return Some(SpliceRefusal::ClosureAdapter);
        };
        if !crate::is_adapter_func_id(adapter.id.index()) || !adapter_ids.insert(adapter.id) {
            return Some(SpliceRefusal::ClosureAdapter);
        }
        let mut targets = r.callees.iter().filter(|callee| callee.func_id == shape.body);
        let Some(target) = targets.next() else { return Some(SpliceRefusal::ClosureAdapter); };
        let closure = &r.closure_types[shape.closure.as_usize()];
        let apparent = &r.func_types[closure.func.as_usize()];
        let mut expected = vec![Ty::Closure(shape.closure)];
        expected.extend(apparent.params.iter().cloned());
        if targets.next().is_some() || !target.is_local || target.force_havoc
            || !target.params.signature().is_some_and(|actual| actual == expected.as_slice())
        {
            return Some(SpliceRefusal::ClosureAdapter);
        }
    }
    let (Some(f), Some(ft)) = (&r.function, &r.func_ty) else {
        return Some(SpliceRefusal::NoFunctionBody);
    };
    // Enum table: positional ids, and every variant field RESOLVABLE (`enum_def_field_ok`).
    // Trust (#174): this used to demand table-free-or-strictly-earlier-enum, because pass 1
    // interned enums before structs so an enum could not name a struct id. Pass 1 is now a
    // TOPOLOGICAL intern of the enum+struct DAG, so ordering is the intern's job (and a cycle
    // fails the body closed there); splice_ok's job here is resolvability alone.
    for (i, ed) in r.enums.iter().enumerate() {
        if ed.id.as_usize() != i {
            return Some(SpliceRefusal::EnumTable);
        }
        // Trust (B3-3): a variant field may be a NESTED first-class enum with
        // a strictly smaller id (registration is inner-before-outer) — the
        // struct-table nested-first discipline, mirrored. Everything else
        // must be table-free.
        if !ed.variants.iter().all(|v| v.fields.iter().all(|f| enum_def_field_ok(r, f))) {
            return Some(SpliceRefusal::EnumTable);
        }
    }
    // Struct table: positional ids, nested-first dependencies and checked array element entries.
    let bounds = def_field_entry_bounds(r);
    for (i, sd) in r.structs.iter().enumerate() {
        if sd.id.as_usize() != i {
            return Some(SpliceRefusal::StructTable);
        }
        if !sd.fields.iter().all(|field| def_field_ok(r, &field.ty, i, &bounds)) {
            return Some(SpliceRefusal::StructTable);
        }
    }
    // Types table: entries may reference structs + strictly-earlier types entries.
    for (j, t) in r.types.iter().enumerate() {
        if !type_entry_ok(r, t, j) {
            return Some(SpliceRefusal::TypesTable);
        }
    }
    // Trust (B6): closure-type table — the `func` id must index the body's own
    // func_types snapshot (with table-free params/returns, re-interned at splice),
    // and every capture must be table-free (the producer's thin-capture gate,
    // CHECKED here, never assumed).
    // Trust (2026-09-23): `table_free_as_tuple_spelled`, not bare `ty_table_free`, for the
    // closure's call signature — a param `[(u8, u8); 2]` was table-free as
    // `Ty::Tuple([(u8, u8); 2])` and is a first-class `Ty::Array` now; the closure map in pass 1
    // remaps it through the types map either way.
    let tuple_spelled = tuple_spelled_table_free_entries(r);
    for ct in &r.closure_types {
        let func_ok = r.func_types.get(ct.func.as_usize()).is_some_and(|ft| {
            !ft.is_vararg
                && ft
                    .params
                    .iter()
                    .chain(ft.returns.iter())
                    .all(|t| table_free_as_tuple_spelled(r, t, &tuple_spelled))
        });
        if !func_ok || !ct.captures.iter().all(ty_table_free) {
            return Some(SpliceRefusal::ClosureTable);
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
        return Some(SpliceRefusal::GlobalShape);
    }
    // Signature and block-param types must be spliceable (remappable ⇒ nothing dangles).
    if !ft.params.iter().chain(ft.returns.iter()).all(|t| ty_spliceable(r, t)) {
        return Some(SpliceRefusal::SignatureType);
    }
    for block in &f.blocks {
        if !block.params.iter().all(|(_, ty)| ty_spliceable(r, ty)) {
            return Some(SpliceRefusal::BlockParamType);
        }
        for node in &block.body {
            // Trust: every instruction-embedded type must be spliceable. The one exception is
            // a reified fn-pointer constant's `Ty::Func` (its own arm below re-interns the sig
            // id through `body_sig_ok`); `inst_embedded_tys` skips exactly that position.
            match inst_embedded_tys(&node.inst) {
                Some(tys) => {
                    if !tys.into_iter().all(|t| ty_spliceable(r, t)) {
                        return Some(SpliceRefusal::InstructionType);
                    }
                }
                // An instruction variant the ty-scan does not model (never producer-emitted
                // today) — refuse rather than move an unscanned type between modules.
                None => return Some(SpliceRefusal::UnmodeledInstruction),
            }
            match &node.inst {
                // The FuncId-bearing instruction pass 2 rewrites through the ledger.
                Inst::Call { .. } => {}
                Inst::MakeClosure { ty, func, captures } => {
                    let Some(adapter) = r.adapters.iter().find(|adapter| adapter.id == *func) else {
                        return Some(SpliceRefusal::ClosureAdapter);
                    };
                    let Some(shape) = crate::closure_adapter::inspect(adapter, &r.closure_types, &r.func_types) else {
                        return Some(SpliceRefusal::ClosureAdapter);
                    };
                    if shape.closure != *ty
                        || r.closure_types.get(ty.as_usize()).is_none_or(|ct| ct.captures.len() != captures.len())
                    {
                        return Some(SpliceRefusal::ClosureAdapter);
                    }
                }
                // Trust: an indirect call is spliceable iff its embedded per-body sig id
                // resolves to a non-vararg, table-free signature (pass 2 re-interns it into
                // the assembled module).
                Inst::CallIndirect { sig, .. } => {
                    if !body_sig_ok(r, *sig) {
                        return Some(SpliceRefusal::IndirectCallSignature);
                    }
                }
                // FuncId-bearing but not rewritten here — never emitted by the producer today;
                // fail closed if that ever changes.
                Inst::Invoke { .. } => return Some(SpliceRefusal::Invoke),
                Inst::Const { ty, value } => match value {
                    // Trust: a reified fn-pointer constant — spliceable iff typed `Ty::Func`
                    // over a resolvable per-body sig AND its `FuncId` has exactly ONE ledger
                    // identity (pass 2 rewrites it exactly like a Call callee; zero identities
                    // mean an unledgered emission, while multiple identities mean malformed
                    // non-singleton ledger input — both refuse, never guess).
                    Constant::FnDef(fid) => {
                        let Ty::Func(sig) = ty else { return Some(SpliceRefusal::FnPtrConstant) };
                        if !body_sig_ok(r, *sig) {
                            return Some(SpliceRefusal::FnPtrConstant);
                        }
                        if r.callees.iter().filter(|c| c.func_id == *fid).count() != 1 {
                            return Some(SpliceRefusal::FnPtrConstant);
                        }
                        // Trust: and the TARGET's own signature must actually be the one this
                        // constant claims — see `fnptr_target_sig_ok`. Sig-resolvability plus a
                        // unique ledger identity (the two checks above) say nothing about arity.
                        if !fnptr_target_sig_ok(r, records, *fid, *sig) {
                            return Some(SpliceRefusal::FnPtrConstant);
                        }
                    }
                    _ => {
                        if !constant_funcid_free(value) {
                            return Some(SpliceRefusal::ConstantFuncId);
                        }
                    }
                },
                Inst::Switch { cases, .. } => {
                    if !cases.iter().all(|c| constant_funcid_free(&c.value)) {
                        return Some(SpliceRefusal::SwitchFuncId);
                    }
                }
                _ => {}
            }
        }
    }
    None
}

/// [`splice_refusal`] as the predicate its callers in this file's tests were written against.
#[cfg(test)]
fn splice_ok(r: &BodyRecord, records: &[BodyRecord]) -> bool {
    splice_refusal(r, records).is_none()
}

/// Trust (storage value traffic): does this per-body mini-module, or a declaration its callee
/// ledger would mint, carry `Ty::Storage` at a value position? The module half is exactly
/// trust-ir's [`Module::visit_storage_violations`] (the policy final validation applies), so
/// the producer neither restates nor narrows it. The ledger half asks the same layout table
/// about each recorded return and signed parameter type, in the body's own numbering, because
/// a call names no result type: only the declaration `decl_ret`/`decl_params` mints does.
/// Over-approximates (an unreferenced pended signature also counts): it can only refuse.
fn module_carries_storage_value_traffic(module: &Module, callees: &[crate::CalleeRef]) -> bool {
    let layouts = module.layout_table();
    let mut found = false;
    module.visit_storage_violations(&layouts, |_| found = true);
    found
        || callees.iter().any(|callee| {
            callee.ret_ty.as_ref().is_some_and(|ty| layouts.type_contains_storage_by_value(ty))
                || callee.params.signature().is_some_and(|params| {
                    params.iter().any(|ty| layouts.type_contains_storage_by_value(ty))
                })
        })
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
/// structs, and their defs are checked self-contained, so no cycle is possible); Trust
/// (vtable slice 15, 2026-09-23): a `Ty::Array` whose types entry this same rule admits
/// (`def_field_entry_bounds` — a scalar, a nested array, a tuple naming earlier structs;
/// an exact earlier registered struct) — pass 1 interns it in dependency order, so
/// no cross-table cycle can arise. Anything else table-indexed fails closed.
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
        // Widest supported structural precheck only: final source-target validation
        // remains mandatory. Geometry is not initialized value traffic.
        Ty::Storage(layout) => layout.is_well_formed(64),
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

fn def_field_ok(r: &BodyRecord, ty: &Ty, i: usize, bounds: &[Option<usize>]) -> bool {
    match ty {
        // Widest supported structural precheck only: final source-target validation
        // remains mandatory. Geometry is not initialized value traffic.
        Ty::Storage(layout) => layout.is_well_formed(64),
        Ty::Vector(elem, _) => def_field_ok(r, elem, i, bounds),
        Ty::Tuple(elems) => elems.iter().all(|e| def_field_ok(r, e, i, bounds)),
        Ty::Ref(inner)
        | Ty::RefMut(inner)
        | Ty::PtrConst(inner)
        | Ty::PtrMut(inner)
        | Ty::Rc(inner) => def_field_ok(r, inner, i, bounds),
        Ty::Struct(sid) => sid.as_usize() < i,
        Ty::Enum(eid) => r.enums.get(eid.as_usize()).is_some_and(|ed| ed.id == *eid),
        // Trust (vtable slice 15): a FIRST-CLASS array field was admitted iff its types-table
        // entry was TABLE-FREE (a scalar element — all `map_ty`'s spelling gate minted for N>0),
        // because pass 1 pre-interned exactly those entries BEFORE the def tables.
        //
        // Trust (2026-09-23): every fixed-size array is first-class now, so a field the OLD
        // spelling carried inline as `Ty::Tuple([T; N])` — and this function admitted through
        // its tuple arm, `def_field_ok(T)` — names an entry `T` instead: `[[u32; 2]; 2]` names
        // `[u32; 2]`, `[(S, u8); 2]` names `(S, u8)`. The entry is admitted by the SAME rules
        // this function applies to a field, resolved through the table
        // ([`def_field_entry_bounds`]), and pass 1 interns it as a `DefNode::Ty` in dependency
        // order. Nonempty arrays of exact earlier registered structs use that same
        // dependency order; direct enum elements keep their separate refusal.
        //
        // Trust: keep the old table-free zero-array lane and additionally carry an exact
        // earlier registered struct element. Every definition is still checked by the outer
        // positional/nested-first loop; the existing DefNode::Ty DAG remaps this dependency
        // before the holding struct, preserving the element type and its alignment. This does
        // not admit zero arrays over tuples naming structs, references, nested arrays or Func.
        Ty::Array(tid, 0) => {
            r.types.get(tid.as_usize()).is_some_and(ty_table_free)
                || zero_array_struct::element_bound(&r.types, &r.structs, *tid, i).is_some()
        }
        Ty::Array(tid, _) => {
            array_field_elem_bound(r, tid.as_usize(), bounds).is_some_and(|b| b <= i)
        }
        _ => ty_table_free(ty),
    }
}

/// Trust (2026-09-23): per types entry, whether it may stand as the element of a first-class
/// array DEF FIELD — `Some(bound)` iff [`def_field_ok`]'s rules hold for it (table-free
/// leaves, resolvable enums, arrays over admissible EARLIER entries), where `bound` is one more
/// than the largest `StructId` it names (0 if none), so the enclosing struct `i` needs
/// `bound <= i` — `def_field_ok`'s nested-first `sid < i`. `None` = never admissible.
///
/// One pass in entry order, each entry deciding against the verdicts of the entries before it
/// (a nested array names a strictly earlier entry — `pend_ty` pends inner-before-outer, and
/// `type_entry_ok` refuses anything else): O(total size of the table), whatever the array
/// lengths and however the entries share sub-entries.
fn def_field_entry_bounds(r: &BodyRecord) -> Vec<Option<usize>> {
    let mut bounds: Vec<Option<usize>> = Vec::with_capacity(r.types.len());
    for t in &r.types {
        let b = def_field_ty_bound(r, t, &bounds);
        bounds.push(b);
    }
    bounds
}

/// Trust (2026-09-23): [`def_field_ok`] for a type inside a types entry, as a struct-id bound
/// (see [`def_field_entry_bounds`]); `earlier` holds the verdicts of the entries before it.
fn def_field_ty_bound(r: &BodyRecord, ty: &Ty, earlier: &[Option<usize>]) -> Option<usize> {
    match ty {
        Ty::Vector(elem, _) => def_field_ty_bound(r, elem, earlier),
        Ty::Tuple(elems) => elems
            .iter()
            .try_fold(0usize, |acc, e| Some(acc.max(def_field_ty_bound(r, e, earlier)?))),
        Ty::Ref(inner)
        | Ty::RefMut(inner)
        | Ty::PtrConst(inner)
        | Ty::PtrMut(inner)
        | Ty::Rc(inner) => def_field_ty_bound(r, inner, earlier),
        Ty::Struct(sid) => {
            r.structs.get(sid.as_usize()).filter(|sd| sd.id == *sid).map(|_| sid.as_usize() + 1)
        }
        Ty::Enum(eid) => r.enums.get(eid.as_usize()).filter(|ed| ed.id == *eid).map(|_| 0),
        // Trust: mirror the exact zero-array element lane in `def_field_ok`. An entry only
        // records the bound here; its enclosing field must still satisfy nested-first order.
        Ty::Array(k, 0) => r.types.get(k.as_usize()).filter(|t| ty_table_free(t)).map(|_| 0).or_else(|| {
            zero_array_struct::element_bound(&r.types, &r.structs, *k, r.structs.len())
        }),
        Ty::Array(k, _) => array_field_elem_bound(r, k.as_usize(), earlier),
        _ => ty_table_free(ty).then_some(0),
    }
}

/// Trust: the verdict for an array whose element is types entry `k`. A direct struct
/// element carries its exact registered positional ID through `def_field_ty_bound`;
/// the holding definition must satisfy that bound, and the dependency DAG interns
/// the struct before this entry and this entry before the holder. This deliberately
/// extends the historical spelling-parity lane. Direct enum elements remain refused.
fn array_field_elem_bound(r: &BodyRecord, k: usize, bounds: &[Option<usize>]) -> Option<usize> {
    if matches!(r.types.get(k)?, Ty::Enum(_)) {
        return None;
    }
    bounds.get(k).copied().flatten()
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
        // v50 `[value; n]`: its one embedded type is the `Array(e, n)` it builds (the element
        // `TyId` inside is remapped like every other array position); its operand is a
        // register.
        | Inst::ArraySplat { ty, .. }
        | Inst::Undef { ty }
        | Inst::Copy { ty, .. }
        | Inst::Select { ty, .. }
        // Trust (step 2 increment 4b, owner ruling D18 OD-1): a v47 drop embeds the dropped
        // place's type, remapped like every other position. Every drop is judged as an event
        // against rustc's drop elaboration by the effect-conservation gate (`drop_oracle.rs`),
        // and every executing consumer still refuses `Inst::Drop` by name.
        | Inst::Drop { ty, .. } => vec![ty],
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
        Inst::MakeClosure { .. } => vec![],
        Inst::Br { .. }
        | Inst::CondBr { .. }
        | Inst::Switch { .. }
        | Inst::Call { .. }
        | Inst::CallIndirect { .. }
        | Inst::Return { .. }
        | Inst::Assume { .. }
        // A siteless assert embeds no id (trust-ir v52 kind operands are registers). A SITED one
        // (v54) names its panic entry (`FuncId`) and possibly a location `GlobalId`, which no
        // pass of the splice remaps: unmodeled, so refused.
        | Inst::Assert { site: None, .. }
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
        // v50 `[value; n]`: its one embedded type is the `Array(e, n)` it builds (the element
        // `TyId` inside is remapped like every other array position); its operand is a
        // register.
        | Inst::ArraySplat { ty, .. }
        | Inst::Undef { ty }
        | Inst::Copy { ty, .. }
        | Inst::Select { ty, .. }
        // Trust (step 2 increment 4b, owner ruling D18 OD-1): a v47 drop embeds the dropped
        // place's type, remapped like every other position. Every drop is judged as an event
        // against rustc's drop elaboration by the effect-conservation gate (`drop_oracle.rs`),
        // and every executing consumer still refuses `Inst::Drop` by name.
        | Inst::Drop { ty, .. } => vec![ty],
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
        Inst::MakeClosure { .. } => vec![],
        Inst::Br { .. }
        | Inst::CondBr { .. }
        | Inst::Switch { .. }
        | Inst::Call { .. }
        | Inst::CallIndirect { .. }
        | Inst::Return { .. }
        | Inst::Assume { .. }
        // Lockstep: a sited assert (trust-ir v54) is refused, as above.
        | Inst::Assert { site: None, .. }
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
/// A full FILE TABLE is not a producer bug but the assembled module's own limit (trust-ir D1b:
/// the door refuses, never panics), and the body is refused with it.
fn remap_node_span(
    node: &mut InstrNode,
    files: &[String],
    module: &mut Module,
) -> Result<(), SpliceRefusal> {
    let Some(sp) = node.span else { return Ok(()) };
    node.span = match files.get(sp.file as usize) {
        Some(path) => Some(SourceSpan {
            file: module.intern_file(path.as_str()).map_err(|_| SpliceRefusal::ModuleTable)?,
            ..sp
        }),
        None => None,
    };
    Ok(())
}

/// Trust (C2-scopes): the scope table's spans carry file ids from the SAME per-body table
/// as instruction spans, so they need the same re-interning — a scope left pointing at the
/// mini-module's index would name a different file (or none) once assembled. The topology
/// (`parent`) is index-into-this-function and needs no remap. Dangling ids drop the span
/// and KEEP the scope: losing a location costs a debugger one line number, losing the entry
/// would renumber every later scope and invalidate every node index pointing past it. A full
/// file table refuses the body, as in [`remap_node_span`].
fn remap_func_scopes(
    func: &mut Function,
    files: &[String],
    module: &mut Module,
) -> Result<(), SpliceRefusal> {
    let Some(scopes) = func.scopes.as_mut() else { return Ok(()) };
    for sc in scopes.iter_mut() {
        let Some(sp) = sc.span else { continue };
        sc.span = match files.get(sp.file as usize) {
            Some(path) => Some(SourceSpan {
                file: module.intern_file(path.as_str()).map_err(|_| SpliceRefusal::ModuleTable)?,
                ..sp
            }),
            None => None,
        };
    }
    Ok(())
}

/// Trust (#174): a node in a body's enum+struct definition DAG, for the topological intern in
/// [`prepare_body_tables`].
///
/// Trust (2026-09-23): `Ty(k)` is types-table entry `k` when a definition FIELD names it
/// through a first-class `Ty::Array(k, _)`. Every fixed-size array is first-class now, so a
/// struct field `[(S, u8); 2]` names an entry `(S, u8)` that itself names struct `S`: the entry
/// must intern AFTER `S` and BEFORE the struct holding the field, which is exactly a DAG edge
/// in each direction. (Under the old `Ty::Tuple([T; N])` spelling the field carried `(S, u8)`
/// inline and needed no node.) Only entries reached from a definition become nodes; every
/// other entry keeps interning after both def tables, as before.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum DefNode {
    Enum(usize),
    Struct(usize),
    Ty(usize),
}

/// Collect the enum/struct definitions that `ty` names, appending to `out`.
///
/// FAIL-CLOSED BY OMISSION, deliberately: if a `Ty` variant that carries an `EnumId`/`StructId`
/// is missing from this walk, the topological order may intern its def too early, and
/// `remap_ty` then finds a `None` and DECLINES the body. A miss costs coverage, never
/// correctness — which is why this mirrors `remap_ty`'s recursive structure rather than trying
/// to be clever. `Ty::Closure`/`Ty::FatPtr(Slice)` name the closure / TYPES tables, which
/// intern strictly after both def tables, so they are not DAG nodes here; a def field naming
/// one already declines in `remap_ty` against the empty maps, exactly as before. A first-class
/// `Ty::Array(k, _)` IS a node, `DefNode::Ty(k)` (see [`DefNode`]): its entry interns in
/// dependency order with the defs.
fn collect_def_refs(ty: &Ty, out: &mut Vec<DefNode>) {
    match ty {
        Ty::Enum(e) => out.push(DefNode::Enum(e.as_usize())),
        Ty::Struct(sid) => out.push(DefNode::Struct(sid.as_usize())),
        Ty::Array(k, _) => out.push(DefNode::Ty(k.as_usize())),
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

/// The DAG edges out of one definition node: every enum/struct (and array types entry) its field
/// types name — or, for a types entry, that the entry itself names.
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
        DefNode::Ty(k) => collect_def_refs(r.types.get(k)?, out),
    }
    Some(())
}

/// The final, unconditional Trust-IR well-formedness authority boundary.
///
/// This is intentionally separate from artifact rendering: a compile with no dump request must
/// fail on the same invalid module as a compile that publishes bytes. Debug events retain the
/// scorecard's stable class/detail/summary protocol, but tracing controls only observation, never
/// whether validation executes or whether an error is fatal.
/// Candidate functions for a block-scoped validation error, resolved from the module.
///
/// `ValidationError::ReturnTypeMismatch` carries `block: u32` and two rendered sorts
/// and NO function identity, while block ids are PER-FUNCTION — `BlockId(0)` is the
/// entry block of very nearly every function in the module. So a finalization failure
/// on a real crate reads
///
/// ```text
/// ReturnTypeMismatch { block: 0, expected: "struct.29", actual: "()" }
/// ```
///
/// five times over and names nothing anyone can open. Measured on nn-core: the run
/// that produces it takes ~55 minutes and this is the whole of what it tells you,
/// because the check fires at FINAL module validation, after every per-function
/// analysis has already been paid for.
///
/// The identity is recoverable here, where the assembled module is in hand: a
/// candidate is a function that has that block and returns from it. Exact when one
/// function qualifies; an explicit candidate list when several do; and SILENT when
/// none do — a guess dressed as an identification is worse than the bare error,
/// which is the failure mode this whole file is careful about elsewhere.
///
/// Fixing it at the source (threading the `Function` into the error, where the
/// validator already has it in scope) means a `trust-ir` release and a pin bump;
/// this is the same information without moving the submodule.
///
/// A candidate must also DECLARE the return type the error expected (its function
/// type's returns render `expected`), the slot the validator compared against.
/// MEASURED 2026-10-19 on `core` (1.101 stage 1): `ReturnTypeMismatch { block: 0,
/// expected: "struct.13", actual: "!" }` listed 18807 candidates, every function with
/// a `ret` in its entry block, which names nothing. A candidate is named by its def
/// path when it has one (`<symbol> (<def path>)`): since WS5.2 the name is the link
/// symbol, and a reserved initializer symbol (`__trust_init_..`) says nothing.
fn functions_returning_in_block(module: &Module, block: u32, expected: &str) -> Vec<String> {
    module
        .functions
        .iter()
        .filter(|function| {
            module
                .func_type(function.ty)
                .is_some_and(|ty| ty.returns.iter().any(|slot| format!("{slot}") == expected))
                && function.blocks.iter().any(|candidate| {
                    candidate.id.index() == block
                        && candidate
                            .body
                            .iter()
                            .any(|node| matches!(node.inst, Inst::Return { .. }))
                })
        })
        .map(|function| match &function.display_path {
            Some(path) => format!("{} ({path})", function.name),
            None => function.name.clone(),
        })
        .collect()
}

/// Functions carrying `block` whose body contains the named operation.
///
/// `OperandTypeMismatch` reports the op as snake_case (`"insert_field"`), while
/// the IR spells it `Inst::InsertField`, so match the Debug prefix. This is the
/// same #189 family as the return-position case and equally anonymous: ny fails
/// with eight rows of
/// `OperandTypeMismatch { block: 0, op: "insert_field", expected: "struct.9",
/// actual: "()" }` and no function named anywhere in them.
/// Functions whose block `block` contains a direct call to `callee`.
///
/// The companion of [`functions_returning_in_block`] for the call family. The
/// callee is matched by NAME, resolved through the module's function table from
/// the `FuncId` the instruction actually carries — not by string-matching a
/// debug rendering, which would silently stop matching the first time
/// `Inst`'s `Debug` shape changed.
///
/// Falls back to naming every function that merely HAS that block id when the
/// callee cannot be resolved (a `CalleeNotFound` module would be exactly that
/// case), because a list of candidates is still incomparably better than the
/// empty string this used to return.
fn functions_calling_in_block<'m>(module: &'m Module, block: u32, callee: &str) -> Vec<&'m str> {
    let callee_id = module
        .functions
        .iter()
        .find(|function| function.name == callee)
        .map(|function| function.id);
    module
        .functions
        .iter()
        .filter(|function| {
            function.blocks.iter().any(|candidate| {
                candidate.id.index() == block
                    && candidate.body.iter().any(|node| match &node.inst {
                        Inst::Call { callee: id, .. } => {
                            callee_id.is_none_or(|want| *id == want)
                        }
                        _ => false,
                    })
            })
        })
        .map(|function| function.name.as_str())
        .collect()
}

fn functions_with_op_in_block<'m>(module: &'m Module, block: u32, op: &str) -> Vec<&'m str> {
    let camel: String = op
        .split('_')
        .map(|word| {
            let mut chars = word.chars();
            match chars.next() {
                Some(first) => first.to_uppercase().collect::<String>() + chars.as_str(),
                None => String::new(),
            }
        })
        .collect();
    module
        .functions
        .iter()
        .filter(|function| {
            function.blocks.iter().any(|candidate| {
                candidate.id.index() == block
                    && candidate
                        .body
                        .iter()
                        .any(|node| format!("{:?}", node.inst).starts_with(&camel))
            })
        })
        .map(|function| function.name.as_str())
        .collect()
}

/// Name the candidate functions for a block-scoped mismatch, when the module has any.
fn locate_validation_error(module: &Module, error: &trust_ir_build::ValidationError) -> String {
    let candidates = match error {
        trust_ir_build::ValidationError::ReturnTypeMismatch { block, expected, .. } => {
            functions_returning_in_block(module, *block, expected)
        }
        // Trust (2026-09-22, diagnostic locality for the struct table). A struct-scoped layout
        // error names an ID into the CRATE module's struct table and nothing else — and that
        // table is assembled here, at the splice, so the number means nothing to the reader
        // of the crate's source. MEASURED 2026-09-22: ay-sat's lib test target reported
        // `StructLayoutInconsistent { struct_id: 282, reason: "declared layout is incoherent
        // (...)" }` and `struct_id: 777`, ay-tla-bridge `struct_id: 32`; attributing them to
        // `core::cell::UnsafeCell<&mut dyn FnMut() -> bool>` took a day of isolated repros
        // that the struct's NAME would have made a one-line grep. The name is the producer's
        // own instantiation-qualified `def_path_str_with_args` (see `register_struct`), so
        // it is a real type the reader can look up.
        trust_ir_build::ValidationError::StructLayoutInconsistent { struct_id, .. }
        | trust_ir_build::ValidationError::TargetScalarLayoutUnavailable { struct_id, .. }
        | trust_ir_build::ValidationError::PackedReprInvalidAlign { struct_id, .. }
        | trust_ir_build::ValidationError::TransparentReprFieldCount { struct_id, .. } => {
            return match module.structs.iter().find(|sd| sd.id.index() == *struct_id) {
                Some(sd) => format!(" in struct `{}`", sd.name),
                None => String::new(),
            };
        }
        trust_ir_build::ValidationError::OperandTypeMismatch { block, op, .. } => {
            functions_with_op_in_block(module, *block, op).into_iter().map(String::from).collect()
        }
        // Trust (diagnostic locality). A call-shaped validation error names the
        // CALLEE and a block index, and nothing else. That is not enough to act
        // on: `finalize_and_dump` validates the whole CRATE module, so the
        // reader is told "some function's block 1 calls `X` with the wrong
        // argument" across every body in the crate.
        //
        // MEASURED 2026-09-07 on `first-party/ty`'s `tla-im` (663 verified
        // functions): the crate failed with
        //
        //   final Trust-IR module validation failed [CallArgTypeMismatch]:
        //   CallArgTypeMismatch { block: 1, callee: "nodes::rrb::Size::size",
        //   arg_index: 0, expected: "ptr", actual: "()" }
        //
        // carrying no span and no caller, and rustc's error carried no span
        // either. Two of these variants were already located here; the call
        // family — the one a producer change is most likely to break — was not.
        //
        // A direct `Inst::Call` records the callee as a `FuncId`, so the callee
        // NAME is recovered through the module's own function table rather than
        // by string-matching the debug rendering.
        trust_ir_build::ValidationError::CallArgTypeMismatch { block, callee, .. }
        | trust_ir_build::ValidationError::CallArgCountMismatch { block, callee, .. } => {
            functions_calling_in_block(module, *block, callee).into_iter().map(String::from).collect()
        }
        _ => return String::new(),
    };
    match candidates {
        candidates if candidates.is_empty() => String::new(),
        candidates if candidates.len() == 1 => format!(" in `{}`", candidates[0]),
        candidates => format!(
            " in one of {} candidate functions: {}",
            candidates.len(),
            candidates.join(", ")
        ),
    }
}

pub(crate) fn final_module_validation_errors(module: &Module) -> Vec<String> {
    let validation_errors = trust_ir_build::validate_module(module);
    if tracing::enabled!(tracing::Level::DEBUG) {
        let mut by_class: BTreeMap<String, u64> = BTreeMap::new();
        for error in &validation_errors {
            *by_class.entry(validation_error_class(error)).or_default() += 1;
        }
        for (class, n) in by_class {
            tracing::debug!(class = %class, n, "trust-ir-lower: module validation error");
        }
        for error in &validation_errors {
            tracing::debug!(detail = ?error, "trust-ir-lower: module validation detail");
        }
        tracing::debug!(
            total = validation_errors.len(),
            "trust-ir-lower: module validation summary"
        );
    }
    let mut errors: Vec<String> = validation_errors
        .into_iter()
        .map(|error| {
            format!(
                "final Trust-IR module validation failed [{}]{}: {error:?}{}",
                validation_error_class(&error),
                locate_validation_error(module, &error),
                validation_type_context::for_error(module, &error)
            )
        })
        .collect();

    // `Module::function_by_name` and codegen's known-fn-pointer resolution are first-match.
    // Therefore duplicate names are not cosmetic metadata: they make an otherwise ID-addressed
    // module operationally ambiguous. trust-ir's structural validator does not reject them yet,
    // so keep this producer boundary closed until that invariant moves into the shared validator.
    let mut by_name: BTreeMap<&str, Vec<FuncId>> = BTreeMap::new();
    for function in &module.functions {
        by_name.entry(&function.name).or_default().push(function.id);
    }
    for (name, ids) in by_name {
        if ids.len() > 1 {
            errors.push(format!(
                "final Trust-IR module validation failed [DuplicateFunctionName]: name={name:?} \
                 ids={ids:?}"
            ));
        }
    }
    errors
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

#[cfg(test)]
mod final_module_validation_gate_tests {
    use super::*;

    fn void_body(id: u32, name: String, ty: FuncTyId, callee: Option<FuncId>) -> Function {
        let mut function = Function::new(FuncId::new(id), name, ty, BlockId::new(0));
        let mut block = trust_ir::Block::new(BlockId::new(0));
        if let Some(callee) = callee {
            block.body.push(InstrNode::new(Inst::Call { callee, args: Vec::new() }));
        }
        block.body.push(InstrNode::new(Inst::Return { values: Vec::new() }));
        function.blocks.push(block);
        function
    }

    fn one_return_module(return_ty: Ty, value_ty: Ty) -> Module {
        let mut module = Module::new("final_validation_probe");
        let func_ty = module
            .add_func_type(FuncTy {
                params: Vec::new(),
                returns: vec![return_ty],
                is_vararg: false,
                abi: None,
            })
            .expect("Module::add_func_type: test fixture");
        let mut function = Function::new(FuncId::new(0), "probe", func_ty, BlockId::new(0));
        let mut block = trust_ir::Block::new(BlockId::new(0));
        block.body.push(
            InstrNode::new(Inst::Const { ty: value_ty, value: Constant::Int(1) })
                .with_result(ValueId::new(0)),
        );
        block.body.push(InstrNode::new(Inst::Return {
            values: vec![ValueId::new(0)],
        }));
        function.blocks.push(block);
        module.try_add_function(function).expect("Module::try_add_function: test fixture");
        module
    }

    #[test]
    fn final_validator_rejects_a_return_type_mismatch_and_accepts_its_twin() {
        let invalid = final_module_validation_errors(&one_return_module(Ty::I64, Ty::I32));
        assert!(
            invalid.iter().any(|error| error.contains("ReturnTypeMismatch")),
            "the final semantic gate must surface the validator class: {invalid:?}"
        );
        assert!(
            final_module_validation_errors(&one_return_module(Ty::I32, Ty::I32)).is_empty(),
            "the close well-typed twin must pass"
        );
    }

    #[test]
    fn a_return_type_mismatch_names_the_function_it_is_in() {
        // `ValidationError::ReturnTypeMismatch` carries `block: u32` and two
        // rendered sorts and no function identity, and block ids are
        // PER-FUNCTION, so `block: 0` is the entry block of nearly everything in
        // the module. On nn-core that produced five rows reading
        // `ReturnTypeMismatch { block: 0, expected: "struct.29", actual: "()" }`
        // after a ~55 minute run and named nothing anyone could open.
        let errors = final_module_validation_errors(&one_return_module(Ty::I64, Ty::I32));
        let mismatch = errors
            .iter()
            .find(|error| error.contains("ReturnTypeMismatch"))
            .expect("the fixture must produce a ReturnTypeMismatch");
        assert!(
            mismatch.contains("`probe`"),
            "the mismatch must name the function it is in: {mismatch}"
        );
    }

    #[test]
    fn a_module_with_no_returning_function_claims_no_identification() {
        // Silence beats a guess: if no function in the module returns from that
        // block, the error is left exactly as the validator wrote it rather than
        // decorated with a candidate that may not be the culprit.
        let mut module = Module::new("no_candidate_probe");
        let ty = module
            .add_func_type(FuncTy {
                params: Vec::new(),
                returns: Vec::new(),
                is_vararg: false,
                abi: None,
            })
            .expect("Module::add_func_type: test fixture");
        module
            .try_add_function(Function::new(FuncId::new(0), "empty", ty, BlockId::new(0)))
            .expect("Module::try_add_function: test fixture");
        assert_eq!(
            locate_validation_error(
                &module,
                &trust_ir_build::ValidationError::ReturnTypeMismatch {
                    block: 0,
                    expected: "struct.29".to_string(),
                    actual: "()".to_string(),
                },
            ),
            ""
        );
    }

    #[test]
    fn final_validator_rejects_duplicate_function_names() {
        let mut module = Module::new("duplicate_function_name_probe");
        let ty = module
            .add_func_type(FuncTy {
                params: Vec::new(),
                returns: Vec::new(),
                is_vararg: true,
                abi: None,
            })
            .expect("Module::add_func_type: test fixture");
        module
            .try_add_function(Function::new(FuncId::new(0), "same", ty, BlockId::new(0)))
            .expect("Module::try_add_function: test fixture");
        module
            .try_add_function(Function::new(FuncId::new(1), "same", ty, BlockId::new(0)))
            .expect("Module::try_add_function: test fixture");

        let errors = final_module_validation_errors(&module);
        assert!(
            errors.iter().any(|error| {
                error.contains("[DuplicateFunctionName]")
                    && error.contains("FuncId(0)")
                    && error.contains("FuncId(1)")
            }),
            "name-based consumers are first-match, so duplicate names must fail closed: \
             {errors:?}"
        );
    }

    #[test]
    fn assembled_codegen_handoff_selects_collision_renamed_callers_by_exact_identity() {
        let first = crate::lineage::DefinitionIdentity::test_only(0xC0DE, 10);
        let second = crate::lineage::DefinitionIdentity::test_only(0xC0DE, 11);
        let helper = crate::lineage::DefinitionIdentity::test_only(0xC0DE, 12);
        let mut module = Module::new("assembled_codegen_identity_probe");
        let ty = module
            .add_func_type(FuncTy {
                params: Vec::new(),
                returns: Vec::new(),
                is_vararg: false,
                abi: None,
            })
            .expect("Module::add_func_type: test fixture");
        module
            .try_add_function(void_body(
                0,
                format!("!trust_definition::probe::same::{}", first.symbol_suffix()),
                ty,
                Some(FuncId::new(2)),
            ))
            .expect("Module::try_add_function: test fixture");
        module
            .try_add_function(void_body(
                1,
                format!("!trust_definition::probe::same::{}", second.symbol_suffix()),
                ty,
                Some(FuncId::new(2)),
            ))
            .expect("Module::try_add_function: test fixture");
        module
            .try_add_function(void_body(2, "probe::helper".to_string(), ty, None))
            .expect("Module::try_add_function: test fixture");

        let handoff = crate::AssembledCrateModuleForCodegen::checked(
            std::sync::Arc::new(module),
            vec![
                (40, first, FuncId::new(0)),
                (41, second, FuncId::new(1)),
                (42, helper, FuncId::new(2)),
            ],
        )
        .expect("three exact definition mappings");

        assert_eq!(handoff.lookup_exact(40, first), Some(FuncId::new(0)));
        assert_eq!(handoff.lookup_exact(41, second), Some(FuncId::new(1)));
        assert_eq!(handoff.lookup_exact(42, helper), Some(FuncId::new(2)));
        assert_eq!(
            handoff.lookup_exact(40, second),
            None,
            "a matching display-path class may not substitute for exact identity"
        );
        assert_eq!(
            handoff.lookup_exact(41, first),
            None,
            "DefIndex and stable definition identity are a conjunctive key"
        );
    }

    #[test]
    fn assembled_codegen_handoff_refuses_missing_and_bodyless_targets() {
        let identity = crate::lineage::DefinitionIdentity::test_only(0xC0DE, 20);
        let mut missing = Module::new("missing_target");
        missing
            .add_func_type(FuncTy {
                params: Vec::new(),
                returns: Vec::new(),
                is_vararg: false,
                abi: None,
            })
            .expect("Module::add_func_type: test fixture");
        let error = crate::AssembledCrateModuleForCodegen::checked(
            std::sync::Arc::new(missing),
            vec![(50, identity, FuncId::new(0))],
        )
        .err()
        .expect("missing target must be refused");
        assert!(error.contains("missing FuncId(0)"), "{error}");

        let mut bodyless = Module::new("bodyless_target");
        let ty = bodyless
            .add_func_type(FuncTy {
                params: Vec::new(),
                returns: Vec::new(),
                is_vararg: false,
                abi: None,
            })
            .expect("Module::add_func_type: test fixture");
        bodyless
            .try_add_function(Function::new(FuncId::new(0), "decl", ty, BlockId::new(0)))
            .expect("Module::try_add_function: test fixture");
        let error = crate::AssembledCrateModuleForCodegen::checked(
            std::sync::Arc::new(bodyless),
            vec![(50, identity, FuncId::new(0))],
        )
        .err()
        .expect("bodyless target must be refused");
        assert!(error.contains("bodyless FuncId(0)"), "{error}");
    }

    // Plan step 3.4: `assembled_codegen_handoff_refuses_clean_origin_rows` (which pinned that the
    // handoff never indexes a Clean row) is replaced by the ledger tests in
    // `crate_module/carrier_ledger_tests.rs`: a gated, authenticated row is indexed, every other
    // Clean row is not, and a forged stamp, an edited row or another Session's ledger refuses.

    #[test]
    fn clean_thir_overlap_is_keyed_by_source_identity_not_emitted_name() {
        let assigned = vec![(30, FuncId::new(0))];
        let emitted = crate::clean_origin_join::EmittedRow {
            def_index: 30,
            def_path: "main::CONST_EVAL::{constant#0}".to_string(),
            clean_name: "Clean.constEval".to_string(),
            shape: "probe",
            func_id: 1,
            tier: crate::clean_origin_join::CleanOriginTier::Structural,
            gate_subject_digest: None,
            gate_carrier: None,
            gate_method: None,
            gate_environment_digest: None,
            gate_kernel_version: None,
            gate_ledger_digest: None,
            tv_note: None,
        };
        let errors = clean_origin_thir_overlap_errors(&assigned, std::slice::from_ref(&emitted));
        assert_eq!(errors.len(), 1, "the same DefIndex must fail even after THIR name mangling");
        assert!(errors[0].contains("def index 30"));

        let disjoint = vec![(31, FuncId::new(0))];
        assert!(clean_origin_thir_overlap_errors(&disjoint, &[emitted]).is_empty());
    }

    #[test]
    fn final_validator_is_after_all_joins_and_before_serialization() {
        let source = include_str!("crate_module.rs");
        let production = source
            .split_once("#[cfg(test)]\nmod final_module_validation_gate_tests")
            .map(|(production, _)| production)
            .expect("final validation test-module boundary");
        let obligation_gate = production
            .find("errors.extend(crate::direct_obligations::inventory_errors_at_tier(")
            .expect("direct-obligation inventory gate");
        let final_gate = production
            .find("errors.extend(final_module_validation_errors(&assembled.module));")
            .expect("unconditional final validation call");
        // WS5.23: the artifacts are rendered (and the text companion guarded)
        // through `render_publication_bytes`, the one serialization site.
        let serialization = production
            .find("render_publication_bytes(&assembled.module)")
            .expect("artifact serialization");
        assert!(
            obligation_gate < final_gate && final_gate < serialization,
            "final validation must cover obligations/Clean joins and precede every serialization"
        );
        assert_eq!(
            production
                .matches("errors.extend(final_module_validation_errors(&assembled.module));")
                .count(),
            1,
            "there must be one unconditional final authority boundary"
        );
        // WS5.23 review (2026-09-28): the F-099 guard is only a guard if it cannot be
        // walked around. `render_publication_bytes` is the ONE place the assembled module
        // is serialized, its refusal WITHHOLDS the artifact set (it joins
        // `publication_errors`, which blocks the commit marker) rather than falling back
        // to unguarded bytes, and nothing else in production serializes a module to either
        // artifact format. The raw-call needles are assembled from pieces so no test
        // source can satisfy or break them.
        assert_eq!(
            production.matches("render_publication_bytes(&assembled.module)").count(),
            1,
            "the guarded renderer must be the one serialization site of the assembled module"
        );
        let squashed = production.split_whitespace().collect::<Vec<_>>().join(" ");
        assert!(
            squashed.contains(
                "Ok(coverage) => match render_publication_bytes(&assembled.module) { \
                 Ok((bin, txt)) => rendered = Some((coverage, bin, txt)), \
                 Err(error) => publication_errors.push(error), },"
            ),
            "a text-companion refusal must join `publication_errors` (withholding the set), \
             never be dropped or replaced by unguarded bytes"
        );
        for raw in [["binary::", "serialize_module("].concat(), ["format::", "canonical("].concat()]
        {
            assert!(
                !production.contains(raw.as_str()),
                "production serializes a module with `{raw}` outside `render_publication_bytes` \
                 — a publication path that bypasses the F-099 guard"
            );
        }
        // WS5.23 landing review (2026-09-28, batch owner): the loop above reads only the
        // PREFIX before this test module, and ~900 lines of production code follow it (the
        // splice helpers, the coverage writer, the guard itself) — a raw serialization there was
        // invisible to it, so "nothing else in production serializes a module" was broader
        // than what this test enforced. The whole-file scan below closes that, and adds the
        // structural half: every published artifact's bytes are the guarded pair or the
        // coverage marker, and `rendered` is filled only by the guarded arm.
        let bypasses = publication_bypasses(source);
        assert!(
            bypasses.is_empty(),
            "the F-099 guard can be walked around:\n{}",
            bypasses.join("\n")
        );
    }

    /// WS5.23 landing review (2026-09-28): the lines the publication-bypass scan reads —
    /// every line of `source` that is PRODUCTION code, with its 1-based number. Removed:
    /// comment lines; the guard's own two functions (`render_publication_bytes`,
    /// `check_text_companion_is_canonical`, the one place a raw serialization is the point);
    /// and every top-level `#[cfg(test)]` item this scan can POSITIVELY delimit — a `mod x;`
    /// line, a one-line `fn`, or a `mod x {` / `fn` block that trustfmt closes with a
    /// column-0 `}`. Any other `#[cfg(test)]` item is read as production: an item the scan
    /// cannot delimit costs a false alarm, never a hidden line (fail closed).
    fn publication_scan_lines(source: &str) -> Vec<(usize, &str)> {
        const GUARDS: [&str; 2] = [
            "pub(crate) fn render_publication_bytes(",
            "pub(crate) fn check_text_companion_is_canonical(",
        ];
        fn item(line: &str) -> &str {
            line.strip_prefix("pub(crate) ").or_else(|| line.strip_prefix("pub ")).unwrap_or(line)
        }
        fn is_file_mod(line: &str) -> bool {
            item(line)
                .strip_prefix("mod ")
                .and_then(|rest| rest.strip_suffix(';'))
                .is_some_and(|name| {
                    !name.is_empty() && name.chars().all(|c| c.is_alphanumeric() || c == '_')
                })
        }
        fn is_block_item(line: &str) -> bool {
            let item = item(line);
            (item.starts_with("mod ") && item.ends_with(" {")) || item.starts_with("fn ")
        }
        let lines: Vec<&str> = source.lines().collect();
        // The index of the column-0 `}` closing the block item that starts at `start`, if any.
        let close = |start: usize| (start + 1..lines.len()).find(|&j| lines[j] == "}");
        let mut kept = Vec::new();
        let mut i = 0;
        while i < lines.len() {
            let line = lines[i];
            if line == "#[cfg(test)]" {
                let mut at = i + 1;
                while lines.get(at).is_some_and(|l| l.starts_with("#[")) {
                    at += 1;
                }
                let next = lines.get(at).copied().unwrap_or("");
                if is_file_mod(next) || (item(next).starts_with("fn ") && next.ends_with('}')) {
                    i = at + 1;
                    continue;
                }
                if is_block_item(next) {
                    if let Some(end) = close(at) {
                        i = end + 1;
                        continue;
                    }
                }
            } else if GUARDS.iter().any(|guard| line.starts_with(guard)) {
                if let Some(end) = close(i) {
                    i = end + 1;
                    continue;
                }
            }
            if !line.trim_start().starts_with("//") {
                kept.push((i + 1, line));
            }
            i += 1;
        }
        kept
    }

    /// Does `code` name the canonical renderer as an identifier (a bare call, or an import
    /// list entry), as opposed to the word in prose?
    fn names_canonical(code: &str) -> bool {
        let word = "canonical";
        code.match_indices(word).any(|(at, _)| {
            let ident = |c: char| c.is_alphanumeric() || c == '_';
            let tail = &code[at + word.len()..];
            let after = tail.trim_start();
            !code[..at].chars().next_back().is_some_and(ident)
                && !tail.starts_with(ident)
                && (after.starts_with(['(', ',', '}', ';']) || after.starts_with("as "))
        })
    }

    /// Does `code` bind a pattern named `bin` or `txt` — the names the guarded bytes travel
    /// under from `rendered` to the artifact set?
    fn rebinds_guarded_bytes(code: &str) -> bool {
        code.split("let ").skip(1).any(|rest| {
            rest.split(['=', ':'])
                .next()
                .unwrap_or("")
                .split(|c: char| !(c.is_alphanumeric() || c == '_'))
                .any(|word| word == "bin" || word == "txt")
        })
    }

    /// Every way the production lines of `source` walk around the F-099 guard: a raw
    /// module serialization or canonical rendering outside `render_publication_bytes`; a
    /// published `Artifact` whose bytes are not the guarded `bin` / `txt` pair or the
    /// `&coverage` marker; a `publish` of anything but that artifact set; the guarded names
    /// rebound; or `rendered` filled anywhere but the guarded arm.
    fn publication_bypasses(source: &str) -> Vec<String> {
        // Assembled from pieces, like the needles above: this module's text is skipped by
        // the scan, and a needle spelled whole would still read as a call to a reader.
        let serialize = ["serialize", "_module"].concat();
        let deserialize = ["de", "serialize", "_module"].concat();
        let canonical_path = ["format", "::canonical"].concat();
        let artifact = ["Artifact", " {"].concat();
        let publish = [".publish", "("].concat();
        let guarded_publish = [".publish", "(&artifacts)"].concat();
        let rendered_some = ["rendered", " = Some("].concat();
        let mut found = Vec::new();
        let mut fills = Vec::new();
        for (n, line) in publication_scan_lines(source) {
            let code = line.replace(deserialize.as_str(), "");
            let shown = line.trim();
            if code.contains(serialize.as_str()) {
                found.push(format!("line {n}: a raw module serialization outside the guard: `{shown}`"));
            }
            if code.contains(canonical_path.as_str()) || names_canonical(&code) {
                found.push(format!("line {n}: the canonical renderer outside the guard: `{shown}`"));
            }
            if let Some(at) = code.find(artifact.as_str()) {
                let bytes = code[at..]
                    .split_once("bytes: ")
                    .and_then(|(_, rest)| rest.split_once(" }"))
                    .map(|(bytes, _)| bytes.trim());
                if !matches!(bytes, Some("bin" | "txt" | "&coverage")) {
                    found.push(format!(
                        "line {n}: a published artifact whose bytes are not the guarded pair \
                         or the coverage marker: `{shown}`"
                    ));
                }
            }
            if code.contains(publish.as_str()) && !code.contains(guarded_publish.as_str()) {
                found.push(format!("line {n}: a publish of something other than the guarded artifact set: `{shown}`"));
            }
            if rebinds_guarded_bytes(&code) {
                found.push(format!("line {n}: rebinds the guarded bytes' names (`bin` / `txt`): `{shown}`"));
            }
            if code.contains(rendered_some.as_str()) {
                fills.push(n);
            }
        }
        if fills.len() != 1 {
            found.push(format!(
                "`rendered` must be filled exactly once, by the guarded arm; filled at lines {fills:?}"
            ));
        }
        found
    }

    /// WS5.23 landing review (2026-09-28): the whole-file scan against the walk-arounds it
    /// exists to catch, and the lines it must leave alone. Every mutant is the REAL source
    /// with one edit, so the scan is exercised on exactly the text it guards.
    #[test]
    fn publication_bypass_scan_catches_every_walk_around_and_nothing_else() {
        let source = crate::source_scan::sibling_source("crate_module.rs");
        let clean = publication_bypasses(source);
        assert!(clean.is_empty(), "the real source must scan clean: {clean:#?}");
        let flagged = |label: &str, text: &str, needle: &str| {
            let found = publication_bypasses(text);
            assert!(
                found.iter().any(|f| f.contains(needle)),
                "{label}: the scan must report `{needle}`; it reported {found:#?}"
            );
        };
        let passes = |label: &str, text: &str| {
            let found = publication_bypasses(text);
            assert!(found.is_empty(), "{label}: a false alarm: {found:#?}");
        };
        let raw_bin = ["trust_ir::binary::", "serialize", "_module(m)"].concat();
        let raw_path = ["trust_ir::binary::", "serialize", "_module"].concat();
        let leak = format!("fn leak(m: &Module) -> Vec<u8> {{\n    {raw_bin}\n}}\n");

        // (1) THE HOLE this scan closes: production code AFTER the first test module. The
        //     prefix-only check above cannot see it; the scan must.
        let after = format!("{source}\n{leak}");
        let prefix = after
            .split_once("#[cfg(test)]\nmod final_module_validation_gate_tests")
            .map(|(prefix, _)| prefix)
            .expect("boundary");
        let old_needle = ["binary::", "serialize_module("].concat();
        assert!(
            source.split_once("#[cfg(test)]\nmod final_module_validation_gate_tests").is_some()
                && !prefix.contains(old_needle.as_str()),
            "the mutant must sit past the prefix, where the prefix-only check is blind"
        );
        flagged("production after the test module", &after, "raw module serialization");
        // (2) the canonical renderer imported, then called bare.
        let bare = format!(
            "use trust_ir::format::{};\n{source}\nfn leak(m: &Module) -> String {{\n    canonical(m)\n}}\n",
            "canonical"
        );
        flagged("imported canonical", &bare, "canonical renderer");
        // (3) the canonical renderer in a multi-line import list.
        let listed = format!("use trust_ir::format::{{\n    canonical,\n}};\n{source}");
        flagged("import-list canonical", &listed, "canonical renderer");
        // (4) an artifact published from Display (the F-099 class itself) instead of `txt`.
        let display = source.replacen(
            "Artifact { name: &text_name, bytes: txt }",
            "Artifact { name: &text_name, bytes: &display }",
            1,
        );
        assert_ne!(display, source, "the anchor for mutant (4) moved");
        flagged("Display-rendered artifact", &display, "published artifact");
        // (5) `rendered` filled a second time, from anywhere.
        let refill = source.replacen(
            "    let mut prepared_publication = prepared_publication;\n",
            "    rendered = Some((String::new(), Vec::new(), Vec::new()));\n    \
             let mut prepared_publication = prepared_publication;\n",
            1,
        );
        assert_ne!(refill, source, "the anchor for mutant (5) moved");
        flagged("second fill", &refill, "filled exactly once");
        // (6) the guarded bytes shadowed between `rendered` and the artifact set.
        let shadow = source.replacen(
            "(Some((coverage_json, bin, txt)), Some(prepared)) => {\n",
            "(Some((coverage_json, bin, txt)), Some(prepared)) => {\n                \
             let txt = &display;\n",
            1,
        );
        assert_ne!(shadow, source, "the anchor for mutant (6) moved");
        flagged("shadowed bytes", &shadow, "rebinds the guarded bytes");
        // (7) a publish of a hand-built artifact list.
        let publish = format!("{source}\nfn leak(p: Prepared) {{\n    p.publish(&[]);\n}}\n");
        flagged("foreign publish", &publish, "publish of something other");
        // (8) production hidden behind an attribute-carrying `#[cfg(test)] mod x;`, and
        // (9) behind a one-line `#[cfg(test)] fn`: neither may swallow the item after it.
        let path_mod = format!("{source}\n#[cfg(test)]\n#[path = \"x.rs\"]\nmod x;\n{leak}");
        flagged("after a #[path] test mod", &path_mod, "raw module serialization");
        let one_line = format!("{source}\n#[cfg(test)]\nfn noop() {{}}\n{leak}");
        flagged("after a one-line test fn", &one_line, "raw module serialization");
        // (10) FAIL CLOSED: a `#[cfg(test)]` item the scan cannot delimit is read, not skipped.
        let undelimited =
            format!("{source}\n#[cfg(test)]\nstatic LEAK: fn(&Module) -> Vec<u8> =\n    {raw_path};\n");
        flagged("undelimited test item", &undelimited, "raw module serialization");

        // Controls: the scan must NOT report test code, comments, or the words in prose.
        let in_test = format!(
            "{source}\n#[cfg(test)]\nmod extra_tests {{\n    fn leak(m: &Module) -> Vec<u8> {{\n        \
             {raw_bin}\n    }}\n}}\n"
        );
        passes("inside a test module", &in_test);
        passes("in comments", &format!("{source}\n// {raw_bin}\n/// {raw_bin}\n"));
        passes(
            "in prose",
            &format!("{source}\nconst NOTE: &str = \"the canonical form; a canonical-text row\";\n"),
        );
    }
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
    ty_map: Vec<Option<TyId>>,
    closure_map: Vec<trust_ir::ClosureTyId>,
    /// Trust (v41 `RustAbiVararg`): body-positional `FuncTyId` -> assembled id,
    /// for a declaration whose PARAMETER is a fn pointer. `Ty::Func` holds a
    /// body-local id, so without this `remap_ty` had no arm for it and
    /// `decl_params` refused the whole signature.
    ///
    /// SPARSE AND LAZY BY DESIGN. Only the ids a declaration actually needs are
    /// interned — the ones a recorded `CalleeRef::params` signature names — so an
    /// ordinary body adds nothing to `module.func_types`. That matters because
    /// the assembled `func_types` table is SCANNED (`first_ffi_boundary`'s
    /// aggregate-at-a-boundary walk), so interning every body's whole table to
    /// serve a rare parameter would change verdicts elsewhere for no gain.
    func_map: Vec<Option<FuncTyId>>,
}

impl BodyMaps {
    /// Remap a BODY-numbered `Ty` into the assembled module's numbering. `None` (fail-closed) for
    /// an out-of-range id, a not-yet-interned def, or a variant `remap_ty` does not model.
    fn remap(&self, ty: &Ty) -> Option<Ty> {
        remap_ty_with_funcs(
            ty,
            &self.enum_map,
            &self.struct_map,
            &self.ty_map,
            &self.closure_map,
            &self.func_map,
        )
    }
}

/// The source type context of one body; no instructions are cloned.
fn body_layout_context(record: &BodyRecord) -> Module {
    let mut source = Module::new("body_layouts");
    source.target_info = record.target_info.clone();
    source.types = record.types.clone();
    source.structs = record.structs.clone();
    source.enums = record.enums.clone();
    source.func_types = record.func_types.clone();
    source.closure_types = record.closure_types.clone();
    source.tuple_layouts = record.tuple_layouts.clone();
    source.closure_layouts = record.closure_layouts.clone();
    source
}

fn prepare_body_tables(
    r: &BodyRecord,
    module: &mut Module,
    static_globals: &mut static_globals::StaticGlobals,
) -> Result<(Function, FuncTy, BodyMaps), SpliceRefusal> {
    static_globals::validate_origins(r).map_err(|_| SpliceRefusal::StaticGlobalOrigin)?;
    let layout_source = (!r.tuple_layouts.is_empty() || !r.closure_layouts.is_empty())
        .then(|| body_layout_context(r));
    if let Some(source) = &layout_source {
        source.validate_closure_layouts().map_err(|_| SpliceRefusal::ClosureLayout)?;
        module.validate_closure_layouts().map_err(|_| SpliceRefusal::ClosureLayout)?;
        if !source.closure_layouts.is_empty()
            && (source.target_info.is_none()
                || module.target_info.as_ref().is_some_and(|target| Some(target) != source.target_info.as_ref()))
        {
            return Err(SpliceRefusal::ClosureLayout);
        }
    }
    let (Some(func), Some(func_ty)) = (&r.function, &r.func_ty) else {
        return Err(SpliceRefusal::NoFunctionBody);
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
    //
    // Trust (2026-09-23): a types entry a def field names through a first-class array is a node
    // too (`DefNode::Ty`, see its doc), reached only from a def, never a start — so an entry no
    // def names keeps interning after both def tables, and a body whose def fields name only
    // table-free entries (pre-interned below, so their node is a no-op) assembles exactly as
    // before.
    let n_enums = r.enums.len();
    let n_structs = r.structs.len();
    let n_types = r.types.len();
    let total_defs = n_enums.checked_add(n_structs).ok_or(SpliceRefusal::DefTableGraph)?;
    let total_nodes = total_defs.checked_add(n_types).ok_or(SpliceRefusal::DefTableGraph)?;
    // Node numbering: enums [0, n_enums), structs [n_enums, total_defs), types entries
    // [total_defs, total_nodes).
    let node_of = |n: DefNode| match n {
        DefNode::Enum(i) => i,
        DefNode::Struct(j) => n_enums + j,
        DefNode::Ty(k) => total_defs + k,
    };
    const UNVISITED: u8 = 0;
    const ON_PATH: u8 = 1;
    const DONE: u8 = 2;
    let mut state = vec![UNVISITED; total_nodes];
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
                return Err(SpliceRefusal::DefTableGraph); // defensive: a back edge is a cycle — fail closed.
            }
            state[k] = ON_PATH;
            stack.push((n, true));
            def_node_refs(r, n, &mut refs).ok_or(SpliceRefusal::DefTableGraph)?;
            for m in refs.drain(..) {
                let mk = match m {
                    DefNode::Enum(i) if i < n_enums => node_of(m),
                    DefNode::Struct(j) if j < n_structs => node_of(m),
                    DefNode::Ty(k) if k < n_types => node_of(m),
                    // Out-of-range id: refuse the body rather than intern against a table
                    // that cannot resolve it.
                    _ => return Err(SpliceRefusal::DefTableGraph),
                };
                match state[mk] {
                    UNVISITED => stack.push((m, false)),
                    ON_PATH => return Err(SpliceRefusal::DefTableGraph), // cycle
                    _ => {}
                }
            }
        }
    }
    let mut enum_map: Vec<Option<EnumId>> = vec![None; n_enums];
    let mut struct_map: Vec<Option<StructId>> = vec![None; n_structs];
    // Trust (vtable slice 15): PRE-PASS over the types table — intern every TABLE-FREE entry
    // (a scalar array element, the wave-17 bytes element) BEFORE the def tables, so a struct
    // field's first-class `Ty::Array(TyId, N)` resolves during the def remap below. Entries
    // that reference structs/enums stay holes in this pre-pass. A qualified zero-array struct
    // element is reached through the dependency DAG below; unused entries wait for the main loop.
    // `intern_ty` dedups structurally, so re-reaching an entry later is idempotent.
    // Trust (2026-09-23): a NON-table-free entry a def field names through an array — a nested
    // array `[[u32; 2]; 2]`, an array of tuples naming a struct `[(S, u8); 2]` — is not a hole
    // at the def remap either: it is a `DefNode::Ty` in `order`, interned below after
    // everything it names and before the def that names it.
    let mut ty_map: Vec<Option<TyId>> = r
        .types
        .iter()
        .map(|t| {
            if ty_table_free(t) {
                intern_ty(module, t.clone()).map(Some).map_err(|_| SpliceRefusal::ModuleTable)
            } else {
                Ok(None)
            }
        })
        .collect::<Result<_, _>>()?;
    for n in &order {
        match *n {
            DefNode::Enum(i) => {
                let mut remapped = r.enums.get(i).ok_or(SpliceRefusal::DefTableRemap)?.clone();
                for variant in &mut remapped.variants {
                    for fty in &mut variant.fields {
                        // Trust (B3-3 + #174): a nested first-class enum field, and now a
                        // struct-payload field, both resolve through the maps — which the
                        // topological order guarantees are already filled for everything this
                        // def names.
                        *fty = remap_ty(fty, &enum_map, &struct_map, &[], &[])
                            .ok_or(SpliceRefusal::DefTableRemap)?;
                    }
                }
                enum_map[i] =
                    Some(module.add_enum_def(remapped).map_err(|_| SpliceRefusal::ModuleTable)?);
            }
            DefNode::Struct(j) => {
                let mut remapped = r.structs.get(j).ok_or(SpliceRefusal::DefTableRemap)?.clone();
                for field in &mut remapped.fields {
                    // Trust (vtable slice 15): the partial types map serves the `Ty::Array`
                    // fields `def_field_ok` admits — pre-interned table-free entries, and
                    // (2026-09-23) every other entry a field names, interned as its own
                    // `DefNode::Ty` earlier in `order`; a hole fails closed.
                    field.ty = remap_ty(&field.ty, &enum_map, &struct_map, &ty_map, &[])
                        .ok_or(SpliceRefusal::DefTableRemap)?;
                }
                struct_map[j] =
                    Some(module.add_struct_def(remapped).map_err(|_| SpliceRefusal::ModuleTable)?);
            }
            // Trust (2026-09-23): a types entry a def field names through an array. The topological
            // order put every def and earlier entry it names before it; a pre-interned table-free
            // entry is already `Some` and stays (one mint per entry, as in the main loop below).
            DefNode::Ty(k) => {
                if ty_map.get(k).ok_or(SpliceRefusal::TypeTableRemap)?.is_none() {
                    let entry = r.types.get(k).ok_or(SpliceRefusal::TypeTableRemap)?;
                    let remapped = remap_ty(entry, &enum_map, &struct_map, &ty_map, &[])
                        .ok_or(SpliceRefusal::TypeTableRemap)?;
                    ty_map[k] =
                        Some(intern_ty(module, remapped).map_err(|_| SpliceRefusal::ModuleTable)?);
                }
            }
        }
    }
    // Densify: the traversal covers every node, so a `None` here would mean the walk missed
    // one — refuse rather than let a later phase index a hole.
    let enum_map: Vec<EnumId> =
        enum_map.into_iter().collect::<Option<Vec<_>>>().ok_or(SpliceRefusal::DefTableGraph)?;
    let struct_map: Vec<StructId> =
        struct_map.into_iter().collect::<Option<Vec<_>>>().ok_or(SpliceRefusal::DefTableGraph)?;
    let enum_map: Vec<Option<EnumId>> = enum_map.into_iter().map(Some).collect();
    let struct_map: Vec<Option<StructId>> = struct_map.into_iter().map(Some).collect();
    for (j, t) in r.types.iter().enumerate() {
        // (A types entry cannot reference a closure type — `type_entry_ok` refuses it —
        // so the closure map, built AFTER this loop, is passed empty: fail-closed.)
        // Pre-interned table-free entries (slice 15 pre-pass) are already `Some` and stay:
        // re-interning would be idempotent, skipping is cheaper and keeps ids single-minted.
        if ty_map[j].is_none() {
            let remapped = remap_ty(t, &enum_map, &struct_map, &ty_map, &[])
                .ok_or(SpliceRefusal::TypeTableRemap)?;
            ty_map[j] = Some(intern_ty(module, remapped).map_err(|_| SpliceRefusal::ModuleTable)?);
        }
    }
    // Trust (B6): closure-type table — after types (a ClosureTy's captures may reference
    // structs/types entries; its `func` indexes the BODY's func_types table and is
    // re-interned into the assembled module here). Captures are table-free by the
    // producer's thin-capture gate — re-checked in `splice_ok`, remapped defensively
    // anyway (a `?`-decline refuses the body, never a guess).
    let mut closure_map: Vec<trust_ir::ClosureTyId> = Vec::with_capacity(r.closure_types.len());
    let mut closure_interner = crate::closure_layout::Interner::default();
    for (index, ct) in r.closure_types.iter().enumerate() {
        let mut ft =
            r.func_types.get(ct.func.as_usize()).ok_or(SpliceRefusal::ClosureTableRemap)?.clone();
        for t in ft.params.iter_mut().chain(ft.returns.iter_mut()) {
            *t = remap_ty(t, &enum_map, &struct_map, &ty_map, &closure_map)
                .ok_or(SpliceRefusal::ClosureTableRemap)?;
        }
        let func = intern_func_ty(module, ft).map_err(|_| SpliceRefusal::ModuleTable)?;
        let mut captures = ct.captures.clone();
        for t in captures.iter_mut() {
            *t = remap_ty(t, &enum_map, &struct_map, &ty_map, &closure_map)
                .ok_or(SpliceRefusal::ClosureTableRemap)?;
        }
        closure_map.push(
            closure_interner.intern(
                module,
                trust_ir::ClosureTy { func, captures },
                r.closure_layouts.iter().find(|row| row.closure.as_usize() == index),
            )
            .map_err(|_| SpliceRefusal::ModuleTable)?,
        );
    }
    if let Some(source) = &layout_source {
        // Thin captures have no tuple dependencies. Install their frames first
        // so a tuple containing a closure can be checked against that image.
        crate::closure_layout::merge(source, module, &closure_map)
            .map_err(|_| SpliceRefusal::ClosureLayout)?;
        crate::tuple_layout::merge(source, module, |ty| {
            remap_ty(ty, &enum_map, &struct_map, &ty_map, &closure_map)
        })
        .map_err(|error| {
            // The merge's own reason travels on the debug channel; the row carries the class.
            tracing::debug!(
                def_path = %r.def_path,
                error = %error,
                "trust-ir-lower: tuple layout merge refused a body's splice"
            );
            SpliceRefusal::TupleLayout
        })?;
    }
    // Globals last, after their type tables. Rust statics intern by compiler
    // DefId; body-local promotions remain distinct. The append-only registry
    // always points at valid initialized globals, even after a later unrelated
    // body-remap refusal. No growing Module clone or rollback-sensitive index.
    let mut global_map: Vec<GlobalId> = Vec::with_capacity(r.globals.len());
    for (g, origin) in r.globals.iter().zip(&r.global_origins) {
        if !global_spliceable(r, g) {
            return Err(SpliceRefusal::GlobalShape);
        }
        let mut g = g.clone();
        // Trust (wave-17): a bytes `Ty::Array(TyId, N)` global's element `TyId` indexes the body's
        // types table — remap it to the assembled module's interned id (the `ty_map` built above,
        // globals come after the types loop). A wave-16 SCALAR global's `ty` is table-free, so this
        // is a no-op there. `?`-decline (an out-of-range id) refuses the body, consistent with the
        // enum/struct/type table remaps; `splice_ok` already validated the id, so it never fires.
        g.ty = remap_ty(&g.ty, &enum_map, &struct_map, &ty_map, &closure_map)
            .ok_or(SpliceRefusal::GlobalRemap)?;
        let Some(global) = static_globals.intern(module, *origin, g) else {
            if static_globals.conflicts(r) {
                static_globals.poison_record(r);
            }
            return Err(SpliceRefusal::GlobalRemap);
        };
        global_map.push(global);
    }
    // Trust (v41 `RustAbiVararg`): the fn-pointer map, built SPARSELY and BEFORE
    // the fast path below — which returns `BodyMaps::default()` and would
    // otherwise drop it for exactly the small bodies that reify a fn pointer.
    //
    // `Ty::Func` holds a body-local `FuncTyId`, so a declaration whose parameter
    // is a fn pointer had no way across into the assembled module and
    // `decl_params` refused the whole signature. Only the ids a recorded
    // `CalleeRef::params` signature actually names are interned — an ordinary body adds
    // nothing to `module.func_types`, which matters because that table is SCANNED
    // (`first_ffi_boundary`'s aggregate-at-a-boundary walk) and interning every
    // body's whole table to serve a rare parameter would move verdicts elsewhere
    // for no gain.
    //
    // Built with an EMPTY func map in hand, so a signature that itself contains a
    // fn pointer declines rather than needing a fixpoint. That is the honest
    // answer for a nested fn-pointer signature today and costs nothing the
    // producer could otherwise spell.
    let mut func_map: Vec<Option<FuncTyId>> = vec![None; r.func_types.len()];
    {
        let scratch = BodyMaps {
            enum_map: enum_map.clone(),
            struct_map: struct_map.clone(),
            ty_map: ty_map.clone(),
            closure_map: closure_map.clone(),
            func_map: Vec::new(),
        };
        let mut wanted: Vec<usize> = Vec::new();
        for callee in &r.callees {
            let Some(params) = callee.params.signature() else { continue };
            for p in params {
                if let Ty::Func(fid) = p {
                    let idx = fid.index() as usize;
                    if idx < func_map.len() && !wanted.contains(&idx) {
                        wanted.push(idx);
                    }
                }
            }
        }
        for idx in wanted {
            let Some(body_ft) = r.func_types.get(idx).cloned() else { continue };
            let Some(remapped) = remap_func_ty(&body_ft, &scratch) else { continue };
            func_map[idx] =
                Some(intern_func_ty(module, remapped).map_err(|_| SpliceRefusal::ModuleTable)?);
        }
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
        // Source provenance is sealed to the original single-body mini-module.
        // Crate assembly changes the containing module/files/function identity,
        // so this ordinary transform must drop authority, never self-reseal it.
        f.source_provenance = None;
        for block in &mut f.blocks {
            for node in &mut block.body {
                remap_node_span(node, &r.files, module)?;
            }
        }
        remap_func_scopes(&mut f, &r.files, module)?;
        return Ok((f, func_ty.clone(), BodyMaps { func_map, ..BodyMaps::default() }));
    }
    let mut ft = func_ty.clone();
    for t in ft.params.iter_mut().chain(ft.returns.iter_mut()) {
        *t = remap_ty(t, &enum_map, &struct_map, &ty_map, &closure_map)
            .ok_or(SpliceRefusal::FunctionRemap)?;
    }
    let mut f = func.clone();
    // Same invalidation as the table-free fast path: every remap changes the
    // semantic image authenticated by the per-body carrier.
    f.source_provenance = None;
    for block in &mut f.blocks {
        for (_, ty) in &mut block.params {
            *ty = remap_ty(ty, &enum_map, &struct_map, &ty_map, &closure_map)
                .ok_or(SpliceRefusal::FunctionRemap)?;
        }
        for node in &mut block.body {
            remap_node_span(node, &r.files, module)?;
            for t in inst_embedded_tys_mut(&mut node.inst).ok_or(SpliceRefusal::FunctionRemap)? {
                *t = remap_ty(t, &enum_map, &struct_map, &ty_map, &closure_map)
                    .ok_or(SpliceRefusal::FunctionRemap)?;
            }
            // Trust (wave-16): remap a promoted-borrow `Inst::GlobalAddr`'s per-body `GlobalId`
            // to its assembled-module index (`splice_ok` validated the id is in range).
            if let Inst::MakeClosure { ty, .. } = &mut node.inst {
                *ty = *closure_map.get(ty.as_usize()).ok_or(SpliceRefusal::FunctionRemap)?;
            }
            if let Inst::GlobalAddr { global } = &mut node.inst {
                *global = *global_map.get(global.as_usize()).ok_or(SpliceRefusal::FunctionRemap)?;
            }
        }
    }
    remap_func_scopes(&mut f, &r.files, module)?;

    Ok((f, ft, BodyMaps { enum_map, struct_map, ty_map, closure_map, func_map }))
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
/// [`remap_ty`] with the fn-pointer map threaded through. `remap_ty` keeps its
/// old signature and delegates with an EMPTY func map, so every existing caller
/// behaves exactly as before: a `Ty::Func` there still fails the remap closed.
fn remap_ty_with_funcs(
    ty: &Ty,
    enum_map: &[Option<EnumId>],
    struct_map: &[Option<StructId>],
    ty_map: &[Option<TyId>],
    closure_map: &[trust_ir::ClosureTyId],
    func_map: &[Option<FuncTyId>],
) -> Option<Ty> {
    if let Ty::Func(fid) = ty {
        return Some(Ty::Func((*func_map.get(fid.index() as usize)?)?));
    }
    remap_ty(ty, enum_map, struct_map, ty_map, closure_map)
}

fn remap_ty(
    ty: &Ty,
    enum_map: &[Option<EnumId>],
    struct_map: &[Option<StructId>],
    // Trust (vtable slice 15): `Option` like the enum/struct maps — pass 1 now pre-interns the
    // TABLE-FREE types entries before the def tables (so a struct field's scalar-element
    // `Ty::Array` id resolves), leaving holes for the struct/enum-referencing entries until the
    // main types loop fills them. A hole fails the remap closed, exactly like an unfilled def.
    ty_map: &[Option<TyId>],
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
        Ty::Array(tid, n) => Ty::Array((*ty_map.get(tid.as_usize())?)?, *n),
        // Trust (B6): first-class closure types remap through the pass-1 closure map
        // (per-body positional id -> assembled-module id, exactly like structs/enums).
        Ty::Closure(cid) => Ty::Closure(*closure_map.get(cid.as_usize())?),
        // Trust (B2): a slice fat pointer's ELEMENT id remaps through the types map;
        // the id-less fat kinds are table-free (handled by the catch below).
        // (B2-3: `TraitObject { trait_id }` clones VERBATIM there — sound because
        // trait_id is a CONTENT hash of the trait's def path, never a positional
        // table id; the producer's mint tripwire fail-closes hash collisions.)
        Ty::FatPtr(trust_ir::FatPtrKind::Slice(tid)) => {
            Ty::FatPtr(trust_ir::FatPtrKind::Slice((*ty_map.get(tid.as_usize())?)?))
        }
        // Storage has no table ids. Preserve its exact geometry during table transport;
        // signature/instruction admission and final NoValue validation remain independent.
        Ty::Storage(layout) if layout.is_well_formed(64) => Ty::Storage(*layout),
        other if ty_table_free(other) => other.clone(),
        _ => return None,
    })
}

/// Equality-interning into `Module::types` (`add_type` itself never dedups) — the `TyId`
/// counterpart of [`intern_func_ty`].
fn intern_ty(module: &mut Module, ty: Ty) -> Result<TyId, trust_ir::IdSpaceExhausted> {
    match module.types.iter().position(|existing| *existing == ty) {
        Some(i) => Ok(TyId::new(i as u32)),
        None => module.add_type(ty),
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
/// struct/enum-bearing signatures (the `fn() -> Name` shape behind the `LazyLock` statics).
///
/// STALE-DOC CORRECTION (#184 follow-on). This comment used to continue: "…that this gate then
/// refuses — a `lowered`-only admission", citing
/// `test_every_newly_admitted_component_is_still_refused_by_the_splice_predicate` as proof that
/// "the two halves are consistent precisely because every signature that widening newly admits
/// fails `ty_table_free`". That stopped being true when #184 removed the `all(ty_table_free)`
/// requirement below, and neither the comment nor the test was updated — so the retired contract
/// stayed asserted and turned main red. The protection MOVED rather than vanished: an
/// unresolvable component is now declined by `remap_func_ty`, tested by
/// `test_remap_func_ty_is_the_wall_that_replaced_table_freedom`.
fn body_sig_ok(r: &BodyRecord, sig: FuncTyId) -> bool {
    match r.func_types.get(sig.as_usize()) {
        // Trust (#184 follow-on): the `all(ty_table_free)` requirement is GONE. It existed only
        // because the seam re-interned these signatures RAW; both sites now remap through
        // `BodyMaps`, so a table-indexed param/return resolves correctly. Resolvability is
        // re-checked at the remap (a dangling id declines the body), exactly as #174 replaced
        // table-freedom with resolvability for enum variant fields.
        Some(ft) => !ft.is_vararg,
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
///   * ONE ledger identity with an exact CONCRETE key. A key-less edge is the unresolved
///     polymorphic/dynamic havoc class (`resolve_callee`'s `havoc:` key): taking its ADDRESS at a
///     concrete `Ty::Func` would claim the signature the havoc refuses to commit to.
///   * A FORCED-HAVOC edge WITH a concrete key (W1, 8932acd798: a concrete generic instance that
///     is declared, never linked to its identity-lowered body) is judged by the SAME branches as
///     any other edge below, never admitted on the flag alone. Ratification review 2026-09-28:
///     W1 had it return `true` before any comparison, which admitted a forced edge whose local
///     record's signature CONTRADICTS the claimed one (the closure-env arity hole this predicate
///     exists for) — an admission the pin refused. Routing it through the pin's own branches
///     keeps every edge the pin admitted (an extern target, an unrecorded one, a record whose
///     signature equals the claim) and refuses the rest, as the pin did;
///     `test_fnptr_target_sig_refuses_forced_concrete_edge_against_a_contradicting_record` pins it.
///     Like the two declaration-bound targets below it is also refused when the claim's arity
///     contradicts the callee's DECLARED one (last bullet), since it too is only ever declared.
///   * A LOCAL target with a record in this crate is the linkable case: compare its
///     producer-signed `func_ty` to `sig` STRUCTURALLY and refuse on any mismatch, on a record
///     with no signature at all, and on a target signature that is not table-free (the two sides
///     are numbered in DIFFERENT per-body tables, so only table-free types compare meaningfully;
///     `body_sig_ok` already forces the `sig` side).
///   * A target with NO record in this crate (cross-crate, or a local `DefIndex` this crate never
///     recorded) cannot be linked at all: pass 2's `resolve_callee` sends it to `decl_id`, and
///     since W1 that declaration is SIGNED WITH `sig` ITSELF — the constant's remapped signature
///     is `decl_id`'s `full_sig`, it becomes `DeclSigState::Exact`, and `append_declarations`
///     prefers it over the ledger's recovered `params`. (This comment used to say the declaration
///     is minted with the unknown-PARAMS encoding, so that "no ARITY is asserted": true before
///     W1, not after it.) The one fact on hand that can contradict `sig` there is the callee's
///     DECLARED parameter list, `ParamSignature::Signed`, read from `tcx.fn_sig` at this instance
///     and ground truth about the callee; a claimed arity that differs from it is REFUSED (D20,
///     2026-09-28: `test_a_declaration_bound_fnptr_whose_declared_arity_differs_does_not_splice`).
///     Before that check such a constant spliced and published the false arity as the
///     declaration's signature, whether or not any direct call exposed it. An `Unsigned` or
///     `Withdrawn` ledger states no parameters, so `sig` is then the only arity claim there is;
///     that it is the callee's rests on the `ReifyFnPointer` arm reading it from the same rustc
///     signature (above), and a direct call to the same declaration anywhere in the crate is still
///     checked against it by the final validator (`CallArgCountMismatch`, fatal).
///
/// WHAT THAT ARGUMENT DOES **NOT** COVER. Parameter TYPES on the declaration-bound targets: only
/// the arity is compared there, because the declared list and `sig` are two readers' spellings of
/// one rustc signature, and a refusal on a spelling difference has a splice-rate cost nobody has
/// measured. And `returns`: a declaration signed by a reified constant carries `claimed.returns`,
/// the ledger records no declared return type to compare it with (`ParamSignature` is parameters
/// only), and only a direct call that binds a different result is caught, by the final validator.
/// A `Withdrawn` ledger is admitted like an `Unsigned` one, and `c.params` is only THIS body's
/// contribution: a withdrawal another body records is merged in `decl_id`, after this predicate.
/// Only the local-with-a-record branch compares both halves (`target == claimed`). The hole this
/// predicate is here to close is the ARITY hole; the residuals are named rather than papered over.
///
/// SPLICE-RATE DELTA: UNMEASURED, pending a trustc rebuild + corpus run — and it could go either
/// way, so no "strengthening only" claim is made here. The specific branch that makes the optimistic
/// reading unsafe is `func_ty: None` (~:4062): a reify of a LOCAL fn whose own body did not lower
/// has no producer-signed signature to compare, and this predicate refuses it, which un-splices the
/// CALLER. Before this check that caller spliced and the edge simply became a `local-unlowered:`
/// declaration. The declared-arity refusal (D20) is unmeasured too. By inspection it should not
/// fire on an honest producer: `map_fn_ptr_ty` and `recover_callee_param_tys` (lib.rs) each map
/// the signature's inputs one to one or decline the whole list. No corpus run has confirmed it.
fn fnptr_target_sig_ok(r: &BodyRecord, records: &[BodyRecord], fid: FuncId, sig: FuncTyId) -> bool {
    let Some(claimed) = r.func_types.get(sig.as_usize()) else {
        return false;
    };
    let idents: Vec<&CalleeRef> = r.callees.iter().filter(|c| c.func_id == fid).collect();
    let [c] = idents.as_slice() else {
        return false;
    };
    // A reified target must carry an exact concrete identity. `None` is the unresolved
    // polymorphic/dynamic havoc class; taking its address at a concrete FuncTy would invent an
    // instance. A forced-bodyless CONCRETE key is declared at `claimed` in pass 2, but that
    // declaration is a CLAIM, so the edge is judged by the branches below exactly like every
    // other edge — never admitted on `force_havoc` alone (see the doc comment above).
    if c.concrete_key.is_none() {
        return false;
    }
    // Trust (D20, 2026-09-28): every edge pass 2 can only DECLARE — forced bodyless, cross-crate,
    // or a local `DefIndex` with no record — has that declaration signed with `claimed` (see the
    // doc comment), so `claimed` must not contradict the callee's DECLARED arity when the ledger
    // carries one. `Unsigned` and `Withdrawn` state none. A forced edge with a local record is
    // ALSO judged by the record comparison below; this only adds a refusal in front of it.
    let declared_arity_agrees =
        c.params.signature().is_none_or(|declared| declared.len() == claimed.params.len());
    if c.force_havoc && !declared_arity_agrees {
        return false;
    }
    if !c.is_local {
        return declared_arity_agrees;
    }
    let Ok(i) = records.binary_search_by_key(&c.def_index, |t| t.def_index) else {
        // No record for this local `DefIndex` ⇒ `lookup` misses in pass 2 ⇒ bodyless
        // `local-unlowered:` declaration, signed with `claimed` ⇒ only a declared arity can
        // contradict it.
        return declared_arity_agrees;
    };
    let Some(target) = &records[i].func_ty else {
        return false;
    };
    // Trust (2026-09-23): table-freedom is asked AS THE OLD `Ty::Tuple([T; N])` SPELLING WOULD
    // HAVE ANSWERED IT, and the comparison reads each side's arrays through its OWN types table.
    // A param `[(u8, u8); 2]` was table-free inline and compared by `==`; it is a first-class
    // `Ty::Array` now, whose id means nothing outside its body, so `==` across two bodies would
    // refuse every such pointer (measured: a `fn([(u8, u8); 2]) -> u8` reify spliced on
    // 7bc480faf and stopped splicing when the array became first-class). An array the old
    // spelling ALREADY made `Ty::Array` (a scalar or struct/enum element, or length 0) stays
    // refused, as it was.
    let tuple_spelled = tuple_spelled_table_free_entries(&records[i]);
    if target.is_vararg
        || !target
            .params
            .iter()
            .chain(target.returns.iter())
            .all(|t| table_free_as_tuple_spelled(&records[i], t, &tuple_spelled))
    {
        return false;
    }
    func_ty_eq_across(target, &records[i], claimed, r)
}

/// Trust (2026-09-23): per types entry, is it table-free under the rule the old
/// `Ty::Tuple([T; N])` spelling was? That spelling carried an array whose element was NOT a
/// scalar or struct/enum inline, as N copies of the element, so such an array was exactly as
/// table-free as its element; every other array (a scalar or struct/enum element, or length 0)
/// was already `Ty::Array` and so never table-free. One pass in entry order; an array names a
/// strictly earlier entry or is refused, so a malformed table cannot loop.
fn tuple_spelled_table_free_entries(r: &BodyRecord) -> Vec<bool> {
    let mut verdicts: Vec<bool> = Vec::with_capacity(r.types.len());
    for t in &r.types {
        let v = table_free_as_tuple_spelled(r, t, &verdicts);
        verdicts.push(v);
    }
    verdicts
}

/// Trust (2026-09-23): the per-type step of [`tuple_spelled_table_free_entries`] — `ty_table_free`,
/// except that a first-class array over an entry `k` answers `verdicts[k]` when the old spelling
/// would have tuple-spelled it (length > 0, element neither a scalar nor a struct/enum).
fn table_free_as_tuple_spelled(r: &BodyRecord, ty: &Ty, verdicts: &[bool]) -> bool {
    match ty {
        Ty::Array(tid, n) => {
            *n > 0
                && r.types.get(tid.as_usize()).is_some_and(|elem| !array_spelled_before(elem))
                && verdicts.get(tid.as_usize()).copied().unwrap_or(false)
        }
        Ty::Vector(elem, _) => table_free_as_tuple_spelled(r, elem, verdicts),
        Ty::Tuple(elems) => elems.iter().all(|e| table_free_as_tuple_spelled(r, e, verdicts)),
        Ty::Ref(inner)
        | Ty::RefMut(inner)
        | Ty::PtrConst(inner)
        | Ty::PtrMut(inner)
        | Ty::Rc(inner) => table_free_as_tuple_spelled(r, inner, verdicts),
        _ => ty_table_free(ty),
    }
}

/// Trust (2026-09-23): did the producer spell `[elem; N>0]` as a first-class `Ty::Array` before
/// every array was — a `seed_constant` scalar or float (vtable slice 15) or a struct/enum
/// (wave-NSA)?
fn array_spelled_before(elem: &Ty) -> bool {
    matches!(
        elem,
        Ty::Bool
            | Ty::I8
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
            | Ty::F32
            | Ty::F64
            | Ty::Struct(_)
            | Ty::Enum(_)
    )
}

/// Trust (2026-09-23): `a == b` for two signatures numbered in DIFFERENT bodies' tables, reading
/// each side's first-class arrays through its own types table. Every other component compares
/// by `==`, which is only meaningful for table-free types — the caller has already required that
/// of `a` (`table_free_as_tuple_spelled`), and equality then forces it of `b`.
fn func_ty_eq_across(a: &FuncTy, ra: &BodyRecord, b: &FuncTy, rb: &BodyRecord) -> bool {
    let mut memo: FxHashMap<(usize, usize), bool> = FxHashMap::default();
    a.is_vararg == b.is_vararg
        && a.params.len() == b.params.len()
        && a.returns.len() == b.returns.len()
        && a.params
            .iter()
            .zip(&b.params)
            .chain(a.returns.iter().zip(&b.returns))
            .all(|(x, y)| ty_eq_across(x, ra, y, rb, &mut memo))
}

/// Trust (2026-09-23): the per-type step of [`func_ty_eq_across`]. An array pair is decided once
/// per (entry, entry) pair (`memo`), so shared sub-entries cost one comparison, not one per path.
fn ty_eq_across(
    a: &Ty,
    ra: &BodyRecord,
    b: &Ty,
    rb: &BodyRecord,
    memo: &mut FxHashMap<(usize, usize), bool>,
) -> bool {
    match (a, b) {
        (Ty::Array(ta, na), Ty::Array(tb, nb)) => {
            if na != nb {
                return false;
            }
            let key = (ta.as_usize(), tb.as_usize());
            if let Some(v) = memo.get(&key) {
                return *v;
            }
            // Provisionally unequal while this pair is being decided: a cyclic (malformed)
            // table then answers `false` instead of recursing forever.
            memo.insert(key, false);
            let v = match (ra.types.get(key.0), rb.types.get(key.1)) {
                (Some(ea), Some(eb)) => ty_eq_across(ea, ra, eb, rb, memo),
                _ => false,
            };
            memo.insert(key, v);
            v
        }
        (Ty::Tuple(xs), Ty::Tuple(ys)) => {
            xs.len() == ys.len() && xs.iter().zip(ys).all(|(x, y)| ty_eq_across(x, ra, y, rb, memo))
        }
        (Ty::Vector(x, n), Ty::Vector(y, m)) => n == m && ty_eq_across(x, ra, y, rb, memo),
        (Ty::Ref(x), Ty::Ref(y))
        | (Ty::RefMut(x), Ty::RefMut(y))
        | (Ty::PtrConst(x), Ty::PtrConst(y))
        | (Ty::PtrMut(x), Ty::PtrMut(y))
        | (Ty::Rc(x), Ty::Rc(y)) => ty_eq_across(x, ra, y, rb, memo),
        _ => a == b,
    }
}

/// True iff `ty` references no module-level table (`structs`/`enums`/`types`/`func_types`/
/// `records`/`closure_types`) — i.e. it survives being moved between modules verbatim.
/// Allow-list, so any future `Ty` variant fails closed.
pub(crate) fn ty_table_free(ty: &Ty) -> bool {
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
        // `ContainerLen` (v38) is id-less by construction, so it is table-free
        // for exactly the reason `Str` is. Omitting it declined the SPLICE of
        // every body whose signature mentions one: measured, spliced 9 -> 6 on
        // the fat-pointee fixture, module 142 lines -> 74, which read as "zero
        // validation errors" because the types were no longer emitted to
        // validate. A green that comes from emitting NOTHING is what this arm
        // prevents.
        // Trust (v39): `ContainerVtable` joins for the same reason — id-less
        // (no trait id, no pointee TyId), so nothing to remap and nothing to dangle.
        Ty::FatPtr(trust_ir::FatPtrKind::Str)
        | Ty::FatPtr(trust_ir::FatPtrKind::ContainerLen)
        | Ty::FatPtr(trust_ir::FatPtrKind::ContainerVtable)
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
            // Trust (vtable slice 15): widened from Int-elements-only to the full promotable
            // scalar family, VARIANT-MATCHED per element (an Int-family element takes only
            // `Constant::Int`, a float only `Constant::Float`, bool only `Constant::Bool`) —
            // the wave-PA promoted `&[1.5f32, 2.5]` now arrives spelled `(Ty::Array,
            // Constant::Array)` instead of the tuple pair, and must stay exactly as admissible.
            //
            // Trust (2026-09-23): an element the OLD spelling tuple-spelled — a tuple, a nested
            // array, anything that is neither a scalar nor a struct/enum — takes this same
            // function per element, against the element type: exactly the check the tuple arm
            // below made per lane while `map_ty` spelled such an array `Ty::Tuple([T; N])`. Every
            // fixed-size array is first-class now, so the promoted `&[(1, 2), (3, 4)]` that
            // arrived as `(Ty::Tuple, Constant::Aggregate)` arrives as `(Ty::Array,
            // Constant::Array)`; without this disjunct it would stop splicing. Scalar elements keep
            // their variant-matched disjuncts above, unchanged.
            //
            // A STRUCT/ENUM element is excluded BY NAME, and that is parity, not an oversight:
            // wave-NSA already spelled `[S; N]` as `(Ty::Array, Constant::Array)`, and this arm
            // refused it (measured: a promoted `&[S { .. }, S { .. }]` lowered and did not
            // splice). Letting the per-element recursion reach the `Ty::Struct` arm below would
            // newly splice those globals — a widening of the oracle's splice set that would need
            // its own measured change, not a ride on a respelling.
            //
            // LENGTH ZERO IS NOT PART OF THAT PARITY (ratification review 2026-09-28). The old
            // spelling made `[T; 0]` a first-class `Ty::Array` for EVERY element, and this arm
            // refused it unless the element was one of the scalar families above; a vacuous
            // `all()` over no elements must not admit a zero-length array of tuples, pointers or
            // arrays that the pin refused. `*n > 0` restores exactly that.
            *n as usize == elems.len()
                && r.types.get(tid.as_usize()).is_some_and(|et| {
                    (scalar_int_ty(et) && elems.iter().all(|e| matches!(e, Constant::Int(_))))
                        || (matches!(et, Ty::F32 | Ty::F64)
                            && elems.iter().all(|e| matches!(e, Constant::Float(_))))
                        || (matches!(et, Ty::Bool)
                            && elems.iter().all(|e| matches!(e, Constant::Bool(_))))
                        || (*n > 0
                            && !scalar_global_ty(et)
                            && !matches!(et, Ty::Struct(_) | Ty::Enum(_))
                            && elems.iter().all(|e| global_const_ok(r, et, e)))
                })
        }
        // v50 uniform array `[elem; len]`: holds iff `len` is the declared length and its ONE
        // element passes exactly the per-element check the list arm above applies to every
        // element (the same variant-matched scalar family, the same struct/enum exclusion), so
        // it admits precisely the arrays the list spelling admitted, checked once whatever
        // `len` is.
        (Ty::Array(tid, n), Constant::Splat { elem, len }) => {
            *n == *len
                && r.types.get(tid.as_usize()).is_some_and(|et| {
                    (scalar_int_ty(et) && matches!(**elem, Constant::Int(_)))
                        || (matches!(et, Ty::F32 | Ty::F64) && matches!(**elem, Constant::Float(_)))
                        || (matches!(et, Ty::Bool) && matches!(**elem, Constant::Bool(_)))
                        || (*n > 0
                            && !scalar_global_ty(et)
                            && !matches!(et, Ty::Struct(_) | Ty::Enum(_))
                            && global_const_ok(r, et, elem))
                })
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
        // v50 uniform array: every lane is its one element, so it is FuncId-free iff that
        // element is (checked once, never per lane).
        Constant::Splat { elem, .. } => constant_funcid_free(elem),
        // FnDef, Closure, SymbolAddr, and anything new.
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// Artifact bytes — the binary and its text companion (WS5.23, F-099 guard).
// ---------------------------------------------------------------------------

/// The named refusal of [`check_text_companion_is_canonical`]: the head of every
/// message it returns, so a consumer (and the tests) can assert the reason by
/// substring.
pub(crate) const TEXT_COMPANION_NOT_CANONICAL: &str =
    "text companion is not the canonical form of the binary";

/// Render the two module-bearing artifacts of a publication, `<crate>.trust-ir.bin`
/// and `<crate>.trust-ir.txt`, and GUARD the relation between them.
///
/// The text companion is normatively `trust_ir::format::canonical` of the module
/// the binary carries — not `Display` (`trust-ir dump`, the human-readable,
/// insertion-ordered rendering with the producer's arena SSA ids), and not the
/// canonical text of some in-memory module that the binary does not faithfully
/// carry. Since 17d0ac39fd the producer already rendered `canonical`; F-099 asked
/// for a guard so that a text-diff consumer (G8 byte-stable text artifacts) can
/// rely on it. The guard is fail-closed and in-band: the bytes are re-derived
/// from the binary (`deserialize_module`, then `canonical`) and must equal the
/// text byte for byte, otherwise publication is refused with
/// [`TEXT_COMPANION_NOT_CANONICAL`] and no artifact set is committed. A mismatch
/// can only mean the binary codec is lossy for this module or the text renderer
/// depends on state the binary does not carry — both are producer defects a
/// consumer must never be handed silently.
pub(crate) fn render_publication_bytes(module: &Module) -> Result<(Vec<u8>, Vec<u8>), String> {
    // Trust (trust-ir D1b): a module the binary writer refuses publishes nothing.
    let bin = trust_ir::binary::serialize_module(module)
        .map_err(|refusal| format!("the assembled module has no wire image: {refusal}"))?;
    let txt = trust_ir::format::canonical(module).into_bytes();
    check_text_companion_is_canonical(&bin, &txt)?;
    Ok((bin, txt))
}

/// `txt == canonical(deserialize_module(bin))`, or a refusal that starts with
/// [`TEXT_COMPANION_NOT_CANONICAL`] and names the first differing line.
///
/// This is the whole F-099 relation; it takes only the two byte strings a
/// publication commits, so it states a property of the ARTIFACTS, not of the
/// module the producer happened to hold in memory.
pub(crate) fn check_text_companion_is_canonical(bin: &[u8], txt: &[u8]) -> Result<(), String> {
    let decoded = trust_ir::binary::deserialize_module(bin).map_err(|error| {
        format!(
            "{TEXT_COMPANION_NOT_CANONICAL}: the `.trust-ir.bin` bytes do not decode \
             (`trust_ir::binary::deserialize_module`: {error:?})"
        )
    })?;
    let expected = trust_ir::format::canonical(&decoded);
    if expected.as_bytes() == txt {
        return Ok(());
    }
    let actual = String::from_utf8_lossy(txt);
    let (line, want, got) = expected
        .lines()
        .zip(actual.lines())
        .enumerate()
        .find(|(_, (want, got))| want != got)
        .map(|(index, (want, got))| (index + 1, want.to_string(), got.to_string()))
        .unwrap_or_else(|| {
            let line = expected.lines().count().min(actual.lines().count()) + 1;
            (
                line,
                expected.lines().nth(line - 1).unwrap_or("<end of text>").to_string(),
                actual.lines().nth(line - 1).unwrap_or("<end of text>").to_string(),
            )
        });
    Err(format!(
        "{TEXT_COMPANION_NOT_CANONICAL}: `.trust-ir.txt` must be \
         `trust_ir::format::canonical` of the module decoded from `.trust-ir.bin` \
         (never `Display`, which is `trust-ir dump`); first difference at text line {line}: \
         expected `{want}`, found `{got}` ({} expected bytes, {} found bytes)",
        expected.len(),
        txt.len(),
    ))
}

/// WS5.23 (F-099 guard): the text companion is the canonical form of the binary.
///
/// The corpus is the trust-ir conformance fixture set of the pinned submodule
/// (`trust-ir-conformance/tests/fixtures/*.tmbc`, one byte-golden module per
/// wire feature), plus a hand-built module whose SSA ids are deliberately not
/// dense, so that `Display` (`trust-ir dump`) and `canonical` visibly differ.
/// The WS5.1 producer-ratchet corpus is exercised by the same guard in-process:
/// `render_publication_bytes` is the finalizer's ONLY artifact render site
/// (`final_validator_is_after_all_joins_and_before_serialization` pins that),
/// so every published crate module has already passed it.
///
/// Gate: `quick.thir-lower-unit-tests`
/// (`RUSTC_BOOTSTRAP=1 x.py test --stage 1 crates/trust-thir-lower`). This crate
/// links `rustc_private` and is in the `exclude` list of `crates/Cargo.toml`, so
/// the `targo … -p trust-thir-lower` lane the roadmap names answers "did not
/// match any packages" and `quick.crates-lib-tests` never compiles a line of it;
/// the per-crate x.py step is the only rung that reaches these tests.
#[cfg(test)]
mod text_companion_guard_tests {
    use super::*;

    fn conformance_fixture_dir() -> std::path::PathBuf {
        crate::source_scan::trust_ir_conformance_fixture_dir()
    }

    /// Every `.tmbc` byte-golden of the pinned trust-ir, decoded. The corpus
    /// must be non-vacuous: a missing submodule checkout is a test failure,
    /// never an empty PASS.
    fn corpus() -> Vec<(String, Module)> {
        let dir = conformance_fixture_dir();
        let mut fixtures: Vec<_> = std::fs::read_dir(&dir)
            .unwrap_or_else(|error| panic!("conformance fixture dir {}: {error}", dir.display()))
            .map(|entry| entry.expect("fixture entry").path())
            .filter(|path| path.extension().is_some_and(|ext| ext == "tmbc"))
            .collect();
        fixtures.sort();
        let corpus: Vec<_> = fixtures
            .into_iter()
            .map(|path| {
                let bytes = std::fs::read(&path).expect("fixture bytes");
                let module = trust_ir::binary::deserialize_module(&bytes)
                    .unwrap_or_else(|error| panic!("{}: {error:?}", path.display()));
                (path.file_name().unwrap().to_string_lossy().into_owned(), module)
            })
            .collect();
        assert!(
            corpus.len() >= 30,
            "the conformance corpus is the guard's positive fixture set; found {} `.tmbc` \
             goldens under {}",
            corpus.len(),
            dir.display()
        );
        corpus
    }

    /// A module the producer could assemble: arena SSA ids `%7` / `%3` that
    /// `canonical` renumbers densely and `Display` prints as they are.
    fn arena_id_module() -> Module {
        let mut module = Module::new("text_companion_probe");
        let func_ty = module
            .add_func_type(FuncTy {
                params: Vec::new(),
                returns: vec![Ty::I32],
                is_vararg: false,
                abi: None,
            })
            .expect("Module::add_func_type: test fixture");
        let mut function = Function::new(FuncId::new(0), "probe", func_ty, BlockId::new(0));
        let mut block = trust_ir::Block::new(BlockId::new(0));
        block.body.push(
            InstrNode::new(Inst::Const { ty: Ty::I32, value: Constant::Int(1) })
                .with_result(ValueId::new(7)),
        );
        block.body.push(
            InstrNode::new(Inst::Const { ty: Ty::I32, value: Constant::Int(2) })
                .with_result(ValueId::new(3)),
        );
        block.body.push(
            InstrNode::new(Inst::BinOp {
                op: trust_ir::BinOp::Add,
                ty: Ty::I32,
                lhs: ValueId::new(7),
                rhs: ValueId::new(3),
            })
            .with_result(ValueId::new(11)),
        );
        block.body.push(InstrNode::new(Inst::Return { values: vec![ValueId::new(11)] }));
        function.blocks.push(block);
        module.functions.push(function);
        module
    }

    /// The mutation under test: the pre-guard producer spelled `Display`
    /// instead of `canonical` — exactly what `trust-ir dump` prints.
    fn render_with_display(module: &Module) -> (Vec<u8>, Vec<u8>) {
        (
            trust_ir::binary::serialize_module(module).expect("serialize_module: test fixture"),
            format!("{module}").into_bytes(),
        )
    }

    // Positive: the relation holds on the whole corpus, and on the arena-id
    // module the published text is the DENSE renumbering, not the arena ids.
    #[test]
    fn corpus_text_companion_is_canonical_of_binary() {
        let mut corpus = corpus();
        corpus.push(("arena_id_module".into(), arena_id_module()));
        for (name, module) in &corpus {
            let (bin, txt) = render_publication_bytes(module)
                .unwrap_or_else(|error| panic!("{name}: {error}"));
            let decoded = trust_ir::binary::deserialize_module(&bin)
                .unwrap_or_else(|error| panic!("{name}: rendered binary decodes: {error:?}"));
            assert_eq!(
                txt,
                trust_ir::format::canonical(&decoded).into_bytes(),
                "{name}: txt == canonical(deserialize_module(bin))"
            );
            assert_eq!(
                check_text_companion_is_canonical(&bin, &txt),
                Ok(()),
                "{name}: the guard accepts what the producer renders"
            );
        }
        let (_, txt) = render_publication_bytes(&arena_id_module()).expect("renders");
        let txt = String::from_utf8(txt).expect("canonical text is UTF-8");
        assert!(txt.contains("%0") && txt.contains("%1") && txt.contains("%2"), "{txt}");
        assert!(!txt.contains("%7") && !txt.contains("%11"), "arena ids leaked: {txt}");
    }

    // Negative twin: `trust-ir dump` output (`Display`) differs from the
    // canonical companion and is refused with the named reason.
    #[test]
    fn display_dump_twin_is_refused_by_name() {
        let module = arena_id_module();
        let (bin, canonical) = render_publication_bytes(&module).expect("renders");
        let (twin_bin, display) = render_with_display(&module);
        assert_eq!(bin, twin_bin, "the twin differs from the positive by the text renderer only");
        assert_ne!(display, canonical, "Display keeps arena ids; canonical renumbers them");
        assert!(String::from_utf8_lossy(&display).contains("%7"), "Display is `trust-ir dump`");
        let error = check_text_companion_is_canonical(&bin, &display)
            .expect_err("Display bytes are not the canonical companion");
        assert!(error.starts_with(TEXT_COMPANION_NOT_CANONICAL), "{error}");
        assert!(error.contains("never `Display`, which is `trust-ir dump`"), "{error}");
        assert!(error.contains("first difference at text line"), "{error}");
        assert!(error.contains("%7") || error.contains("%0"), "names the differing line: {error}");
    }

    // Mutation control: with the producer spelling `Display` instead of
    // `canonical`, the guard fails — on the arena-id module always, and on
    // the corpus wherever the two renderings differ. The count of differing
    // corpus fixtures is asserted non-zero so the corpus itself, not only the
    // hand-built probe, carries the mutation.
    #[test]
    fn mutation_display_instead_of_canonical_is_caught() {
        let (bin, display) = render_with_display(&arena_id_module());
        assert!(
            check_text_companion_is_canonical(&bin, &display)
                .is_err_and(|error| error.starts_with(TEXT_COMPANION_NOT_CANONICAL))
        );
        let mut differing = Vec::new();
        for (name, module) in corpus() {
            let (bin, display) = render_with_display(&module);
            match check_text_companion_is_canonical(&bin, &display) {
                Ok(()) => assert_eq!(
                    display,
                    trust_ir::format::canonical(&module).into_bytes(),
                    "{name}: the guard accepts Display only where it equals canonical"
                ),
                Err(error) => {
                    assert!(error.starts_with(TEXT_COMPANION_NOT_CANONICAL), "{name}: {error}");
                    differing.push(name);
                }
            }
        }
        assert!(
            !differing.is_empty(),
            "no conformance fixture distinguishes Display from canonical; the corpus no \
             longer carries the F-099 mutation"
        );
    }

    // The guard states a property of the ARTIFACT bytes: a binary that does
    // not decode is refused under the same name, never accepted on the
    // strength of the in-memory module.
    #[test]
    fn undecodable_binary_is_refused_by_name() {
        let (bin, txt) = render_publication_bytes(&arena_id_module()).expect("renders");
        let truncated = &bin[..bin.len() / 2];
        let error = check_text_companion_is_canonical(truncated, &txt)
            .expect_err("a truncated binary has no canonical form");
        assert!(error.starts_with(TEXT_COMPANION_NOT_CANONICAL), "{error}");
        assert!(error.contains("do not decode"), "{error}");
    }

    // `scout-emit.P6` ported by name (roadmap §2.4 rule 4: a row whose defect
    // was closed upstream lands as a PASS row with a twin). The row read
    // "trustc's `.trust-ir.txt` is printed with pre-canonical SSA ids and
    // differs textually from Display of its own `.bin`". Since 17d0ac39fd the
    // published text IS the canonical form, so the row passes — and the
    // rendering it actually observed, `Display` (`trust-ir dump`), is the twin
    // that still prints the arena ids and is now refused by name.
    #[test]
    fn scout_emit_p6_published_text_is_canonical_never_arena_ids() {
        let module = arena_id_module();
        let (bin, txt) = render_publication_bytes(&module).expect("renders");
        let published = String::from_utf8(txt).expect("canonical text is UTF-8");
        let decoded = trust_ir::binary::deserialize_module(&bin).expect("the `.bin` decodes");
        assert_eq!(published, trust_ir::format::canonical(&decoded), "the row's PASS form");
        assert!(!published.contains("%7"), "pre-canonical SSA ids published: {published}");

        let (twin_bin, display) = render_with_display(&module);
        assert_eq!(bin, twin_bin, "the twin differs by the text renderer only");
        let display = String::from_utf8(display).expect("Display is UTF-8");
        assert!(display.contains("%7"), "the row's observation, still true of Display: {display}");
        assert_ne!(display, published, "Display differs textually from canonical");
        let error = check_text_companion_is_canonical(&bin, display.as_bytes())
            .expect_err("the row's twin is refused");
        assert!(error.starts_with(TEXT_COMPANION_NOT_CANONICAL), "{error}");
    }

    // Over-refusal control: a text that differs only by a trailing byte is
    // named at the right line, and the empty text is refused rather than
    // treated as "no companion".
    #[test]
    fn refusal_names_the_first_differing_line() {
        let (bin, mut txt) = render_publication_bytes(&arena_id_module()).expect("renders");
        txt.push(b'\n');
        let error = check_text_companion_is_canonical(&bin, &txt).expect_err("extra newline");
        assert!(error.contains("<end of text>"), "{error}");
        let error = check_text_companion_is_canonical(&bin, b"").expect_err("empty text");
        assert!(error.starts_with(TEXT_COMPANION_NOT_CANONICAL), "{error}");
        assert!(error.contains("0 found bytes"), "{error}");
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
    // Trust (IR-1, design §3.4): the additive `clean_origin` section. Every
    // pre-existing key, totals entry, and row stays byte-identical; only the
    // structural comma after the `bodies` array moves.
    clean_origin: &crate::clean_origin_join::CleanOriginJoinSummary,
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
        // Trust (2026-09-27): the typed splice refusal (schema-additive). `null` for a spliced row
        // and for an unlowered one (whose `unsupported` tags say why); a lowered row that is not
        // spliced MUST name its refusal, and anything else is a producer defect that fails the
        // artifact here rather than publishing a body lost without a reason. See `SpliceRefusal`.
        let splice_refusal = match (r.lowered, r.spliced, r.splice_refusal) {
            (true, false, Some(refusal)) => format!("\"{}\"", json_escape(refusal.marker())),
            (_, true, None) | (false, false, None) => "null".to_string(),
            (true, false, None) => {
                return Err(format!(
                    "coverage row `{}` (def index {}) is lowered but not spliced and names no \
                     splice refusal",
                    r.def_path, r.def_index
                ));
            }
            (_, _, Some(refusal)) => {
                return Err(format!(
                    "coverage row `{}` (def index {}) carries splice refusal `{}` but is {}",
                    r.def_path,
                    r.def_index,
                    refusal.marker(),
                    if r.spliced { "spliced" } else { "not lowered" }
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
             \"spliced\": {}, \"splice_refusal\": {}, \"lineage\": {}, \"func_id\": {}, \
             \"instr_count\": {}, \
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
            splice_refusal,
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
    let _ = writeln!(out, "  ],");
    // Trust (IR-1, design §3.4): the additive clean-origin section, rendered
    // by `clean_origin_join` (the frozen file only splices it in).
    let _ = writeln!(out, "{}", crate::clean_origin_join::coverage_section(clean_origin));
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
            splice_refusal: None,
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
            coverage_json("probe", &rows, 2, 0, &crate::clean_origin_join::CleanOriginJoinSummary::not_recorded()).is_err(),
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
        let coverage = coverage_json("probe", &rows, 2, 0, &crate::clean_origin_join::CleanOriginJoinSummary::not_recorded()).expect("resolved coverage");
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
        let ty = module
            .add_func_type(FuncTy {
                params: Vec::new(),
                returns: Vec::new(),
                is_vararg: false,
                abi: None,
            })
            .expect("Module::add_func_type: test fixture");
        module
            .try_add_function(Function::new(FuncId::new(0), "probe", ty, BlockId::new(0)))
            .expect("Module::try_add_function: test fixture");
        let digest = crate::lineage::body_lineage_digest(lineage_probe_definition(3), &module, &[])
            .expect("single-function probe module must digest");

        let mut with_digest = coverage_row(3, false);
        with_digest.lineage = Some(digest);
        with_digest.func_id = Some(4);
        let rows = vec![with_digest, coverage_row(7, false)];
        let coverage = coverage_json("probe", &rows, 2, 0, &crate::clean_origin_join::CleanOriginJoinSummary::not_recorded()).expect("resolved coverage");
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

    /// The definition a lineage probe body belongs to. The digest binds it, so a fixture
    /// must name one — and `lineage_body_record` derives it from `def_index`, so two
    /// fixture bodies are two definitions exactly when their records are.
    fn lineage_probe_definition(index: u64) -> crate::lineage::DefinitionIdentity {
        crate::lineage::DefinitionIdentity::test_only(0xC0DE, index)
    }

    #[test]
    fn tuple_layouts_survive_body_table_relocation_and_reject_conflicts() {
        let mut record = lineage_body_record(0, "tuple_layout_source");
        record.types = vec![Ty::Tuple(vec![Ty::U8, Ty::U64, Ty::U8])];
        record.target_info = Some(trust_ir::TargetInfo {
            triple: "aarch64-apple-darwin".into(), pointer_size: 8,
            endianness: trust_ir::Endianness::Little, abi: None,
            struct_passing: trust_ir::StructPassingPolicy::Unclassified,
        });
        record.tuple_layouts = vec![trust_ir::TupleLayoutDescriptor {
            tuple_type: TyId::new(0), size: 16, align: 8, field_offsets: vec![8, 0, 9],
        }];
        let mut destination = Module::new("tuple_layout_destination");
        let mut static_globals = static_globals::StaticGlobals::default();
        destination.add_type(Ty::Bool).expect("Module::add_type: test fixture");
        assert!(prepare_body_tables(&record, &mut destination, &mut static_globals).is_ok());
        assert_eq!(destination.tuple_layouts[0].tuple_type, TyId::new(1));
        assert_eq!(destination.tuple_layouts[0].field_offsets, vec![8, 0, 9]);
        assert_eq!(destination.target_info, record.target_info);
        let layouts = destination.tuple_layouts.clone();
        assert!(prepare_body_tables(&record, &mut destination, &mut static_globals).is_ok());
        assert_eq!(destination.tuple_layouts, layouts);
        record.tuple_layouts[0].field_offsets.swap(0, 2);
        assert_eq!(
            prepare_body_tables(&record, &mut destination, &mut static_globals).err(),
            Some(SpliceRefusal::TupleLayout),
            "a conflicting tuple layout observation refuses the splice BY NAME"
        );
        assert_eq!(destination.tuple_layouts, layouts);
    }

    #[test]
    fn closure_frames_survive_body_relocation_without_aliasing_different_layouts() {
        let mut record = lineage_body_record(0, "closure_frame_source");
        let signature = FuncTy {
            params: Vec::new(), returns: vec![Ty::U64], is_vararg: false, abi: None,
        };
        record.func_types.push(signature.clone());
        record.closure_types.push(trust_ir::ClosureTy {
            func: FuncTyId::new(0), captures: vec![Ty::U64, Ty::U64],
        });
        record.target_info = Some(trust_ir::TargetInfo {
            triple: "aarch64-apple-darwin".into(), pointer_size: 8,
            endianness: trust_ir::Endianness::Little, abi: None,
            struct_passing: trust_ir::StructPassingPolicy::Unclassified,
        });
        record.closure_layouts.push(trust_ir::ClosureLayoutDescriptor {
            origin: None,
            closure: trust_ir::ClosureTyId::new(0), size: 16, align: 8,
            capture_offsets: vec![8, 0],
        });
        let mut destination = body_layout_context(&record);
        destination.closure_layouts[0].capture_offsets = vec![0, 8];
        let mut globals = static_globals::StaticGlobals::default();
        assert!(prepare_body_tables(&record, &mut destination, &mut globals).is_ok());
        assert_eq!(destination.closure_types.len(), 2);
        assert_eq!(destination.closure_layouts[0].capture_offsets, vec![0, 8]);
        assert_eq!(destination.closure_layouts[1].capture_offsets, vec![8, 0]);
        let before = destination.clone();
        assert!(prepare_body_tables(&record, &mut destination, &mut globals).is_ok());
        assert_eq!(destination.closure_layouts, before.closure_layouts);
        record.closure_layouts[0].capture_offsets[1] = 8;
        let before = destination.clone();
        assert_eq!(prepare_body_tables(&record, &mut destination, &mut globals).err(),
            Some(SpliceRefusal::ClosureLayout));
        assert_eq!(destination, before);
    }

    #[test]
    fn same_body_closure_frame_observations_are_kept_distinct() {
        for known_first in [true, false] {
            let mut record = lineage_body_record(0, "closure_frame_twins");
            record.func_types.push(FuncTy {
                params: Vec::new(), returns: vec![Ty::U64], is_vararg: false, abi: None,
            });
            let ty = trust_ir::ClosureTy {
                func: FuncTyId::new(0), captures: vec![Ty::U64, Ty::U64],
            };
            record.closure_types = vec![ty.clone(), ty];
            record.target_info = Some(trust_ir::TargetInfo {
                triple: "aarch64-apple-darwin".into(), pointer_size: 8,
                endianness: trust_ir::Endianness::Little, abi: None,
                struct_passing: trust_ir::StructPassingPolicy::Unclassified,
            });
            let known = usize::from(!known_first);
            record.closure_layouts.push(trust_ir::ClosureLayoutDescriptor {
                origin: None,
                closure: trust_ir::ClosureTyId::new(known as u32), size: 16, align: 8,
                capture_offsets: vec![0, 8],
            });
            let mut destination = Module::new("closure_frame_twins_destination");
            let mut globals = static_globals::StaticGlobals::default();
            assert!(prepare_body_tables(&record, &mut destination, &mut globals).is_ok());
            assert_eq!(destination.closure_types.len(), 2);
            assert!(destination.closure_layout_descriptor(trust_ir::ClosureTyId::new(known as u32))
                .unwrap().is_some());
            assert!(destination.closure_layout_descriptor(trust_ir::ClosureTyId::new((1 - known) as u32))
                .unwrap().is_none());
        }
    }

    fn relocation_struct(id: u32, ty: Ty) -> trust_ir::StructDef {
        trust_ir::StructDef {
            id: StructId::new(id),
            name: format!("S{id}"),
            fields: vec![trust_ir::FieldDef { name: "f".into(), ty, offset: None }],
            size: None,
            align: None,
            repr: trust_ir::StructRepr::Rust,
            origin: None,
        }
    }

    /// Trust (2026-09-23): pass 1 interns a non-table-free array entry a struct field names as
    /// a `DefNode::Ty`, AFTER the struct it names and BEFORE the struct holding the field, so the
    /// field remaps; and an entry no def names keeps interning after both def tables, so a body
    /// that spliced before assembles its types table in exactly the order it did.
    #[test]
    fn test_array_field_entries_intern_in_dependency_order_and_others_keep_their_order() {
        // `struct T { f: [(S, u8); 2] }` beside `struct S { f: u8 }`.
        let mut record = lineage_body_record(0, "array_of_tuple_field");
        record.types = vec![Ty::Tuple(vec![Ty::Struct(StructId::new(0)), Ty::U8])];
        record.structs =
            vec![relocation_struct(0, Ty::U8), relocation_struct(1, Ty::Array(TyId::new(0), 2))];
        let mut destination = Module::new("array_of_tuple_destination");
        let mut static_globals = static_globals::StaticGlobals::default();
        assert!(prepare_body_tables(&record, &mut destination, &mut static_globals).is_ok());
        assert_eq!(destination.types, vec![Ty::Tuple(vec![Ty::Struct(StructId::new(0)), Ty::U8])]);
        assert_eq!(destination.structs[1].fields[0].ty, Ty::Array(TyId::new(0), 2));

        // `struct M { m: [[u32; 2]; 2] }`: the inner array is the element entry.
        let mut record = lineage_body_record(0, "nested_array_field");
        record.types = vec![Ty::U32, Ty::Array(TyId::new(0), 2)];
        record.structs = vec![relocation_struct(0, Ty::Array(TyId::new(1), 2))];
        let mut destination = Module::new("nested_array_destination");
        let mut static_globals = static_globals::StaticGlobals::default();
        assert!(prepare_body_tables(&record, &mut destination, &mut static_globals).is_ok());
        assert_eq!(destination.types, vec![Ty::U32, Ty::Array(TyId::new(0), 2)]);
        assert_eq!(destination.structs[0].fields[0].ty, Ty::Array(TyId::new(1), 2));

        // No def names the array entry (2): it stays a main-loop entry, after the
        // struct-referencing entry (0), with only the table-free entry (1) pre-interned.
        let mut record = lineage_body_record(0, "unneeded_array_entry");
        record.types = vec![Ty::Struct(StructId::new(0)), Ty::U8, Ty::Array(TyId::new(1), 4)];
        record.structs = vec![relocation_struct(0, Ty::U8)];
        let mut destination = Module::new("order_destination");
        let mut static_globals = static_globals::StaticGlobals::default();
        assert!(prepare_body_tables(&record, &mut destination, &mut static_globals).is_ok());
        assert_eq!(
            destination.types,
            vec![Ty::U8, Ty::Struct(StructId::new(0)), Ty::Array(TyId::new(0), 4)]
        );
    }

    #[test]
    fn nonempty_struct_array_fields_remap_ids_and_keep_layout_observations() {
        for length in [1, 2, 5] {
            let mut record = lineage_body_record(0, "nonempty_struct_array_field");
            record.types = vec![Ty::Struct(StructId::new(0))];
            let mut inner = relocation_struct(0, Ty::U32);
            inner.name = "Inner".into();
            inner.fields[0].offset = Some(0);
            inner.size = Some(4);
            inner.align = Some(4);
            let mut holder = relocation_struct(1, Ty::Array(TyId::new(0), length));
            holder.name = "Holder".into();
            holder.fields[0].offset = Some(0);
            holder.size = Some(4 * length);
            holder.align = Some(4);
            record.structs = vec![inner.clone(), holder.clone()];
            assert!(splice_ok(&record, std::slice::from_ref(&record)));

            // Force BOTH namespaces to move. Raw source IDs would select the
            // unrelated U16 prefix rather than the registered U32 element.
            let mut destination = Module::new("nonempty_struct_array_destination");
            let mut prefix = relocation_struct(0, Ty::U16);
            prefix.name = "Unrelated".into();
            destination.structs.push(prefix);
            destination.types.push(Ty::U16);
            let mut globals = static_globals::StaticGlobals::default();
            let (_, _, maps) = prepare_body_tables(&record, &mut destination, &mut globals)
                .expect("the typed dependency DAG must carry nonempty registered elements");
            assert_eq!(maps.remap(&Ty::Struct(StructId::new(0))), Some(Ty::Struct(StructId::new(1))));
            assert_eq!(destination.types, vec![Ty::U16, Ty::Struct(StructId::new(1))]);
            inner.id = StructId::new(1);
            holder.id = StructId::new(2);
            holder.fields[0].ty = Ty::Array(TyId::new(1), length);
            assert_eq!(destination.structs, vec![destination.structs[0].clone(), inner, holder]);
        }
    }

    /// A per-body record whose mini-module is the minimal spliceable shape: one
    /// zero-argument, block-free function, no tables, no callees. `lineage` is minted by
    /// the production function over that same mini-module, exactly as `record` does.
    pub(super) fn lineage_body_record(def_index: u32, fn_name: &str) -> BodyRecord {
        let mut module = Module::new("lineage_assembly_probe");
        let func_ty =
            FuncTy { params: Vec::new(), returns: Vec::new(), is_vararg: false, abi: None };
        let ty =
            module.add_func_type(func_ty.clone()).expect("Module::add_func_type: test fixture");
        module
            .try_add_function(Function::new(FuncId::new(0), fn_name, ty, BlockId::new(0)))
            .expect("Module::try_add_function: test fixture");
        let lineage = crate::lineage::body_lineage_digest(
            lineage_probe_definition(u64::from(def_index)),
            &module,
            &[],
        )
        .expect("the minimal per-body mini-module must digest");
        let function = module.functions.remove(0);
        BodyRecord {
            generated_ungated: false,
            coroutine_frame_ptr: false,
            abi: crate::calling_convention::FunctionAbi::RUST,
            def_index,
            definition: lineage_probe_definition(u64::from(def_index)),
            kind: BodyKind::Fn,
            symbolic: false,
            union_lane: false,
            storage_value_traffic: false,
            layout_withheld_structs: Vec::new(),
            enum_param_lane: false,
            def_path: fn_name.to_string(),
            place_path_carrier: false,
            zst_closure_arg: false,
            fnptr_adapter: false,
            adapters: Vec::new(),
            function: Some(function),
            func_ty: Some(func_ty),
            files: Vec::new(),
            closure_types: Vec::new(),
            closure_layouts: Vec::new(),
            structs: Vec::new(),
            enums: Vec::new(),
            types: Vec::new(),
            tuple_layouts: Vec::new(),
            target_info: None,
            globals: Vec::new(),
            global_origins: Vec::new(),
            unsupported: Vec::new(),
            unsupported_details: Vec::new(),
            enum_declines: Vec::new(),
            collect_primary: Vec::new(),
            collect_cascade: Vec::new(),
            instr_count: 0,
            callees: Vec::new(),
            func_types: Vec::new(),
            pending_consts: Vec::new(),
            contains_call: false,
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
            // WS5.2: a probe's link symbol is its probe name, so the assembled row is named by
            // exactly what the fixture says; `display_path` carries `def_path` (the same text).
            link_symbol: Some(fn_name.to_string()),
            callee_links: Vec::new(),
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

    /// Trust (storage value traffic) SPLICE REFUSAL, PINNED. The flag alone refuses an
    /// otherwise spliceable record, with its own marker.
    #[test]
    fn storage_value_traffic_record_is_refused_by_the_splice() {
        let clean = vec![lineage_body_record(1, "probe::clean")];
        assert!(
            splice_ok(&clean[0], &clean),
            "the minimal mini-module must splice — otherwise the storage half proves nothing"
        );
        let mut tainted = lineage_body_record(1, "probe::storage_value_traffic");
        tainted.storage_value_traffic = true;
        let tainted = vec![tainted];
        assert_eq!(
            splice_refusal(&tainted[0], &tainted),
            Some(SpliceRefusal::StorageValueTraffic),
            "value-position storage must be refused per body, never left to crate validation"
        );
        assert_eq!(SpliceRefusal::StorageValueTraffic.marker(), "Splice(storage value traffic)");
    }

    /// The predicate the flag is computed by, over real mini-modules: a struct holding storage
    /// geometry RETURNED by value is traffic (the `thread_local!` `LazyStorage` initializer
    /// shape); the same struct behind a reference is not; a callee ledger whose recorded return
    /// carries it is, because pass 2 would mint that declaration signature.
    #[test]
    fn storage_value_traffic_follows_the_shared_storage_policy() {
        let storage_module = |returns: Vec<Ty>, params: Vec<Ty>| {
            let mut module = Module::new("storage_value_probe");
            module.structs = vec![StructDef {
                id: StructId::new(0),
                name: "probe::Storage".to_string(),
                fields: vec![trust_ir::FieldDef {
                    name: "value".to_string(),
                    ty: Ty::Storage(trust_ir::StorageLayout::new(8, 8)),
                    offset: None,
                }],
                size: None,
                align: None,
                repr: trust_ir::StructRepr::Rust,
                origin: None,
            }];
            let ty = module
                .add_func_type(FuncTy { params, returns, is_vararg: false, abi: None })
                .expect("Module::add_func_type: test fixture");
            module
                .try_add_function(Function::new(FuncId::new(0), "probe", ty, BlockId::new(0)))
                .expect("Module::try_add_function: test fixture");
            module
        };
        let owner = Ty::Struct(StructId::new(0));
        let by_value = storage_module(vec![owner.clone()], Vec::new());
        assert!(module_carries_storage_value_traffic(&by_value, &[]));
        let by_reference = storage_module(Vec::new(), vec![Ty::Ref(Box::new(owner.clone()))]);
        assert!(!module_carries_storage_value_traffic(&by_reference, &[]));
        let mut callee = probe_callee(1, false, false);
        callee.ret_ty = Some(owner);
        assert!(module_carries_storage_value_traffic(&by_reference, &[callee]));
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
            coroutine_frame_ptr: false,
            global_origins: Vec::new(),
            mut_reborrows: Vec::new(),
            module: Module::new("param_lane_confinement_probe"),
            // Synthetic probe: no lowered blocks at all, so no enum-fold switch. Empty is
            // also the fail-closed value — an unrecorded fold can only MISS a flip, never
            // miscompile, because the comparator re-verifies derived == built.
            enum_fold_switch_blocks: std::collections::HashSet::new(),
            body_kind: BodyKind::Fn,
            opaque_collapse: ledger_nonempty,
            enum_declines: Vec::new(),
            union_lane: false,
            layout_withheld_structs: Vec::new(),
            enum_param_lane: ledger_nonempty,
            // The class IS symbolic in fact; carried so the assertion below that the differential
            // is unmoved by it is made against the real posture, not a stripped one.
            symbolic: ledger_nonempty,
            unsubstituted_opaque_return: false,
            unsupported: Vec::new(),
            contains_call: crate::param_lane_forces_not_interpretable(
                body_emitted_a_call,
                ledger_nonempty,
            ),
            place_path_carrier: false,
            zst_closure_arg: false,
            fnptr_adapter: false,
            thin_reborrows: Vec::new(),
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
            coroutine_frame_ptr: false,
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
        let assembled = assemble("fnptr_adapter_probe", &[r], &BTreeSet::new());
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

        let assembled = assemble("lineage_assembly_probe", &sorted, &BTreeSet::new());
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

    /// Macro expansion gives several const bodies one display path (measured: six spliced
    /// definitions sharing `main::CONST_EVAL::{constant#0}`). WS5.2: they no longer need a
    /// collision rename — each initializer is NAMED by the reserved `__trust_init_<stable
    /// definition hex>` symbol, injective by construction, `Linkage::Internal` (nothing links
    /// to an initializer), and both keep the shared path as their (non-unique) display path.
    #[test]
    fn assembly_names_macro_duplicate_initializers_by_distinct_reserved_symbols() {
        let shared = "main::CONST_EVAL::{constant#0}";
        let initializer = |def_index: u32| {
            let mut record = lineage_body_record(def_index, shared);
            record.kind = BodyKind::ConstInit;
            record.link_symbol = Some(crate::link_symbol::initializer_symbol(record.definition));
            // A spliced initializer always has a body. The shared fixture's function is
            // block-free, which at `Linkage::Internal` is an `EmptyFunction` (only an
            // External / ExternalWeak block-free row is a declaration), so give it one.
            let mut block = trust_ir::Block::new(BlockId::new(0));
            block.body.push(InstrNode::new(Inst::Return { values: Vec::new() }));
            record.function.as_mut().expect("the fixture function").blocks.push(block);
            record
        };
        let records = vec![initializer(30), initializer(36)];

        let assembled = assemble("duplicate_definition_name_probe", &records, &BTreeSet::new());
        assert!(assembled.errors.is_empty(), "{:?}", assembled.errors);
        assert_eq!(assembled.spliced, 2, "both measured-shape const bodies must splice");
        let names: BTreeSet<_> =
            assembled.module.functions.iter().map(|function| function.name.as_str()).collect();
        assert_eq!(names.len(), 2, "distinct definitions must have distinct link-time names");
        assert!(
            names.iter().all(|name| name.starts_with(crate::link_symbol::INITIALIZER_SYMBOL_PREFIX)),
            "{names:?}"
        );
        for function in &assembled.module.functions {
            assert_eq!(
                function.display_path.as_deref(),
                Some("main::CONST_EVAL::{constant#0}::{const-init}")
            );
            assert_eq!(function.linkage, Linkage::Internal, "nothing links to an initializer");
        }
        let validation = final_module_validation_errors(&assembled.module);
        assert!(
            validation.is_empty(),
            "one shared display path is not a collision: display paths are not identity: \
             {validation:?}"
        );
    }

    /// WS5.2 POSITIVE: a spliced fn body is NAMED by its link-time symbol and carries its def
    /// path as its display path.
    #[test]
    fn a_spliced_body_is_named_by_its_link_symbol_and_displays_its_def_path() {
        let mut record = lineage_body_record(5, "probe::a");
        record.link_symbol = Some("_RNvCs0_5probe1a".to_string());
        let assembled = assemble("link_symbol_probe", &[record], &BTreeSet::new());
        assert!(assembled.errors.is_empty(), "{:?}", assembled.errors);
        let function = &assembled.module.functions[0];
        assert_eq!(function.name, "_RNvCs0_5probe1a");
        assert_eq!(function.display_path.as_deref(), Some("probe::a"));
        assert_eq!(function.linkage, Linkage::External);
    }

    /// WS5.2 MUTATION CONTROL: a splice candidate that reached assembly WITHOUT a link-time
    /// symbol (finalization's stamp skipped) is a fatal producer defect — never a guessed name.
    #[test]
    fn a_spliced_body_without_a_link_symbol_is_a_fatal_producer_defect() {
        let mut record = lineage_body_record(5, "probe::a");
        record.link_symbol = None;
        let assembled = assemble("missing_link_symbol_probe", &[record], &BTreeSet::new());
        assert!(
            assembled.errors.iter().any(|e| e.contains("[missing-link-symbol]") && e.contains("probe::a")),
            "{:?}",
            assembled.errors
        );
        assert!(
            assembled.module.functions.iter().all(|f| f.name != "probe::a"),
            "the def path is never used as the name"
        );
    }

    /// WS5.2: two declaration rows that would carry ONE link-time symbol (one callee spelled
    /// two ways) are refused at the BODIES that mint them — every one, never "first wins" — and
    /// the control with distinct symbols refuses nothing.
    #[test]
    fn declarations_sharing_a_link_symbol_refuse_their_minting_bodies() {
        let caller = |def_index: u32, callee_fid: u32, symbol: &str| {
            let mut record = unsignable_edge_caller(def_index, "probe::caller", callee_fid);
            record.link_symbol = Some(format!("_RNvCs0_5probe6caller{def_index}"));
            record.callees[0].params = crate::ParamSignature::Signed(Vec::new());
            record.callee_links = vec![CalleeLink {
                symbol: Some(symbol.to_string()),
                producer: None,
                instance_lane_spelling: false,
                foreign_signature: None,
                foreign_source: None,
            }];
            record
        };
        let colliding = vec![caller(11, 7, "_RNvCs0_5probe4twin"), caller(12, 8, "_RNvCs0_5probe4twin")];
        let assembled = assemble("symbol_collision_probe", &colliding, &BTreeSet::new());
        assert_eq!(assembled.spliced, 2, "both callers splice before the refusal exists");
        let refused = symbol_collision_minting_bodies(&assembled);
        let refused_bodies: BTreeSet<u32> = refused.iter().map(|(def, _)| *def).collect();
        assert_eq!(refused_bodies, BTreeSet::from([11, 12]), "every minting body: {refused:?}");
        assert!(
            refused.iter().all(|(_, reason)| {
                reason.starts_with("LinkSymbolCollision(_RNvCs0_5probe4twin): ")
                    && reason.contains("probe::target")
            }),
            "{refused:?}"
        );

        let distinct = vec![caller(11, 7, "_RNvCs0_5probe3one"), caller(12, 8, "_RNvCs0_5probe3two")];
        let assembled = assemble("symbol_collision_control", &distinct, &BTreeSet::new());
        assert!(symbol_collision_minting_bodies(&assembled).is_empty());
    }

    fn probe_def_id(index: u32) -> DefId {
        DefId { krate: LOCAL_CRATE, index: rustc_span::def_id::DefIndex::from_u32(index) }
    }

    /// A ledger entry for `fid`, pointing at `def_index` in (or out of) this crate.
    fn probe_callee(fid: u32, is_local: bool, force_havoc: bool) -> CalleeRef {
        let definition = crate::lineage::DefinitionIdentity::test_only(0xC0DE, fid as u64);
        CalleeRef {
            func_id: FuncId::new(fid),
            is_local,
            def_index: fid,
            def_id: probe_def_id(fid),
            definition,
            concrete_key: Some(crate::lineage::ConcreteCalleeKey::test_only(
                definition,
                crate::lineage::ConcreteInstanceKind::Item,
                Vec::new(),
            )),
            // WS5.2: the key's own args (none), re-materializable.
            instance_args: Some(Vec::new()),
            def_path: format!("probe::target{fid}"),
            force_havoc,
            site_def_id: probe_def_id(fid),
            site_args: None,
            ret_ty: None,
            ret_ty_conflict: false,
            // #180: the conservative value the mint itself uses for a callee it
            // does not query (`lib.rs`, `abi: !def_id.is_local() && ..`).
            // A probe callee has no `tcx`, so it can only state `false` — the
            // pre-existing foreign-boundary treatment, never a new claim.
            abi: crate::calling_convention::FunctionAbi::C,
            // No contributing body withdrew this callee's signature, and none signed
            // it — the producer's own default at `admit_callee`'s push site.
            params: crate::ParamSignature::Unsigned,
        }
    }

    fn probe_decl_record(id: u32, key: &str, name: &str) -> DeclRecord {
        let definition = crate::lineage::DefinitionIdentity::test_only(0xD3C1, 7);
        DeclRecord {
            key: key.to_string(),
            id: FuncId::new(id),
            name: name.to_string(),
            ret: None,
            ret_conflict: false,
            abi: crate::calling_convention::FunctionAbi::RUST,
            definition: Some(definition),
            concrete_key: Some(crate::lineage::ConcreteCalleeKey::test_only(
                definition,
                crate::lineage::ConcreteInstanceKind::Item,
                vec![crate::lineage::ConcreteInstanceArg::Const(
                    crate::lineage::ConcreteInstanceConst::Value(
                        crate::lineage::ConcreteInstanceTy::Uint(rustc_middle::ty::UintTy::U8),
                        crate::lineage::ConcreteInstanceValTree::Leaf(7, 1),
                    ),
                )],
            )),
            local_def_index: key.starts_with("local-unlowered:").then_some(7),
            signature: DeclSigState::Unknown,
            params: crate::ParamSignature::Unsigned,
            params_conflict: false,
            // WS5.2: a probe row carries no finalization stamp (no symbol, unrecorded).
            link: CalleeLink::default(),
        }
    }

    #[test]
    fn clean_body_demand_requires_an_emitted_reference_and_exact_local_identity() {
        let clean = probe_callee(1, true, false);
        let unused = probe_callee(2, true, false);
        let ordinary = probe_callee(3, true, false);
        let mut record = lineage_body_record(9, "probe::caller");
        let function = record.function.as_mut().unwrap();
        let mut block = trust_ir::Block::new(BlockId::new(0));
        block.body.push(InstrNode::new(Inst::Call {
            callee: ordinary.func_id,
            args: Vec::new(),
        }));
        function.blocks.push(block);
        let clean_defs = BTreeSet::from([1, 2]);
        let mut ledger = vec![clean.clone(), unused, ordinary];
        assert!(referenced_clean_callees(function, &ledger, &clean_defs).is_empty());

        function.blocks[0].body.push(InstrNode::new(Inst::Call {
            callee: clean.func_id,
            args: Vec::new(),
        }));
        assert_eq!(
            referenced_clean_callees(function, &ledger, &clean_defs),
            vec![clean.def_id.expect_local()]
        );
        function.blocks[0].body.pop();
        function.blocks[0].body.push(InstrNode::new(Inst::Const {
            ty: Ty::Func(FuncTyId::new(0)),
            value: Constant::FnDef(clean.func_id),
        }));
        assert_eq!(
            referenced_clean_callees(function, &ledger, &clean_defs),
            vec![clean.def_id.expect_local()],
            "an emitted function address demands its exact def, never the unused ledger entry"
        );
        function.blocks[0].body.push(InstrNode::new(Inst::Call {
            callee: clean.func_id,
            args: Vec::new(),
        }));
        assert_eq!(referenced_clean_callees(function, &ledger, &clean_defs).len(), 1);
        ledger[0].is_local = false;
        assert!(referenced_clean_callees(function, &ledger, &clean_defs).is_empty());
        ledger[0] = clean.clone();
        ledger[0].def_index = 2;
        assert!(referenced_clean_callees(function, &ledger, &clean_defs).is_empty());
        ledger[0] = clean.clone();
        ledger.push(clean.clone());
        assert!(
            referenced_clean_callees(function, &ledger, &clean_defs).is_empty(),
            "an ambiguous ledger cannot choose a source definition"
        );

        record.callees = vec![clean.clone()];
        let mut registry = CrateModuleRegistry::default();
        registry.records.insert(record.def_index, record);
        assert_eq!(
            referenced_clean_origin_records(&registry, &clean_defs),
            vec![clean.def_id.expect_local()]
        );
        registry.duplicate_def_indices.push(9);
        assert!(
            referenced_clean_origin_records(&registry, &clean_defs).is_empty(),
            "known duplicate owners must reach the existing inventory refusal"
        );
    }

    #[test]
    fn recovered_declaration_parameters_remap_all_or_nothing() {
        let mut callee = probe_callee(1, false, false);
        let mut maps = BodyMaps {
            func_map: Vec::new(),
            enum_map: Vec::new(),
            struct_map: vec![Some(StructId::new(7))],
            ty_map: Vec::new(),
            closure_map: Vec::new(),
        };
        assert_eq!(
            decl_params(&callee, &maps),
            crate::ParamSignature::Unsigned,
            "unknown must not become zero-arity"
        );
        callee.params = crate::ParamSignature::Signed(vec![
            Ty::U64,
            Ty::Tuple(vec![Ty::Struct(StructId::new(0)), Ty::Bool]),
        ]);
        assert_eq!(
            decl_params(&callee, &maps),
            crate::ParamSignature::Signed(vec![
                Ty::U64,
                Ty::Tuple(vec![Ty::Struct(StructId::new(7)), Ty::Bool])
            ]),
        );
        maps.struct_map[0] = None;
        assert_eq!(
            decl_params(&callee, &maps),
            crate::ParamSignature::Unsigned,
            "missing nested type must not shorten params"
        );
        maps.struct_map.clear();
        assert_eq!(
            decl_params(&callee, &maps),
            crate::ParamSignature::Unsigned,
            "out-of-range type must not leak a body id"
        );
    }

    #[test]
    fn unrecovered_rust_declaration_does_not_invent_zero_parameters() {
        let mut module = Module::new("unrecovered_decl_stays_refused");
        let decl = probe_decl_record(0, "external:unknown", "probe::unknown");
        let mut unsignable = Vec::new();
        assert!(append_declarations(&mut module, &[decl], &mut unsignable).is_empty());
        assert_eq!(unsignable.len(), 1, "the unsigned row must be recorded for refusal");
        assert!(
            trust_ir_build::validate_module(&module).iter().any(|error| matches!(
                error,
                trust_ir_build::validate::ValidationError::RustAbiVararg { .. },
            )),
            "an unknown Rust declaration must remain refused"
        );
    }

    /// Trust (v41 `RustAbiVararg`): the BODYLESS GENERIC INSTANCE half of the
    /// producer refusal, pinned on the shape that reaches it —
    /// `tests/run-make/trust-cg-char-fieldless-enum-abi`'s `G::<u32>::tag`.
    ///
    /// The declaration cannot be signed: it is a LOCAL callee (so `tcx.fn_sig`
    /// is closed to the producer — the E0391 family) whose single parameter is a
    /// reference to a generic ADT, outside the table-free fragment. So the
    /// producer refuses it BY NAME and says why, and this test pins the two facts
    /// the user needs — the instance's arguments and the pre-monomorphization
    /// reason — plus the v7/D3 options.
    #[test]
    fn an_unsignable_generic_instance_declaration_is_refused_by_name_with_its_options() {
        let mut module = Module::new("unsignable_generic_instance");
        let definition = crate::lineage::DefinitionIdentity::test_only(0xD3C1, 7);
        let mut decl =
            probe_decl_record(0, "havoc:G::<T>::tag|concrete-v1:key", "G::<T>::tag");
        decl.concrete_key = Some(crate::lineage::ConcreteCalleeKey::test_only(
            definition,
            crate::lineage::ConcreteInstanceKind::Item,
            vec![crate::lineage::ConcreteInstanceArg::Ty(
                crate::lineage::ConcreteInstanceTy::Uint(rustc_middle::ty::UintTy::U32),
            )],
        ));
        let mut unsignable = Vec::new();
        assert!(append_declarations(&mut module, &[decl], &mut unsignable).is_empty());

        // The module is exactly the one the validator refuses today: this is the
        // defect being repaired, reproduced at the seam it is produced at.
        assert!(
            trust_ir_build::validate_module(&module).iter().any(|error| matches!(
                error,
                trust_ir_build::validate::ValidationError::RustAbiVararg { .. },
            )),
            "fixture must reproduce the validator's refusal"
        );

        let refusals =
            unsignable_declaration_refusals(&module, &unsignable, &BTreeSet::new());
        assert_eq!(refusals.len(), 1, "{refusals:?}");
        let refusal = &refusals[0];
        assert!(refusal.contains("unsignable-rust-abi-declaration"), "{refusal}");
        // WS5.2: the refusal names the def path the user wrote (the row's display path), not
        // its reserved link name.
        let shown = module.functions[0]
            .display_path
            .as_deref()
            .expect("WS5.2: a declaration with a definition identity displays its def path");
        assert!(refusal.contains(&format!("`{shown}`")), "{refusal}");
        assert!(refusal.contains("instance carries generic arguments `[u32]`"), "{refusal}");
        assert!(refusal.contains("lowers the body pre-monomorphization"), "{refusal}");
        assert!(refusal.contains("Options: (1)"), "{refusal}");
        assert!(refusal.contains("(2)") && refusal.contains("(3)"), "{refusal}");
        // Trust (H4, 2026-09-16): option (1) must name a lane that EXISTS. It used to say
        // "compile without `-Ztrust-ir-lower`", but `trust_ir_lower_enabled_by_flags`
        // (rustc_session) returns true whenever verification is on, so under verification
        // that option was not a choice the user had. The lane where it is a choice is
        // `-Ztrust-verify=off`, and the refusal says so.
        assert!(refusal.contains("Options: (1) `-Ztrust-verify=off`"), "{refusal}");
        assert!(!refusal.contains("compile without `-Ztrust-ir-lower`"), "{refusal}");
    }

    /// The complement, and the reason the refusal is computed at finalization
    /// rather than at append: a row SIGNED after assembly — which is exactly what
    /// the Clean-origin join does to the declaration its appended definition
    /// shadows — must not be refused. The record is a candidate list, never a
    /// verdict.
    #[test]
    fn a_declaration_signed_after_assembly_is_not_refused() {
        let mut module = Module::new("late_signed_declaration");
        let decl = probe_decl_record(0, "local-unlowered:m::clean_def", "m::clean_def");
        let mut unsignable = Vec::new();
        assert!(append_declarations(&mut module, &[decl], &mut unsignable).is_empty());
        assert_eq!(unsignable.len(), 1);
        assert_eq!(
            unsignable_declaration_refusals(&module, &unsignable, &BTreeSet::new()).len(),
            1,
        );

        // A later pass signs the row with a real signature, exactly as
        // `link_clean_origin_edges` does with the appended definition's FuncTyId.
        let signed = module
            .add_func_type(FuncTy {
                params: vec![Ty::U64],
                returns: vec![Ty::U64],
                is_vararg: false,
                abi: None,
            })
            .expect("Module::add_func_type: test fixture");
        module.functions[0].ty = signed;
        assert!(
            unsignable_declaration_refusals(&module, &unsignable, &BTreeSet::new()).is_empty(),
            "a declaration signed before the module is emitted must not be refused"
        );
    }

    // ---------------------------------------------------------------------
    // Trust (owner call 2026-09-17(b)): REFUSE THE BODY, NOT THE CRATE.
    //
    // `reports/2026-09-14-rust-abi-vararg-producer-half.md` ends on two moves, both
    // format-level, and the owner chose (b): the producer refuses every body that mints an
    // unsignable Rust-ABI call edge, trading that body's coverage for a module the rest of the
    // crate can still be assembled and validated into. These pin the three halves of that —
    // the body IS refused and says why with its options, a body with no such edge is NOT
    // touched, and the module that results VALIDATES.
    // ---------------------------------------------------------------------

    /// A caller whose single block calls `FuncId(callee_fid)` and returns, with a ledger entry
    /// for an EXTERN Rust-ABI callee whose parameter types the producer never recovered. That
    /// is exactly the population `append_declarations` records as unsignable: `abi` true,
    /// `params` `None`, so the interned signature is `params: [] + is_vararg: true`.
    fn unsignable_edge_caller(def_index: u32, name: &str, callee_fid: u32) -> BodyRecord {
        let mut record = lineage_body_record(def_index, name);
        let mut callee = probe_callee(callee_fid, false, false);
        callee.abi = crate::calling_convention::FunctionAbi::RUST;
        callee.params = crate::ParamSignature::Unsigned;
        record.callees = vec![callee];
        record.contains_call = true;
        let mut function = record.function.take().expect("the probe record carries a function");
        let mut block = trust_ir::Block::new(BlockId::new(0));
        block.body.push(InstrNode::new(Inst::Call {
            callee: FuncId::new(callee_fid),
            args: Vec::new(),
        }));
        block.body.push(InstrNode::new(Inst::Return { values: Vec::new() }));
        function.blocks.push(block);
        record.function = Some(function);
        record
    }

    /// The same caller shape, but its one call edge names a callee whose parameter types the
    /// producer DID recover — so the declaration is signed and nothing about this body is
    /// unsignable. The control that makes the positive half non-vacuous.
    fn signed_edge_caller(def_index: u32, name: &str, callee_fid: u32) -> BodyRecord {
        let mut record = unsignable_edge_caller(def_index, name, callee_fid);
        record.callees[0].params = crate::ParamSignature::Signed(Vec::new());
        record
    }

    #[test]
    fn a_body_that_mints_an_unsignable_rust_abi_edge_is_refused_with_the_shared_options() {
        let records = vec![unsignable_edge_caller(11, "probe::caller", 7)];
        let assembled = assemble("unsignable_edge_body_refusal", &records, &BTreeSet::new());
        assert_eq!(assembled.spliced, 1, "the caller must splice before the refusal exists");
        assert_eq!(
            assembled.unsignable_declarations.len(),
            1,
            "the fixture must reproduce the unsignable declaration it is about"
        );

        let refused = unsignable_minting_bodies(&assembled, &BTreeSet::new());
        assert_eq!(refused.len(), 1, "{refused:?}");
        assert_eq!(refused[0].0, 11, "the refusal must name the MINTING body's DefIndex");
        let reason = &refused[0].1;
        assert!(reason.starts_with("UnsignableRustAbiDeclaration("), "{reason}");
        assert!(reason.contains("probe::target7"), "the callee must be named: {reason}");
        assert!(reason.contains("mints a call edge"), "{reason}");
        // v7/D3: the OPTIONS travel with the per-body reason, from the same source of truth as
        // the crate-level refusal — not a paraphrase of them.
        assert!(reason.contains("Options: (1) `-Ztrust-verify=off`"), "{reason}");
        assert!(reason.contains("(2)") && reason.contains("(3)"), "{reason}");
        assert!(reason.contains(UNSIGNABLE_DECLARATION_OPTIONS), "{reason}");
        assert!(reason.contains(UNSIGNABLE_DECLARATION_ENCODING), "{reason}");
    }

    #[test]
    fn a_body_with_no_unsignable_edge_is_untouched_by_the_refusal() {
        let records = vec![signed_edge_caller(11, "probe::caller", 7)];
        let assembled = assemble("signed_edge_body_control", &records, &BTreeSet::new());
        assert_eq!(assembled.spliced, 1);
        assert!(
            assembled.unsignable_declarations.is_empty(),
            "a recovered parameter list signs the declaration, so there is nothing to refuse"
        );
        assert!(
            unsignable_minting_bodies(&assembled, &BTreeSet::new()).is_empty(),
            "a body with no unsignable edge must not be refused"
        );
        assert!(
            trust_ir_build::validate_module(&assembled.module).iter().all(|error| !matches!(
                error,
                trust_ir_build::validate::ValidationError::RustAbiVararg { .. },
            )),
            "the control must not carry the defect the positive half is about"
        );
    }

    /// The whole point of the owner call: one unsignable edge used to fail the WHOLE crate, so
    /// nothing was produced. After refusing the body that mints it, the declaration is never
    /// minted (pass 2 mints only from a spliced body's edge), the surviving module VALIDATES,
    /// and the crate-level refusal has nothing left to report.
    #[test]
    fn refusing_the_minting_body_removes_the_row_and_the_module_validates() {
        let mut records =
            vec![unsignable_edge_caller(11, "probe::caller", 7), lineage_body_record(12, "probe::clean")];
        records.sort_by_key(|r| r.def_index);

        let before = assemble("unsignable_edge_before", &records, &BTreeSet::new());
        assert!(
            trust_ir_build::validate_module(&before.module).iter().any(|error| matches!(
                error,
                trust_ir_build::validate::ValidationError::RustAbiVararg { .. },
            )),
            "the fixture must reproduce the validator refusal this change is about"
        );
        assert_eq!(
            unsignable_declaration_refusals(
                &before.module,
                &before.unsignable_declarations,
                &BTreeSet::new(),
            )
            .len(),
            1,
            "and the crate-level refusal must be what fails the crate today"
        );

        let refused = unsignable_minting_bodies(&before, &BTreeSet::new());
        assert_eq!(refused.len(), 1);
        for (def_index, reason) in refused {
            let index = records
                .binary_search_by_key(&def_index, |r| r.def_index)
                .expect("the refusal must name a recorded body");
            bump_unsupported(&mut records[index].unsupported, &reason);
        }

        let after = assemble("unsignable_edge_after", &records, &BTreeSet::new());
        assert!(
            !splice_ok(&records[0], &records),
            "the refused body must be un-spliceable by its own recorded reason"
        );
        assert_eq!(after.spliced, 1, "the body that did NOT mint the edge must still splice");
        assert!(
            after.unsignable_declarations.is_empty(),
            "with no spliced body naming it, the declaration is never minted at all"
        );
        assert_eq!(after.declarations, 0, "no declaration may be minted at all");
        assert_eq!(
            after.module.functions.len(),
            after.assigned.len(),
            "the module must hold the spliced bodies and nothing else: {:?}",
            after.module.functions.iter().map(|f| f.name.clone()).collect::<Vec<_>>(),
        );
        assert!(
            trust_ir_build::validate_module(&after.module).iter().all(|error| !matches!(
                error,
                trust_ir_build::validate::ValidationError::RustAbiVararg { .. },
            )),
            "the emitted module must validate once the minting body is refused"
        );
        assert!(
            final_module_validation_errors(&after.module).is_empty(),
            "{:?}",
            final_module_validation_errors(&after.module)
        );
        assert!(
            unsignable_declaration_refusals(
                &after.module,
                &after.unsignable_declarations,
                &BTreeSet::new(),
            )
            .is_empty(),
            "and the crate-level refusal must have nothing left to say"
        );

        // The coverage sidecar carries the reason, with its options, on the refused body — the
        // refusal is REPORTED, never a silent drop.
        let row = after
            .coverage_rows
            .iter()
            .find(|row| row.def_index == 11)
            .expect("a refused body still appears in coverage");
        assert!(!row.spliced);
        assert!(!row.lowered, "a refused body is not counted as lowered");
        assert_eq!(row.unsupported.len(), 1, "{:?}", row.unsupported);
        assert_eq!(row.unsupported[0].1, 1);
        assert!(row.unsupported[0].0.contains("Options: (1) `-Ztrust-verify=off`"));
    }

    /// The EXEMPTION, and why it is not a hole. A declaration whose `local_def_index` names a
    /// Clean-origin def is the row `link_clean_origin_edges` may still sign — by re-pointing
    /// exactly the edges a body refusal would delete. So the body is NOT refused, the row is
    /// left for the join, and if the join does not shadow it the crate-level refusal fires and
    /// NAMES that disposition instead of blaming the producer.
    #[test]
    fn a_clean_origin_candidate_row_is_exempt_from_body_refusal_and_says_so() {
        let mut caller = unsignable_edge_caller(11, "probe::caller", 7);
        caller.callees[0].is_local = true;
        let records = vec![caller];
        let assembled = assemble("clean_origin_exempt_probe", &records, &BTreeSet::new());
        assert_eq!(assembled.spliced, 1);
        assert_eq!(assembled.unsignable_declarations.len(), 1);
        assert_eq!(
            assembled.unsignable_declarations[0].local_def_index,
            Some(7),
            "a local-unlowered row must carry its exact source identity"
        );

        let exempt: BTreeSet<u32> = [7].into_iter().collect();
        assert!(
            unsignable_minting_bodies(&assembled, &exempt).is_empty(),
            "a Clean-origin candidate's callers must not be refused — IR-5 needs those edges"
        );
        assert_eq!(
            unsignable_minting_bodies(&assembled, &BTreeSet::new()).len(),
            1,
            "and the exemption must be what makes the difference, not an inert fixture"
        );

        let refusals = unsignable_declaration_refusals(
            &assembled.module,
            &assembled.unsignable_declarations,
            &exempt,
        );
        assert_eq!(refusals.len(), 1, "{refusals:?}");
        assert!(refusals[0].contains("names a Clean-origin definition"), "{}", refusals[0]);
        assert!(refusals[0].contains("DefIndex 7"), "{}", refusals[0]);
        assert!(
            !refusals[0].contains("PRODUCER DEFECT"),
            "an exempted row is a disposition, not a producer defect: {}",
            refusals[0]
        );
    }

    /// The other two dispositions, so the message cannot claim the wrong one. A non-exempt row
    /// that survives is a PRODUCER DEFECT, and the message distinguishes "a body still names
    /// it" (attribution missed) from "nothing names it" (a dead row).
    #[test]
    fn a_surviving_non_exempt_row_is_reported_as_a_producer_defect_by_case() {
        let records = vec![unsignable_edge_caller(11, "probe::caller", 7)];
        let assembled = assemble("producer_defect_disposition", &records, &BTreeSet::new());
        let referenced = unsignable_declaration_refusals(
            &assembled.module,
            &assembled.unsignable_declarations,
            &BTreeSet::new(),
        );
        assert_eq!(referenced.len(), 1, "{referenced:?}");
        assert!(referenced[0].contains("PRODUCER DEFECT"), "{}", referenced[0]);
        assert!(referenced[0].contains("still name this declaration"), "{}", referenced[0]);

        // Now strip the edge without removing the row: the dead-row case.
        let mut dead = assembled;
        for function in &mut dead.module.functions {
            for block in &mut function.blocks {
                block.body.retain(|node| !matches!(node.inst, Inst::Call { .. }));
            }
        }
        let orphaned = unsignable_declaration_refusals(
            &dead.module,
            &dead.unsignable_declarations,
            &BTreeSet::new(),
        );
        assert_eq!(orphaned.len(), 1, "{orphaned:?}");
        assert!(orphaned[0].contains("PRODUCER DEFECT"), "{}", orphaned[0]);
        assert!(orphaned[0].contains("no function in the emitted module"), "{}", orphaned[0]);
    }

    /// MONOTONICITY, pinned. The refusal loop re-assembles, and pass 1's own fixpoint is not
    /// monotone in the live set (`place_carrier_reaches_real_params` refuses a caller only
    /// WHILE its callee is a live local with parameters). `assemble`'s `spliced_veto` forbids a
    /// later round from admitting a body an earlier round did not, by construction rather than
    /// by an argument about which predicates happen to be monotone today.
    #[test]
    fn the_spliced_veto_can_only_remove_a_body_never_admit_one() {
        let records = vec![lineage_body_record(3, "probe::a"), lineage_body_record(4, "probe::b")];
        let open = assemble("veto_probe_open", &records, &BTreeSet::new());
        assert_eq!(open.spliced, 2);

        let vetoed = assemble("veto_probe_closed", &records, &[3].into_iter().collect());
        assert_eq!(vetoed.spliced, 1, "the vetoed body must not be spliced");
        assert!(
            vetoed.coverage_rows.iter().any(|row| row.def_index == 3 && !row.spliced),
            "and it must still appear in coverage as un-spliced"
        );
        assert!(
            vetoed.module.functions.iter().all(|f| f.name != "probe::a"),
            "a vetoed body must not reach the assembled module"
        );
    }

    /// The PRODUCTION veto construction, not just `assemble`'s honouring of a veto handed to it.
    ///
    /// Review finding (2026-09-17): `the_spliced_veto_can_only_remove_a_body_never_admit_one`
    /// pins that `assemble` obeys a veto set, but the expression that BUILDS that set each round
    /// — "every record whose def_index is not in this round's SPLICED coverage rows" — was
    /// covered by nothing. This pins the two properties the refusal loop's termination and its
    /// soundness both rest on, against the exact spelling production uses:
    ///
    ///   * it never vetoes a body that spliced this round (a veto that removed a clean body
    ///     would lose coverage the owner's trade did not buy), and
    ///   * it is MONOTONE — re-running it on the next round's assembly can only grow the set,
    ///     which is what stops pass 1's non-monotone fixpoint from re-ADMITTING a refused body.
    ///
    /// The set spelling is also the hoisted one (`spliced_now`), so a future edit that
    /// re-nests the scan changes a tested expression rather than an untested one.
    #[test]
    fn the_production_veto_is_built_from_exactly_the_unspliced_records() {
        let records = vec![
            lineage_body_record(3, "probe::a"),
            lineage_body_record(4, "probe::b"),
            lineage_body_record(5, "probe::c"),
        ];
        // Round 1: nothing vetoed, so every record splices and the veto must stay EMPTY.
        let round1 = assemble("veto_build_r1", &records, &BTreeSet::new());
        let spliced_now: BTreeSet<u32> = round1
            .coverage_rows
            .iter()
            .filter(|row| row.spliced)
            .map(|row| row.def_index)
            .collect();
        let built: BTreeSet<u32> = records
            .iter()
            .map(|r| r.def_index)
            .filter(|def_index| !spliced_now.contains(def_index))
            .collect();
        assert_eq!(round1.spliced, 3, "all three bodies splice with an empty veto");
        assert!(
            built.is_empty(),
            "a round in which every body spliced must veto nothing, got {built:?}"
        );

        // Round 2: one body vetoed. The rebuilt set must contain exactly that body — the
        // other two spliced, so vetoing either would be the ADMIT-side error inverted.
        let mut veto: BTreeSet<u32> = [4u32].into_iter().collect();
        let round2 = assemble("veto_build_r2", &records, &veto);
        let spliced_now2: BTreeSet<u32> = round2
            .coverage_rows
            .iter()
            .filter(|row| row.spliced)
            .map(|row| row.def_index)
            .collect();
        let built2: BTreeSet<u32> = records
            .iter()
            .map(|r| r.def_index)
            .filter(|def_index| !spliced_now2.contains(def_index))
            .collect();
        assert_eq!(built2, [4u32].into_iter().collect::<BTreeSet<u32>>());

        // MONOTONE: folding the rebuilt set back in can only grow it, never drop 4.
        let before = veto.clone();
        veto.extend(built2);
        assert!(before.is_subset(&veto), "the veto set must only ever grow");
        assert!(veto.contains(&4), "a vetoed body stays vetoed across rounds");
    }

    /// The edge scan is an ALLOW-LIST with an `Unmodeled` answer, not a `_ => false` deny-list:
    /// an instruction shape it does not model must make the caller refuse the body rather than
    /// report "no edge" and leave the declaration in the emitted module. `Inst::Invoke` is the
    /// stand-in — `splice_ok` refuses it by name today, so this is the discipline, not a live
    /// population.
    #[test]
    fn an_unmodelled_instruction_shape_cannot_report_absence_of_an_edge() {
        let mut function =
            Function::new(FuncId::new(0), "probe::opaque", FuncTyId::new(0), BlockId::new(0));
        let mut block = trust_ir::Block::new(BlockId::new(0));
        block.body.push(InstrNode::new(Inst::Invoke {
            callee: FuncId::new(9),
            args: Vec::new(),
            normal_dest: BlockId::new(0),
            normal_args: Vec::new(),
            unwind_dest: BlockId::new(0),
        }));
        function.blocks.push(block);
        assert_eq!(
            inst_referenced_funcs(&function.blocks[0].body[0].inst),
            None,
            "an unmodelled FuncId-bearing shape must not answer `no FuncIds`"
        );
        assert_eq!(
            declaration_edge(&function, FuncId::new(1)),
            DeclarationEdge::Unmodeled,
            "and the body must not be reported edge-free on the strength of it"
        );

        let mut modelled = function.clone();
        modelled.blocks[0].body.clear();
        modelled.blocks[0]
            .body
            .push(InstrNode::new(Inst::Call { callee: FuncId::new(1), args: Vec::new() }));
        assert_eq!(declaration_edge(&modelled, FuncId::new(1)), DeclarationEdge::Named);
        assert_eq!(declaration_edge(&modelled, FuncId::new(2)), DeclarationEdge::Absent);
    }

    #[test]
    fn recovered_rust_declaration_checks_argument_count_and_type() {
        use trust_ir_build::validate::ValidationError;

        for (argument_ty, pass_argument) in [(Ty::U64, true), (Ty::U64, false), (Ty::U32, true)] {
            let mut module = Module::new("recovered_decl_argument_validation");
            module.target_info = Some(trust_ir::TargetInfo {
                triple: "aarch64-apple-darwin".into(),
                pointer_size: 8,
                endianness: trust_ir::Endianness::Little,
                abi: None,
                struct_passing: Default::default(),
            });
            let mut decl = probe_decl_record(0, "external:consume", "probe::consume");
            decl.params = crate::ParamSignature::Signed(vec![Ty::U64]);
            let mut unsignable = Vec::new();
            assert!(append_declarations(&mut module, &[decl], &mut unsignable).is_empty());
            assert!(unsignable.is_empty(), "a signed declaration is not a refusal candidate");
            let declaration = &module.functions[0];
            assert_eq!(declaration.calling_conv, trust_ir::CallingConv::Rust);
            let signature = &module.func_types[declaration.ty.index() as usize];
            assert_eq!(signature.params, vec![Ty::U64]);
            assert!(!signature.is_vararg);

            let ty = module
                .add_func_type(FuncTy {
                    params: Vec::new(),
                    returns: Vec::new(),
                    is_vararg: false,
                    abi: None,
                })
                .expect("Module::add_func_type: test fixture");
            let mut function = Function::new(FuncId::new(1), "caller", ty, BlockId::new(0));
            function.calling_conv = trust_ir::CallingConv::Rust;
            let mut block = trust_ir::Block::new(BlockId::new(0));
            block.body.push(
                InstrNode::new(Inst::Const { ty: argument_ty.clone(), value: Constant::Int(7) })
                    .with_result(ValueId::new(0)),
            );
            block.body.push(InstrNode::new(Inst::Call {
                callee: FuncId::new(0),
                args: if pass_argument { vec![ValueId::new(0)] } else { Vec::new() },
            }));
            block.body.push(InstrNode::new(Inst::Return { values: Vec::new() }));
            function.blocks.push(block);
            module.try_add_function(function).expect("Module::try_add_function: test fixture");
            let errors = trust_ir_build::validate_module(&module);
            if !pass_argument {
                assert!(
                    errors.iter().any(|error| matches!(
                        error,
                        ValidationError::CallArgCountMismatch { expected: 1, actual: 0, .. }
                    )),
                    "discarded argument must be rejected: {errors:?}"
                );
            } else if argument_ty == Ty::U32 {
                assert!(
                    errors
                        .iter()
                        .any(|error| matches!(error, ValidationError::CallArgTypeMismatch { .. })),
                    "wrong argument type must be rejected: {errors:?}"
                );
            } else {
                assert!(errors.is_empty(), "correct recovered call must validate: {errors:?}");
            }
        }
    }

    /// Trust (H1, 2026-09-16): the UC fence refuses a VARARG declaration BEFORE conjunct 1,
    /// and the refusal is not vacuous. Stash H1 (the `is_vararg` check in
    /// `uc_declaration_fence`) and the first case returns `Ok(None)` — conjunct 1 iterates the
    /// empty parameter list of a declaration whose parameters are UNKNOWN and passes, which is
    /// the vacuity the report names. The second case is the shape the rvalue-snapshot
    /// admission moves `std::io::_print` into: signed `(struct.k) -> ()`, refused by NAME on
    /// its non-scalar parameter, never `uc-agreed`. The third is the control: a scalar
    /// signature passes the fence and plans its return type.
    #[test]
    fn uc_declaration_fence_refuses_a_vararg_row_before_conjunct_1() {
        let vararg = FuncTy { params: Vec::new(), returns: Vec::new(), is_vararg: true, abi: None };
        assert_eq!(uc_declaration_fence(&vararg), Err("vararg declaration".to_string()));

        let struct_param = FuncTy {
            params: vec![Ty::Struct(StructId::new(4))],
            returns: Vec::new(),
            is_vararg: false,
            abi: None,
        };
        assert_eq!(
            uc_declaration_fence(&struct_param),
            Err("non-scalar callee param struct.4".to_string())
        );

        let scalar =
            FuncTy { params: vec![Ty::U32], returns: vec![Ty::U32], is_vararg: false, abi: None };
        assert_eq!(uc_declaration_fence(&scalar), Ok(Some(Ty::U32)));
        let zero_result =
            FuncTy { params: vec![Ty::U32], returns: Vec::new(), is_vararg: false, abi: None };
        assert_eq!(uc_declaration_fence(&zero_result), Ok(None));
    }

    /// Trust (2026-09-16, rvalue-snapshot admission — control (v): the drop-coherence gate
    /// is still live, pinned at the seam it lives at). The plan of record asked for a ui
    /// fixture on `assert_eq!`'s `assert_failed`, whose `Option<Arguments>` argument wave-28
    /// was said to drop. MEASURED on the `d5e6ef620f3` stage1 before this landing: that
    /// argument LOWERS and `assert_failed` is signed `(enum.0, ptr, ptr, enum.1) -> ()` —
    /// nothing is dropped, so a ui fixture on that shape pins nothing. The gate itself is
    /// `decl_id`'s sticky withdrawal (Addendum 3, defect 1) followed by `append_declarations`
    /// + `unsignable_declaration_refusals`, and it is pinned here directly: in EITHER order —
    /// a signed observation then a withdrawal, or a withdrawal then a signed observation —
    /// the declaration keeps no parameter list, is emitted `params: [] + is_vararg: true`,
    /// and is refused BY NAME at finalization. The rvalue-snapshot admission lowers the
    /// `format_args!` argument and so makes `_print` never enter this path; it does not weaken
    /// the path for a callee that still loses an argument.
    #[test]
    fn a_withdrawn_parameter_list_is_sticky_across_bodies_and_refused_by_name() {
        for withdraw_first in [false, true] {
            let mut decls: Vec<DeclRecord> = Vec::new();
            let observe = |decls: &mut Vec<DeclRecord>, params: crate::ParamSignature| {
                decl_id(
                    decls,
                    0,
                    "extern:std::io::_print".to_string(),
                    "std::io::_print".to_string(),
                    None,
                crate::calling_convention::FunctionAbi::RUST,
                    None,
                    None,
                    None,
                    None,
                    params,
                    CalleeLink::default(),
                )
            };
            let signed = || crate::ParamSignature::Signed(vec![Ty::U64]);
            let (first, second) = if withdraw_first {
                (
                    observe(&mut decls, crate::ParamSignature::Withdrawn),
                    observe(&mut decls, signed()),
                )
            } else {
                (
                    observe(&mut decls, signed()),
                    observe(&mut decls, crate::ParamSignature::Withdrawn),
                )
            };
            assert_eq!(first, second, "one identity, one FuncId");
            assert_eq!(decls.len(), 1);
            // ONE assertion now, where there were two. "Withdrawal recorded" and
            // "states no parameters" were two reads of a field PAIR that could
            // disagree; `ParamSignature::Withdrawn` is one value that cannot.
            assert_eq!(
                decls[0].params,
                crate::ParamSignature::Withdrawn,
                "withdrawal must be recorded, and a withdrawn row states no parameters \
                 (withdraw_first={withdraw_first})"
            );

            let mut module = Module::new("withdrawn_declaration");
            let mut unsignable = Vec::new();
            assert!(append_declarations(&mut module, &decls, &mut unsignable).is_empty());
            let signature = &module.func_types[module.functions[0].ty.index() as usize];
            assert!(signature.params.is_empty() && signature.is_vararg, "{signature:?}");
            let refusals =
            unsignable_declaration_refusals(&module, &unsignable, &BTreeSet::new());
            assert_eq!(refusals.len(), 1, "{refusals:?}");
            assert!(refusals[0].contains("unsignable-rust-abi-declaration"), "{}", refusals[0]);
            assert!(refusals[0].contains("std::io::_print"), "{}", refusals[0]);
        }
    }

    /// Trust (2026-09-16, rvalue-snapshot admission — fixture (iv)): the signed `fmt` edge is
    /// NOT vacuous. With `std::io::_print` signed `(struct.k) -> ()` — the spelling the
    /// `registered_struct_id` arm gives it once the call-bearing `format_args!` block lowers —
    /// trust-ir's own validator rejects a call that drops the argument
    /// (`CallArgCountMismatch { expected: 1, actual: 0 }`) and a call that hands it the
    /// producer's fail-closed unit placeholder (`CallArgTypeMismatch { expected: "struct.k",
    /// actual: "()" }`). This is the check that the `params: [] + is_vararg: true` encoding
    /// used to make run zero times, and it is exactly why a placeholder operand was refused
    /// as the fix: the validator cannot tell `fn(())` from "unknown" if both spell `()`.
    #[test]
    fn a_signed_struct_parameter_edge_rejects_a_dropped_and_a_unit_placeholder_argument() {
        use trust_ir_build::validate::ValidationError;

        for pass_unit_placeholder in [false, true] {
            let mut module = Module::new("signed_struct_param_edge");
            module.target_info = Some(trust_ir::TargetInfo {
                triple: "aarch64-apple-darwin".into(),
                pointer_size: 8,
                endianness: trust_ir::Endianness::Little,
                abi: None,
                struct_passing: Default::default(),
            });
            // The producer's `fmt::Arguments` registration: two thin pointers.
            let arguments = module.add_struct(StructDef {
                id: StructId::new(0),
                name: "core::fmt::Arguments".into(),
                fields: vec![
                    trust_ir::FieldDef { name: "template".into(), ty: Ty::Ptr, offset: None },
                    trust_ir::FieldDef { name: "args".into(), ty: Ty::Ptr, offset: None },
                ],
                size: None,
                align: None,
                repr: trust_ir::StructRepr::Rust,
                origin: None,
            });
            let print_ty = module
                .add_func_type(FuncTy {
                    params: vec![Ty::Struct(arguments)],
                    returns: Vec::new(),
                    is_vararg: false,
                    abi: None,
                })
                .expect("Module::add_func_type: test fixture");
            // Spelled exactly as `append_declarations` spells a signed Rust-ABI declaration.
            let mut print =
                Function::new(FuncId::new(0), "std::io::_print", print_ty, BlockId::new(0))
                    .with_producer(trust_ir::Producer::TRust);
            print.linkage = Linkage::External;
            print.calling_conv = trust_ir::CallingConv::Rust;
            module.try_add_function(print).expect("Module::try_add_function: test fixture");
            assert!(module.functions[0].is_declaration());

            let caller_ty = module
                .add_func_type(FuncTy {
                    params: Vec::new(),
                    returns: Vec::new(),
                    is_vararg: false,
                    abi: None,
                })
                .expect("Module::add_func_type: test fixture");
            let mut caller = Function::new(FuncId::new(1), "main", caller_ty, BlockId::new(0));
            caller.calling_conv = trust_ir::CallingConv::Rust;
            let mut block = trust_ir::Block::new(BlockId::new(0));
            let args = if pass_unit_placeholder {
                block.body.push(
                    InstrNode::new(Inst::Const { ty: Ty::Unit, value: Constant::PhantomData })
                        .with_result(ValueId::new(0)),
                );
                vec![ValueId::new(0)]
            } else {
                Vec::new()
            };
            block.body.push(InstrNode::new(Inst::Call { callee: FuncId::new(0), args }));
            block.body.push(InstrNode::new(Inst::Return { values: Vec::new() }));
            caller.blocks.push(block);
            module.try_add_function(caller).expect("Module::try_add_function: test fixture");

            let errors = trust_ir_build::validate_module(&module);
            if pass_unit_placeholder {
                assert!(
                    errors.iter().any(|error| matches!(
                        error,
                        ValidationError::CallArgTypeMismatch { arg_index: 0, expected, actual, .. }
                            if expected == "struct.0" && actual == "()"
                    )),
                    "a unit placeholder against the signed struct edge must be rejected: {errors:?}"
                );
            } else {
                assert!(
                    errors.iter().any(|error| matches!(
                        error,
                        ValidationError::CallArgCountMismatch { expected: 1, actual: 0, .. }
                    )),
                    "a dropped argument against the signed struct edge must be rejected: {errors:?}"
                );
            }
        }
    }

    fn codegen_declaration_retention_fixture() -> (Module, Vec<CodegenDeclarationRecord>) {
        let decl = probe_decl_record(0, "extern:up::leaf|concrete-v1:fixture", "up::leaf");
        let mut module = Module::new("retained_declaration");
        let sig = module.add_func_type(FuncTy {
            params: vec![Ty::U64], returns: vec![Ty::U64], is_vararg: false, abi: None,
        }).unwrap();
        let mut function = Function::new(FuncId::new(0), "_RActualUpLeaf", sig, BlockId::new(0));
        function.producer = None;
        function.calling_conv = trust_ir::CallingConv::Rust;
        module.try_add_function(function).unwrap();
        let records = retain_codegen_declarations(&module, &[decl]).unwrap();
        (module, records)
    }

    #[test]
    fn codegen_declaration_retention_keeps_typed_keys_and_current_module_after_conservation_clone() {
        let (module, records) = codegen_declaration_retention_fixture();
        let original = std::sync::Arc::new(module);
        let mut handoff = crate::AssembledCrateModuleForCodegen::checked(original.clone(), Vec::new())
            .unwrap().retain_declarations(&records).unwrap();
        let expected_definition = records[0].definition().unwrap().symbol_suffix();
        let expected_concrete = records[0].concrete_key().unwrap().symbol_suffix();
        let current = std::sync::Arc::new((*original).clone());
        // finalize's real conservation pass installs a fresh immutable image.
        handoff.module = Some(current.clone());
        let view = handoff.declaration(FuncId::new(0)).unwrap();
        assert!(std::sync::Arc::ptr_eq(view.module(), &current));
        assert!(std::sync::Arc::ptr_eq(view.original_handoff_module(), &original));
        assert_eq!(view.function(), &original.functions[0]);
        assert_eq!(view.signature(), original.func_type(original.functions[0].ty).unwrap());
        assert_eq!(view.definition_suffix().as_deref(), Some(expected_definition.as_str()));
        assert_eq!(view.concrete_suffix().as_deref(), Some(expected_concrete.as_str()));
    }

    #[test]
    fn codegen_declaration_retention_withholds_changed_name_type_body_or_missing_row() {
        for mutation in 0..4 {
            let (mut module, records) = codegen_declaration_retention_fixture();
            match mutation {
                0 => module.functions[0].name.push_str("_wrong"),
                1 => module.func_types[0].params[0] = Ty::I64,
                2 => module.functions[0].blocks.push(trust_ir::Block::new(BlockId::new(0))),
                _ => {}
            }
            let mut handoff = crate::AssembledCrateModuleForCodegen::checked(std::sync::Arc::new(module), Vec::new()).unwrap();
            if mutation != 3 { handoff = handoff.retain_declarations(&records).unwrap(); }
            assert!(handoff.declaration(FuncId::new(0)).is_none(), "mutation {mutation}");
        }
    }

    #[test]
    fn codegen_declaration_retention_preserves_unknown_identity_and_refuses_duplicate_rows() {
        let (module, _) = codegen_declaration_retention_fixture();
        let mut unknown = probe_decl_record(0, "unknown:up::leaf", "up::leaf");
        unknown.definition = None;
        unknown.concrete_key = None;
        let records = retain_codegen_declarations(&module, &[unknown]).unwrap();
        let handoff = crate::AssembledCrateModuleForCodegen::checked(std::sync::Arc::new(module.clone()), Vec::new())
            .unwrap().retain_declarations(&records).unwrap();
        let view = handoff.declaration(FuncId::new(0)).unwrap();
        assert!(view.definition().is_none());
        assert!(view.concrete_key().is_none());
        let duplicate = retain_codegen_declarations(&module, &[
            probe_decl_record(0, "extern:a", "up::leaf"),
            probe_decl_record(0, "extern:a", "up::leaf"),
        ]).unwrap();
        assert!(crate::AssembledCrateModuleForCodegen::checked(std::sync::Arc::new(module), Vec::new())
            .unwrap().retain_declarations(&duplicate).is_err());
    }

    /// WS5.2 POSITIVE: a declaration whose callee instance has a computed link-time symbol is
    /// NAMED by it — the name the callee's object exports — and carries its def path as the
    /// display path, so a Rust declaration and the definition in another crate agree by symbol.
    #[test]
    fn a_declaration_with_a_computed_symbol_is_named_by_it_and_displays_its_def_path() {
        let module = Module::new("declaration_symbol_probe");
        let mut decl = probe_decl_record(
            1,
            "havoc:probe::single_generic|concrete-v1:instance",
            "probe::single_generic",
        );
        decl.link = CalleeLink {
            symbol: Some("_RINvCs0_5probe14single_genericmEB2_".to_string()),
            producer: Some(trust_ir::Producer::TRust),
            instance_lane_spelling: false,
            foreign_signature: None,
            foreign_source: None,
        };
        let (name, display) = emitted_decl_name(&module, std::slice::from_ref(&decl), &decl);
        assert_eq!(name, "_RINvCs0_5probe14single_genericmEB2_");
        assert_eq!(display.as_deref(), Some("probe::single_generic"));
    }

    /// WS5.2 NEGATIVE TWIN: no computed symbol (no concrete key, a reify shim, args that do not
    /// re-materialize) means a RESERVED, never-linkable name — never the def path, which is not
    /// a symbol and would alias the callee's definition in name-keyed consumers.
    #[test]
    fn a_declaration_without_a_symbol_gets_a_reserved_never_linkable_name() {
        let mut module = Module::new("definition_declaration_name_collision");
        let ty = module
            .add_func_type(FuncTy {
                params: Vec::new(),
                returns: Vec::new(),
                is_vararg: false,
                abi: None,
            })
            .expect("Module::add_func_type: test fixture");
        module
            .try_add_function(Function::new(
                FuncId::new(0),
                "probe::single_generic",
                ty,
                BlockId::new(0),
            ))
            .expect("Module::try_add_function: test fixture");
        let decl = probe_decl_record(
            1,
            "havoc:probe::single_generic|concrete-v1:instance",
            "probe::single_generic",
        );
        let (name, display) = emitted_decl_name(&module, std::slice::from_ref(&decl), &decl);
        assert!(
            name.starts_with(crate::link_symbol::UNLINKED_DECLARATION_PREFIX),
            "an unsymbolled declaration must carry the reserved unlinked spelling: {name}"
        );
        assert_ne!(name, module.functions[0].name);
        assert_eq!(display.as_deref(), Some("probe::single_generic"));
    }

    /// RESIDUAL PIN (WS5.2 NARROWED, `docs/DECISION_QUEUE.md` D17-DECL-SYMBOL-1) — the one place
    /// `Function.name` is not yet the link-time symbol. A declaration of a generic instance the
    /// frozen D17 instance lane appends keeps its PRE-WS5.2 spelling: the bare display path when
    /// nothing shares it, no `display_path`, and no symbol; the lane's own (frozen) acceptance
    /// function, `instance_admission::declaration_name_matches`, accepts it. Naming it by symbol
    /// here, or giving it a display path, turns this red.
    #[test]
    fn an_instance_lane_declaration_keeps_its_pre_ws5_2_display_path_name() {
        let module = Module::new("instance_lane_spelling_probe");
        let mut decl = probe_decl_record(
            1,
            "local-unlowered:probe::single_generic|concrete-v1:instance",
            "probe::single_generic",
        );
        decl.link = CalleeLink {
            symbol: None,
            producer: Some(trust_ir::Producer::TRust),
            instance_lane_spelling: true,
            foreign_signature: None,
            foreign_source: None,
        };
        let (name, display) = emitted_decl_name(&module, std::slice::from_ref(&decl), &decl);
        assert_eq!(name, "probe::single_generic", "the pre-WS5.2 bare display-path name");
        assert_eq!(display, None, "the pre-WS5.2 row carries no display path");
        let definition = decl.definition.expect("probe identity").symbol_suffix();
        let concrete = decl.concrete_key.as_ref().expect("probe key").symbol_suffix();
        crate::instance_admission::declaration_name_matches(
            &name,
            "probe::single_generic",
            &definition,
            &concrete,
        )
        .expect("the frozen relink accepts the carved-out declaration");
        // The same row OUTSIDE the carve-out is named by WS5.2's rule, which the lane refuses:
        // that refusal is exactly why the carve-out exists.
        decl.link.instance_lane_spelling = false;
        let (unlinked, _) = emitted_decl_name(&module, std::slice::from_ref(&decl), &decl);
        assert!(unlinked.starts_with(crate::link_symbol::UNLINKED_DECLARATION_PREFIX));
        assert!(
            crate::instance_admission::declaration_name_matches(
                &unlinked,
                "probe::single_generic",
                &definition,
                &concrete,
            )
            .is_err()
        );
    }

    /// RESIDUAL PIN, the shared-path half: when a WS5.2 definition DISPLAYS the carved-out row's
    /// path (at the pin it was NAMED by it), or a second instance of the same definition is
    /// declared, each carved-out row takes the pin's injective `!trust_bodyless_instance::`
    /// collision form — which the frozen relink checks IN FULL, so each row is accepted for its
    /// own instance and refused for the other's.
    #[test]
    fn instance_lane_declarations_sharing_a_path_take_the_pin_collision_form() {
        let mut module = Module::new("instance_lane_collision_probe");
        let ty = module
            .add_func_type(FuncTy {
                params: Vec::new(),
                returns: Vec::new(),
                is_vararg: false,
                abi: None,
            })
            .expect("Module::add_func_type: test fixture");
        let mut definition_row =
            Function::new(FuncId::new(0), "_RNvCs0_5probe14single_generic", ty, BlockId::new(0));
        definition_row.display_path = Some("probe::single_generic".to_string());
        module.try_add_function(definition_row).expect("Module::try_add_function: test fixture");
        let carved = CalleeLink {
            symbol: None,
            producer: Some(trust_ir::Producer::TRust),
            instance_lane_spelling: true,
            foreign_signature: None,
            foreign_source: None,
        };
        let mut first = probe_decl_record(
            1,
            "local-unlowered:probe::single_generic|concrete-v1:a",
            "probe::single_generic",
        );
        first.link = carved.clone();
        let (alone, display) = emitted_decl_name(&module, std::slice::from_ref(&first), &first);
        assert!(
            alone.starts_with("!trust_bodyless_instance::probe::single_generic::"),
            "a definition displaying the path forces the collision form: {alone}"
        );
        assert_eq!(display, None);

        let empty = Module::new("instance_lane_two_instances_probe");
        let mut second = probe_decl_record(
            2,
            "local-unlowered:probe::single_generic|concrete-v1:b",
            "probe::single_generic",
        );
        second.link = carved;
        second.concrete_key = Some(crate::lineage::ConcreteCalleeKey::test_only(
            second.definition.expect("probe identity"),
            crate::lineage::ConcreteInstanceKind::Item,
            Vec::new(),
        ));
        let decls = vec![first, second];
        let (first_name, _) = emitted_decl_name(&empty, &decls, &decls[0]);
        let (second_name, _) = emitted_decl_name(&empty, &decls, &decls[1]);
        assert!(first_name.starts_with("!trust_bodyless_instance::probe::single_generic::"));
        assert!(second_name.starts_with("!trust_bodyless_instance::probe::single_generic::"));
        assert_ne!(first_name, second_name);
        let definition = decls[0].definition.expect("probe identity").symbol_suffix();
        // The relink reads `<class>:<path>|concrete-v1:<concrete>` out of the name, so each
        // row's own key spelling is the concrete key it is accepted for.
        for (name, own, other) in
            [(&first_name, "a", "b"), (&second_name, "b", "a")]
        {
            crate::instance_admission::declaration_name_matches(
                name,
                "probe::single_generic",
                &definition,
                own,
            )
            .expect("the frozen relink accepts the row for its own instance");
            assert!(
                crate::instance_admission::declaration_name_matches(
                    name,
                    "probe::single_generic",
                    &definition,
                    other,
                )
                .is_err(),
                "and refuses it for the other instance"
            );
        }
    }

    #[test]
    fn bodyless_declaration_name_includes_the_declaration_class() {
        let module = Module::new("declaration_class_name_collision");
        let first = probe_decl_record(0, "havoc:probe::same|concrete-v1:instance", "probe::same");
        let second = probe_decl_record(
            1,
            "local-unlowered:probe::same|concrete-v1:instance",
            "probe::same",
        );
        let decls = vec![first, second];

        let (first_name, _) = emitted_decl_name(&module, &decls, &decls[0]);
        let (second_name, _) = emitted_decl_name(&module, &decls, &decls[1]);
        assert!(first_name.starts_with(crate::link_symbol::UNLINKED_DECLARATION_PREFIX));
        assert!(second_name.starts_with(crate::link_symbol::UNLINKED_DECLARATION_PREFIX));
        assert_ne!(
            first_name, second_name,
            "class is part of declaration identity and must therefore change the reserved name"
        );
    }

    #[test]
    fn conflicting_declaration_occupies_its_id_and_is_fatal_before_joins() {
        let mut module = Module::new("conflicting_declaration_id_probe");
        let defined_ty = module
            .add_func_type(FuncTy {
                params: Vec::new(),
                returns: Vec::new(),
                is_vararg: false,
                abi: None,
            })
            .expect("Module::add_func_type: test fixture");
        module
            .try_add_function(Function::new(
                FuncId::new(0),
                "probe::defined",
                defined_ty,
                BlockId::new(0),
            ))
            .expect("Module::try_add_function: test fixture");

        let definition = crate::lineage::DefinitionIdentity::test_only(0xD3C1, 9);
        let concrete = crate::lineage::ConcreteCalleeKey::test_only(
            definition,
            crate::lineage::ConcreteInstanceKind::Item,
            Vec::new(),
        );
        let first =
            FuncTy { params: vec![Ty::U32], returns: vec![Ty::U32], is_vararg: false, abi: None };
        let second =
            FuncTy { params: vec![Ty::U64], returns: vec![Ty::U64], is_vararg: false, abi: None };
        let mut decls = Vec::new();
        let id = decl_id(
            &mut decls,
            1,
            "extern:probe::contradicted|concrete-v1:key".to_string(),
            "probe::contradicted".to_string(),
            None,
                crate::calling_convention::FunctionAbi::RUST,
            Some(definition),
            Some(&concrete),
            None,
            Some(&first),
            crate::ParamSignature::Unsigned,
            CalleeLink::default(),
        );
        assert_eq!(id, FuncId::new(1));
        assert_eq!(
            decl_id(
                &mut decls,
                1,
                "extern:probe::contradicted|concrete-v1:key".to_string(),
                "probe::contradicted".to_string(),
                None,
                crate::calling_convention::FunctionAbi::RUST,
                Some(definition),
                Some(&concrete),
                None,
                Some(&second),
                crate::ParamSignature::Unsigned,
                CalleeLink::default(),
            ),
            id,
        );
        assert!(matches!(decls[0].signature, DeclSigState::Conflict));

        let mut unsignable = Vec::new();
        let errors = append_declarations(&mut module, &decls, &mut unsignable);
        assert_eq!(
            errors.len(),
            1,
            "the contradiction must be an explicit assembly error"
        );
        assert!(
            unsignable.is_empty(),
            "the conflict placeholder is `is_vararg: false` and is already fatal; it must not \
             also be reported as an unsignable declaration"
        );
        let placeholder = module
            .function_by_id(id)
            .expect("conflict ID must remain occupied");
        assert!(
            placeholder
                .name
                .starts_with("!trust_conflicting_declaration::")
        );
        let appended_id = FuncId::new(module.functions.len() as u32);
        module
            .try_add_function(Function::new(
                appended_id,
                "probe::later_clean_origin",
                defined_ty,
                BlockId::new(0),
            ))
            .expect("Module::try_add_function: test fixture");
        assert_eq!(
            appended_id,
            FuncId::new(2),
            "a later append must never reuse the contradicted declaration's FuncId"
        );

        let source = include_str!("crate_module.rs");
        let conflict_gate = source
            .find("errors.append(&mut assembled.errors);")
            .expect("assembly conflict gate");
        // Trust (2026-09-17): the needle is ASSEMBLED — this test's own source is inside
        // `include_str!("crate_module.rs")`, and a literal here was the second match that
        // broke the `sole_offset` anchors of `validation_tripwire_order_tests` and
        // `crate_module_publication_order_tests` (each demands exactly ONE occurrence).
        let clean_join = source
            .find(concat!(
                "crate::clean_origin_join::", "prepare_clean_origin_with_rust_callees("
            ))
            .expect("Clean-origin append");
        assert!(
            conflict_gate < clean_join,
            "declaration contradictions must abort before any later identity-bearing join"
        );
    }

    /// Trust (wave-RETSPLIT): two bodies spelling ONE source return type as two module types
    /// must mint two declarations, not one poisoned row.
    ///
    /// THE DEFECT this pins. `struct_ty_rmw_opaque` registers a struct with `Ty::Unit`
    /// placeholder siblings for its non-pure lanes — at a field write AND at a whole-struct or
    /// field read through a reference — `map_ty`'s Adt arm registers it faithfully,
    /// `register_struct` dedups per body by `(DefId, GenericArgs)` and `add_struct_def` dedups
    /// structurally — so one callee's result is `Ty::Struct(9)` in a body that never routed
    /// through the RMW builder and `Ty::Struct(14)` in one that did, before the call. That used
    /// to set `ret_conflict` and abort the whole crate:
    ///
    ///   error: trust-ir-lower semantic finalization failed: conflicting bodyless declaration
    ///   observations for FuncId 252 key "local-unlowered:profiles::hardened|concrete-v1:019a.."
    ///
    /// (measured on aterm, seal trust-dac08891, `aterm-policy`/`aterm-forge` lib tests).
    #[test]
    fn contradicting_result_type_observations_split_instead_of_poisoning() {
        let mut module = Module::new("result_type_split_probe");
        let definition = crate::lineage::DefinitionIdentity::test_only(0xB0DE, 4);
        let concrete = crate::lineage::ConcreteCalleeKey::test_only(
            definition,
            crate::lineage::ConcreteInstanceKind::Item,
            Vec::new(),
        );
        let key = "local-unlowered:probe::make|concrete-v1:key";
        let faithful = Ty::Struct(StructId::new(9));
        let degraded = Ty::Struct(StructId::new(14));
        let mut decls = Vec::new();
        let observe = |decls: &mut Vec<DeclRecord>, ret: Option<Ty>| {
            decl_id(
                decls,
                0,
                key.to_string(),
                "probe::make".to_string(),
                ret,
                crate::calling_convention::FunctionAbi::RUST,
                Some(definition),
                Some(&concrete),
                Some(7),
                None,
                crate::ParamSignature::Unsigned,
                CalleeLink::default(),
            )
        };

        let first = observe(&mut decls, Some(faithful.clone()));
        let second = observe(&mut decls, Some(degraded.clone()));
        assert_ne!(
            first, second,
            "a contradicting result-type observation must get its OWN declaration"
        );
        assert_eq!(decls.len(), 2);
        assert_eq!(decls[0].key, key, "the first spelling keeps the unsuffixed key");
        assert_eq!(decls[1].key, format!("{key}|ret:{degraded:?}"));
        assert_eq!(decls[0].ret.as_ref(), Some(&faithful));
        assert_eq!(decls[1].ret.as_ref(), Some(&degraded));
        assert!(decls.iter().all(|d| !d.ret_conflict), "neither row may be poisoned");
        assert_eq!(
            decls[1].local_def_index, decls[0].local_def_index,
            "a TYPE split keeps the one exact source identity — what the Clean-origin join links on"
        );

        // Stable and order-independent: a later observation of either spelling rejoins its row.
        assert_eq!(observe(&mut decls, Some(faithful.clone())), first);
        assert_eq!(observe(&mut decls, Some(degraded)), second);
        // A site that binds no result asserts nothing and must not split.
        assert_eq!(observe(&mut decls, None), first);
        assert_eq!(decls.len(), 2);

        let mut unsignable = Vec::new();
        let errors = append_declarations(&mut module, &decls, &mut unsignable);
        assert!(errors.is_empty(), "the split must not be a producer error: {errors:?}");
        let returns: Vec<Vec<Ty>> = decls
            .iter()
            .map(|d| {
                let f = module.function_by_id(d.id).expect("declaration row");
                module.func_types[f.ty.index() as usize].returns.clone()
            })
            .collect();
        assert_eq!(
            returns,
            vec![vec![faithful], vec![Ty::Struct(StructId::new(14))]],
            "each declaration must return the type ITS OWN call sites bind"
        );
        assert!(
            module
                .functions
                .iter()
                .all(|f| !f.name.starts_with("!trust_conflicting_declaration::")),
            "no conflict placeholder may be emitted for a split"
        );
    }

    /// The split must NOT be a way around the adjacent identity tripwire. Trust: `decl_id`
    /// refuses first- or last-writer-wins on name / ABI / `local_def_index` by parking the row
    /// in `DeclSigState::Conflict`, and `local_def_index` is the LINKING authority for
    /// `link_clean_origin_edges`. An observation that contradicts the row on BOTH the result
    /// type and identity must therefore merge and refuse, never divert to a fresh row — two
    /// rows carrying two def_indexes would link to two different Clean definitions.
    #[test]
    fn identity_contradiction_merges_and_refuses_instead_of_splitting() {
        let mut module = Module::new("identity_contradiction_probe");
        let definition = crate::lineage::DefinitionIdentity::test_only(0xB0DE, 4);
        let concrete = crate::lineage::ConcreteCalleeKey::test_only(
            definition,
            crate::lineage::ConcreteInstanceKind::Item,
            Vec::new(),
        );
        let key = "local-unlowered:probe::make|concrete-v1:key";
        let observe = |decls: &mut Vec<DeclRecord>,
                       name: &str,
                       abi: crate::calling_convention::FunctionAbi,
                       local_def_index: Option<u32>,
                       ret: Ty| {
            decl_id(
                decls,
                0,
                key.to_string(),
                name.to_string(),
                Some(ret),
                abi,
                Some(definition),
                Some(&concrete),
                local_def_index,
                None,
                crate::ParamSignature::Unsigned,
                CalleeLink::default(),
            )
        };

        let mut decls = Vec::new();
        let first = observe(
            &mut decls,
            "probe::make",
            crate::calling_convention::FunctionAbi::RUST,
            Some(7),
            Ty::Struct(StructId::new(9)),
        );
        // Contradicts the row on the result type AND on every identity fact at once.
        let second = observe(
            &mut decls,
            "probe::OTHER",
            crate::calling_convention::FunctionAbi::C,
            Some(99),
            Ty::Struct(StructId::new(14)),
        );
        assert_eq!(
            first, second,
            "an identity contradiction must merge onto the one row, not mint a second"
        );
        assert_eq!(decls.len(), 1, "no `|ret:` split may bypass the identity check");
        assert!(decls[0].ret_conflict, "the result-type contradiction is still recorded");
        assert!(
            matches!(decls[0].signature, DeclSigState::Conflict),
            "name / ABI / local_def_index disagreement must park the row in Conflict"
        );

        let mut unsignable = Vec::new();
        let errors = append_declarations(&mut module, &decls, &mut unsignable);
        assert_eq!(errors.len(), 1, "the refusal must reach finalization: {errors:?}");
        assert!(
            errors[0].contains("(result type and signature)"),
            "the fatal message must name BOTH contradicted facts: {}",
            errors[0]
        );
        assert!(
            !errors[0].contains("  "),
            "the fatal message must not carry run-together padding: {}",
            errors[0]
        );
    }

    /// A caller record carrying ONE fn-pointer constant: `Ty::Func(FuncTyId(1))` over
    /// `fn(f64, f64) -> f64`, targeting `FuncId(fid)` with the given ledger entry.
    fn fnptr_caller(callee: CalleeRef) -> BodyRecord {
        let mut r = lineage_body_record(1, "probe::caller");
        r.func_types = vec![
            FuncTy { params: Vec::new(), returns: Vec::new(), is_vararg: false, abi: None },
            FuncTy {
                params: vec![Ty::F64, Ty::F64],
                returns: vec![Ty::F64],
                is_vararg: false,
                abi: None,
            },
        ];
        r.callees = vec![callee];
        r
    }

    fn target_with_sig(def_index: u32, params: Vec<Ty>) -> BodyRecord {
        let mut t = lineage_body_record(def_index, "probe::target");
        t.func_ty = Some(FuncTy { params, returns: vec![Ty::F64], is_vararg: false, abi: None });
        t
    }

    #[test]
    fn local_unlowered_declaration_carries_exact_source_def_index() {
        let caller = fnptr_caller(probe_callee(42, true, false));
        let resolution = resolve_callee(&caller, FuncId::new(42), &|_| None, &BodyMaps::default());
        let CalleeResolution::Decl { key, local_def_index, .. } = resolution else {
            panic!("an unspliced local target must become a declaration");
        };
        assert!(key.starts_with("local-unlowered:"), "{key}");
        assert_eq!(local_def_index, Some(42));
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
            origin: None,
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
        // Trust (#184 follow-on): THE HANDOFF, restated. This assertion used to read
        // `!body_sig_ok(...)` — "`fn() -> Name` resolves, and is still not MOVABLE". That was true
        // while `body_sig_ok` required `all(ty_table_free)`. #184 removed that requirement
        // deliberately, because both seam sites now remap through `BodyMaps`, and this test was
        // not updated with it — so it asserted a retired contract and main went red.
        //
        // The protection did not disappear; it MOVED, from a predicate to a remap fail-closure.
        // Asserting the move is the honest form of this check: `body_sig_ok` now admits the
        // widened signature, and `remap_func_ty` is what declines it when a component cannot be
        // resolved into the assembled module's numbering
        // (`test_remap_func_ty_is_the_wall_that_replaced_table_freedom`).
        let mut r = lineage_body_record(1, "probe::struct_bearing_sig");
        r.func_types = vec![
            FuncTy { params: Vec::new(), returns: Vec::new(), is_vararg: false, abi: None },
            FuncTy {
                params: Vec::new(),
                returns: vec![Ty::Struct(StructId::new(0))],
                is_vararg: false,
                abi: None,
            },
        ];
        assert!(
            body_sig_ok(&r, FuncTyId::new(1)),
            "post-#184 `fn() -> Name` RESOLVES and is movable; the remap, not this predicate, \
             is what refuses an unresolvable component"
        );
        // …and a vararg signature is still refused here, so the predicate is not vacuous.
        r.func_types[1].is_vararg = true;
        assert!(
            !body_sig_ok(&r, FuncTyId::new(1)),
            "`body_sig_ok` must still refuse a vararg signature"
        );
    }

    /// Trust (#184 follow-on): THE WALL THAT REPLACED TABLE-FREEDOM, and it had no test.
    ///
    /// `body_sig_ok` dropped its `all(ty_table_free)` requirement because both seam sites remap
    /// through `BodyMaps`. That moved the protection from a PREDICATE (tested by
    /// `test_every_newly_admitted_component_is_still_refused_by_the_splice_predicate`) to a REMAP
    /// FAIL-CLOSURE (tested by nothing). A wall with no test is how the retired one stayed
    /// asserted long enough to turn main red; this is the replacement's own test.
    ///
    /// `remap_ty`'s struct arm is `Ty::Struct((*struct_map.get(i)?)?)` — a DOUBLE `?`, so
    /// out-of-range and not-yet-interned are separate decline paths. Both are exercised.
    #[test]
    fn test_remap_func_ty_is_the_wall_that_replaced_table_freedom() {
        let sig = |params: Vec<Ty>, returns: Vec<Ty>| FuncTy {
            params,
            returns,
            is_vararg: false,
            abi: None,
        };

        // ACCEPT CONTROL. Without it every decline below passes against a `remap` that is
        // constantly `None`, which is exactly the vacuity this module keeps having to re-check.
        let resolved = BodyMaps {
            func_map: Vec::new(),
            enum_map: vec![Some(trust_ir::EnumId::new(7))],
            struct_map: vec![Some(StructId::new(3))],
            ty_map: Vec::new(),
            closure_map: Vec::new(),
        };
        let out = remap_func_ty(
            &sig(vec![Ty::Struct(StructId::new(0))], vec![Ty::Enum(trust_ir::EnumId::new(0))]),
            &resolved,
        )
        .expect("every component resolves");
        assert_eq!(
            out.params,
            vec![Ty::Struct(StructId::new(3))],
            "the param must be REMAPPED into module numbering, not copied through"
        );
        assert_eq!(out.returns, vec![Ty::Enum(trust_ir::EnumId::new(7))]);

        // DECLINE 1 — not-yet-interned (the inner `?`). This is the case #184's own comment
        // names: "a reference to a not-yet-interned def is a decline instead of a wrong id".
        let not_interned = BodyMaps {
            func_map: Vec::new(),
            enum_map: Vec::new(),
            struct_map: vec![None],
            ty_map: Vec::new(),
            closure_map: Vec::new(),
        };
        assert!(
            remap_func_ty(&sig(Vec::new(), vec![Ty::Struct(StructId::new(0))]), &not_interned)
                .is_none(),
            "a not-yet-interned struct must decline the whole signature"
        );

        // DECLINE 2 — out of range (the outer `?`).
        let empty = BodyMaps {
            func_map: Vec::new(),
            enum_map: Vec::new(),
            struct_map: Vec::new(),
            ty_map: Vec::new(),
            closure_map: Vec::new(),
        };
        assert!(
            remap_func_ty(&sig(vec![Ty::Struct(StructId::new(0))], Vec::new()), &empty).is_none(),
            "an out-of-range struct id must decline the whole signature"
        );

        // DECLINE 3 — NESTED. The recursion must fail closed too, or a widened signature could
        // smuggle an unresolvable id inside a tuple past a top-level-only check.
        assert!(
            remap_func_ty(
                &sig(vec![Ty::Tuple(vec![Ty::U64, Ty::Struct(StructId::new(0))])], Vec::new()),
                &not_interned,
            )
            .is_none(),
            "an unresolvable component NESTED in a tuple must decline the signature"
        );

        // …and the same tuple resolves when its component does — the nested accept control.
        assert!(
            remap_func_ty(
                &sig(vec![Ty::Tuple(vec![Ty::U64, Ty::Struct(StructId::new(0))])], Vec::new()),
                &resolved,
            )
            .is_some(),
            "a resolvable nested component must NOT decline"
        );
    }

    /// A return-type disagreement is the same defect on the other side of the arrow.
    #[test]
    fn test_fnptr_target_sig_refuses_return_mismatch() {
        let caller = fnptr_caller(probe_callee(42, true, false));
        let mut target = target_with_sig(42, vec![Ty::F64, Ty::F64]);
        target.func_ty = Some(FuncTy {
            params: vec![Ty::F64, Ty::F64],
            returns: Vec::new(),
            is_vararg: false,
            abi: None,
        });
        let records = vec![target];
        assert!(!fnptr_target_sig_ok(&caller, &records, FuncId::new(42), FuncTyId::new(1)));
    }

    /// A forced-bodyless edge with an exact concrete key is not the legacy unresolved-havoc
    /// spelling. Reifying that exact instance supplies its declaration signature while body
    /// linking remains disabled; discarding the observation would make direct + reified uses of
    /// the same instance order-dependent. Admitted here because the local record's signature
    /// EQUALS the claim — the pin's comparison branch, not the forced flag, admits it.
    #[test]
    fn test_fnptr_target_sig_admits_exact_concrete_bodyless_edge() {
        let caller = fnptr_caller(probe_callee(42, true, true));
        let records = vec![target_with_sig(42, vec![Ty::F64, Ty::F64])];
        assert!(
            fnptr_target_sig_ok(&caller, &records, FuncId::new(42), FuncTyId::new(1)),
            "an exact concrete bodyless edge must retain the signature supplied by its FnDef site"
        );
    }

    /// Ratification review 2026-09-28 (the RED this restores): the pin refused every
    /// forced-havoc edge; W1 (8932acd798) admitted a forced edge with a concrete key BEFORE any
    /// comparison, so a claimed `fn(f64, f64) -> f64` against a local record signed
    /// `[env, f64, f64] -> f64` — the closure-env arity hole — was admitted. It must be refused
    /// exactly as the same edge without the forced flag is
    /// (`test_fnptr_target_sig_refuses_closure_env_arity_mismatch`). RED at 2b05b645a1.
    #[test]
    fn test_fnptr_target_sig_refuses_forced_concrete_edge_against_a_contradicting_record() {
        let forced = fnptr_caller(probe_callee(42, true, true));
        let records = vec![target_with_sig(42, vec![Ty::Ptr, Ty::F64, Ty::F64])];
        assert!(
            !fnptr_target_sig_ok(&forced, &records, FuncId::new(42), FuncTyId::new(1)),
            "a forced concrete edge must not be admitted over a record that contradicts its claim"
        );
        // Control: the extern and unrecorded branches still admit a forced concrete edge, as the
        // pin admitted those targets (they can only become declarations).
        let forced_extern = fnptr_caller(probe_callee(42, false, true));
        assert!(fnptr_target_sig_ok(&forced_extern, &records, FuncId::new(42), FuncTyId::new(1)));
        assert!(fnptr_target_sig_ok(&forced, &[], FuncId::new(42), FuncTyId::new(1)));
    }

    /// `fnptr_caller` whose body actually CARRIES the constant, so the whole splice decision
    /// (`splice_refusal`) is asked, not only the predicate in isolation.
    fn fnptr_splice_probe(callee: CalleeRef) -> BodyRecord {
        let fid = callee.func_id;
        let mut r = fnptr_caller(callee);
        let mut block = trust_ir::Block::new(BlockId::new(0));
        block.body.push(InstrNode::new(Inst::Const {
            ty: Ty::Func(FuncTyId::new(1)),
            value: Constant::FnDef(fid),
        }));
        r.function.as_mut().expect("the probe record carries a function").blocks.push(block);
        r
    }

    /// D20 (2026-09-28): THE DECLARED ARITY. A target pass 2 can only turn into a bodyless
    /// DECLARATION is SIGNED with the constant's claimed `Ty::Func`: since W1 (8932acd798) the
    /// reified signature is `decl_id`'s `full_sig`, it becomes `DeclSigState::Exact`, and
    /// `append_declarations` prefers it over the ledger's recovered `params`. So a claim whose
    /// arity differs from the callee's DECLARED parameter list (`ParamSignature::Signed`, read
    /// from `tcx.fn_sig` at the instance) must not splice: splicing it publishes the false arity
    /// as the declaration's signature, and no direct call has to exist for that to happen.
    ///
    /// Five declaration-bound shapes: a forced concrete key that is LOCAL with a record (the
    /// record here EQUALS the claim, so the record comparison
    /// `test_fnptr_target_sig_refuses_forced_concrete_edge_against_a_contradicting_record` pins
    /// cannot be what refuses it), a forced key that is cross-crate or unrecorded, and the same
    /// two targets unforced. The CONTROL on every shape is the same body with the declared list
    /// at the claimed arity, which still splices: the refusal is the arity comparison, not a ban
    /// on the class (`test_fnptr_target_sig_admits_targets_that_can_only_become_declarations`
    /// keeps the unsigned case).
    #[test]
    fn test_a_declaration_bound_fnptr_whose_declared_arity_differs_does_not_splice() {
        let local_record = vec![target_with_sig(42, vec![Ty::F64, Ty::F64])];
        // (shape, is_local, force_havoc, records)
        let shapes: [(&str, bool, bool, &[BodyRecord]); 5] = [
            ("forced concrete key over an agreeing local record", true, true, &local_record),
            ("forced cross-crate target", false, true, &local_record),
            ("forced unrecorded local target", true, true, &[]),
            ("cross-crate target", false, false, &local_record),
            ("unrecorded local target", true, false, &[]),
        ];
        for (shape, is_local, force_havoc, records) in shapes {
            for (declared, admitted) in [
                (vec![Ty::F64], false),
                (vec![Ty::F64, Ty::F64, Ty::F64], false),
                (Vec::new(), false),
                (vec![Ty::F64, Ty::F64], true),
            ] {
                let mut callee = probe_callee(42, is_local, force_havoc);
                callee.params = crate::ParamSignature::Signed(declared.clone());
                let caller = fnptr_splice_probe(callee);
                assert_eq!(
                    fnptr_target_sig_ok(&caller, records, FuncId::new(42), FuncTyId::new(1)),
                    admitted,
                    "{shape}: declared {declared:?} against the claimed fn(f64, f64) -> f64"
                );
                assert_eq!(
                    splice_refusal(&caller, records),
                    (!admitted).then_some(SpliceRefusal::FnPtrConstant),
                    "{shape}: declared {declared:?} — the decision must reach the splice"
                );
            }
        }
    }

    /// Ratification review 2026-09-28 (the RED this restores): `decl_ret` answers a fn-pointer
    /// RETURN as the pin did — it does not remap — even when `func_map` holds that signature
    /// for a fn-pointer PARAMETER. At `2b05b645a1` it went through `BodyMaps::remap` and its
    /// `func_map`, so `call_result_arity_incoherent` stopped refusing a call that binds a
    /// fn-pointer result; the parameter side (`decl_params`, what `5e29156632` was for) still
    /// maps.
    #[test]
    fn test_decl_ret_does_not_remap_a_fn_pointer_return_through_the_param_map() {
        let mut maps = BodyMaps::default();
        maps.func_map = vec![Some(FuncTyId::new(7))];
        let mut c = probe_callee(42, false, false);
        c.ret_ty = Some(Ty::Func(FuncTyId::new(0)));
        assert_eq!(decl_ret(&c, &maps), None, "a fn-pointer return stays un-remapped");
        assert_eq!(
            maps.remap(&Ty::Func(FuncTyId::new(0))),
            Some(Ty::Func(FuncTyId::new(7))),
            "control: the parameter path still maps the same id"
        );
        c.ret_ty = Some(Ty::U32);
        assert_eq!(decl_ret(&c, &maps), Some(Ty::U32), "control: a scalar return still remaps");
    }

    /// A target with no record in this crate (cross-crate, or a local `DefIndex` never recorded)
    /// cannot be LINKED: pass 2 mints a bodyless declaration and, since W1, signs it with the
    /// claimed sig itself (`DeclSigState::Exact`). With an UNSIGNED ledger (`probe_callee`'s)
    /// nothing states another arity, so there is nothing for the claim to contradict and the
    /// target is admitted; a declared arity that differs is refused instead
    /// (`test_a_declaration_bound_fnptr_whose_declared_arity_differs_does_not_splice`). Returns
    /// are not compared on these branches — the named residual on `fnptr_target_sig_ok`.
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

    /// No ledger entry, or a malformed pair behind one body-local `FuncId`: refuse rather than
    /// pick.
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
        let assembled = assemble("direct_authority_tripwire", &[], &BTreeSet::new());
        let coverage = coverage_json(
            "direct_authority_tripwire",
            &assembled.coverage_rows,
            assembled.spliced,
            assembled.declarations,
            &crate::clean_origin_join::CleanOriginJoinSummary::not_recorded(),
        )
        .expect("empty coverage inventory is resolved");

        // Trust (Step 2/3, owner directive 2026-08-30): the const moved to the
        // obligation-bearing-pending tier. What this test pins is what did NOT
        // move: neither authority axis, and the strict-verification refusal.
        assert_eq!(
            DIRECT_OBLIGATION_CAPABILITY,
            DirectObligationCapability::ObligationBearingPending
        );
        assert!(!DIRECT_OBLIGATION_CAPABILITY.grants_proof_authority());
        assert!(!DIRECT_OBLIGATION_CAPABILITY.emits_native_verification_requests());
        assert!(assembled.module.proof_obligations.is_empty());
        assert!(
            !assembled.module.proof_summary().is_fully_verified_strict(),
            "an empty direct obligation table must never mean strictly verified"
        );
        assert!(
            coverage.contains("\"direct_obligation_capability\": \"obligation-bearing-pending-v2\"")
        );
        assert!(coverage.contains("\"proof_authority\": false"));
        assert!(coverage.contains("\"native_verification_requests\": false"));
        assert!(direct_authority_inventory_errors(&assembled.module).is_empty());
    }

    /// Trust (Step 2/3): the post-birth pin the tier move requires. One
    /// conforming Pending direct row passes the RECORDED tier's inventory
    /// check and still FAILS the pre-birth arm — so the tier split is real,
    /// not two spellings of one check.
    #[test]
    fn a_conforming_pending_row_passes_only_the_recorded_tier() {
        let module = crate::direct_obligations::module_with_conforming_pending_row_for_tests();
        assert!(
            crate::direct_obligations::inventory_errors_at_tier(
                &module,
                DIRECT_OBLIGATION_CAPABILITY.tier(),
            )
            .is_empty(),
            "a conforming Pending direct row must pass the recorded tier"
        );
        assert!(
            !crate::direct_obligations::inventory_errors_at_tier(
                &module,
                crate::direct_obligations::DirectObligationTier::StructuralParityOnly,
            )
            .is_empty(),
            "the pre-birth arm must still refuse the same row"
        );
        assert!(
            !direct_authority_inventory_errors(&module).is_empty(),
            "runs 1-3 delegate to the pre-birth arm and must refuse it too"
        );
    }

    #[test]
    fn direct_thir_authority_inventory_fails_closed_on_future_claim_wiring() {
        let mut module = Module::new("direct_authority_violation");
        let ty = module
            .add_func_type(FuncTy {
                params: Vec::new(),
                returns: Vec::new(),
                is_vararg: false,
                abi: None,
            })
            .expect("Module::add_func_type: test fixture");
        let mut function = Function::new(FuncId::new(0), "direct", ty, BlockId::new(0));
        function.proofs.push(trust_ir::proof::ProofAnnotation::NoOverflow);
        function.summary = Some(trust_ir::FunctionSummary::new());
        module.try_add_function(function).expect("Module::try_add_function: test fixture");
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
        let ty = module
            .add_func_type(FuncTy {
                params: Vec::new(),
                returns: Vec::new(),
                is_vararg: false,
                abi: None,
            })
            .expect("Module::add_func_type: test fixture");
        // The shape a lowered Clean `def` would have: real executable content,
        // empty `proofs`, no `summary`.
        let plain = Function::new(FuncId::new(0), "clean_def_gcd", ty, BlockId::new(0));
        assert!(plain.proofs.is_empty(), "the lowered-def shape carries no claims");
        assert!(plain.summary.is_none(), "the lowered-def shape carries no summary");
        module.try_add_function(plain).expect("Module::try_add_function: test fixture");

        assert!(
            direct_authority_inventory_errors(&module).is_empty(),
            "populating `functions` is not proof authority; the tripwire bounds \
             obligations/certificates/diagnostics/claims/summaries/spec-proofs/linked-specs"
        );
        // Trust (Step 2/3, owner directive 2026-08-30): the recorded tier
        // moved to ObligationBearingPending. The property this test pins —
        // a populated `functions` table is not authority — is tier-independent
        // and unchanged; the variant assert simply tracks the recorded const.
        assert_eq!(
            DIRECT_OBLIGATION_CAPABILITY,
            DirectObligationCapability::ObligationBearingPending,
            "and the recorded tier stays the one the owner signed"
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
    fn generated_inventory_cannot_omit_duplicate_or_invent_a_callback() {
        let hir_plus_generated = [2, 7, 23];
        assert!(body_inventory_errors(&hir_plus_generated, &[2, 7, 23]).is_empty());
        assert!(!body_inventory_errors(&hir_plus_generated, &[2, 7]).is_empty());
        assert!(!body_inventory_errors(&hir_plus_generated, &[2, 7, 23, 23]).is_empty());
        assert!(!body_inventory_errors(&hir_plus_generated, &[2, 7, 24]).is_empty());
    }

    #[test]
    fn generated_ungated_record_cannot_splice_even_with_forged_producer_label() {
        let mut record = lineage_body_record(7, "generated");
        let mut block = trust_ir::Block::new(BlockId::new(0));
        block.body.push(InstrNode::new(Inst::Return { values: Vec::new() }));
        record.function.as_mut().unwrap().blocks.push(block);
        assert!(splice_ok(&record, &[]));
        record.generated_ungated = true;
        for producer in [None, Some(trust_ir::Producer::TRust), Some(trust_ir::Producer::TrustIr)] {
            record.function.as_mut().unwrap().producer = producer;
            assert!(!splice_ok(&record, &[]));
        }
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
        let ty = module
            .add_func_type(FuncTy {
                params: Vec::new(),
                returns: Vec::new(),
                is_vararg: false,
                abi: None,
            })
            .expect("Module::add_func_type: test fixture");
        module
            .try_add_function(
                Function::new(FuncId::new(0), "direct", ty, BlockId::new(0))
                    .with_producer(trust_ir::Producer::TRust),
            )
            .expect("Module::try_add_function: test fixture");
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
        let base = coverage_json("publication", &[], 0, 0, &crate::clean_origin_join::CleanOriginJoinSummary::not_recorded()).expect("empty coverage is resolved");
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
    #[test]
    fn same_shaped_source_abi_conflict_is_sticky_even_when_target_aliases_agree() {
        use crate::calling_convention::FunctionAbi;
        use rustc_abi::{CanonAbi, ExternAbi};
        let mut decls = Vec::new();
        let definition = crate::lineage::DefinitionIdentity::test_only(0xAB1, 7);
        let system_c = FunctionAbi::test_only(ExternAbi::System { unwind: false }, Some(CanonAbi::C));
        let observe = |decls: &mut Vec<DeclRecord>, abi| decl_id(
            decls, 0, "extern:abi-probe".into(), "abi-probe".into(), Some(Ty::I32),
            abi, Some(definition), None, None, None,
            crate::ParamSignature::Signed(vec![Ty::I32]), CalleeLink::default(),
        );
        let first = observe(&mut decls, FunctionAbi::C);
        assert_eq!(observe(&mut decls, system_c), first);
        assert!(matches!(decls[0].signature, DeclSigState::Conflict));
        assert_eq!(observe(&mut decls, FunctionAbi::C), first);
        assert_eq!(decls.len(), 1);
        assert!(matches!(decls[0].signature, DeclSigState::Conflict));
        let mut module = Module::new("abi-conflict");
        assert!(!append_declarations(&mut module, &decls, &mut Vec::new()).is_empty());
    }

    fn foreign_prototype_fixture(variadic: bool) -> FuncTy {
        use trust_ir::signature_abi::*;
        let scalar = |place, bytes, align, extension| AbiArgument {
            size: bytes, align,
            mode: AbiPassMode::Direct(AbiScalar {
                register: AbiRegister { class: AbiRegisterClass::Integer, bytes },
                source_offset: 0, source_bytes: bytes, value_bits: (bytes * 8) as u16,
                attributes: AbiAttributes { extension, ..AbiAttributes::default() },
            }),
            bindings: vec![AbiBinding {
                place, source_offset: 0, source_bytes: bytes, carrier_offset: 0, carrier_bytes: bytes,
            }],
        };
        FuncTy {
            params: vec![Ty::Ptr, Ty::I8], returns: vec![Ty::I32], is_vararg: variadic,
            abi: Some(SignatureAbi {
                target: AbiTarget {
                    triple: "aarch64-apple-darwin".into(), data_layout: "e-p:64:64".into(),
                    abi: String::new(), cpu: "generic".into(), features: Vec::new(),
                    target_spec: "fixture-original-target-spec".into(), pointer_bytes: 8,
                    little_endian: true,
                },
                frontend: AbiFrontend { name: "test-source".into(), revision: "1".into() },
                convention: "C".into(), lowered_convention: trust_ir::CallingConv::C,
                source_abi: "C".into(), can_unwind: false, variadic, fixed_count: 2,
                arguments: vec![
                    scalar(AbiBindingPlace::Parameter(0), 8, 8, AbiExtension::None),
                    scalar(AbiBindingPlace::Parameter(1), 1, 1, AbiExtension::Sign),
                ],
                result: scalar(AbiBindingPlace::Result(0), 4, 4, AbiExtension::None),
            }),
        }
    }

    fn foreign_prototype_decl(variadic: bool) -> DeclRecord {
        let mut decl = probe_decl_record(0, "extern:foreign", "foreign");
        decl.abi = if variadic {
            crate::calling_convention::FunctionAbi::test_only_variadic(
                rustc_abi::ExternAbi::C { unwind: false }, Some(rustc_abi::CanonAbi::C))
        } else { crate::calling_convention::FunctionAbi::C };
        decl.ret = Some(Ty::I32);
        decl.link.foreign_signature = Some(foreign_prototype_fixture(variadic));
        decl
    }

    #[test]
    fn original_foreign_variadic_prefix_is_not_the_unknown_signature_encoding() {
        let decl = foreign_prototype_decl(true);
        assert!(decl.params.signature().is_none(), "legacy reader cannot sign a variadic item");
        let mut module = Module::new("foreign-prefix");
        assert!(append_declarations(&mut module, &[decl], &mut Vec::new()).is_empty());
        let function = &module.functions[0];
        let signature = module.func_type(function.ty).unwrap();
        assert_eq!(signature.params, [Ty::Ptr, Ty::I8]);
        assert!(signature.is_vararg);
        assert_eq!(signature.abi.as_ref().unwrap().fixed_count, 2);
        signature.abi.as_ref().unwrap().validate(signature).unwrap();
    }

    #[test]
    fn foreign_abi_survives_the_real_module_codec_and_changes_its_digest() {
        let decl = foreign_prototype_decl(true);
        let mut module = Module::new("foreign-codec");
        module.target_info = Some(trust_ir::TargetInfo {
            triple: "aarch64-apple-darwin".into(), pointer_size: 8,
            endianness: trust_ir::Endianness::Little, abi: None,
            struct_passing: trust_ir::StructPassingPolicy::Unclassified,
        });
        assert!(append_declarations(&mut module, &[decl], &mut Vec::new()).is_empty());
        let before = module.stable_digest();
        let bytes = trust_ir::binary::serialize_module(&module).unwrap();
        let decoded = trust_ir::binary::deserialize_module(&bytes).unwrap();
        assert_eq!(decoded.stable_digest(), before);
        assert_eq!(decoded.func_types[0], module.func_types[0]);
        assert!(decoded.functions[0].fn_abi(&decoded).unwrap().unwrap().is_vararg());
        module.func_types[0].abi.as_mut().unwrap().source_abi = "system".into();
        assert_ne!(module.stable_digest(), before, "source spelling is identity, not only canonical C");
    }

    #[test]
    fn source_prototype_cannot_resurrect_short_or_conflicting_calls() {
        for damage in 0..6 {
            let mut decl = foreign_prototype_decl(false);
            match damage {
                0 => { decl.params.withdraw(); }
                1 => { decl.params_conflict = true; }
                2 => { decl.params = crate::ParamSignature::Signed(vec![Ty::Ptr, Ty::U8]); }
                3 => { decl.ret = Some(Ty::U32); }
                4 => { decl.abi = crate::calling_convention::FunctionAbi::UNKNOWN; }
                5 => { decl.link.foreign_signature.as_mut().unwrap().abi.as_mut().unwrap().source_abi = "system".into(); }
                _ => unreachable!(),
            }
            assert!(checked_foreign_declaration_signature(&decl).is_err(), "damage {damage}");
            assert!(!append_declarations(&mut Module::new("short-foreign"), &[decl], &mut Vec::new()).is_empty());
        }
    }

    #[test]
    fn plain_c_function_pointer_keeps_its_existing_callable_type_boundary() {
        let mut decl = foreign_prototype_decl(false);
        let mut pointer = foreign_prototype_fixture(false);
        pointer.abi = None;
        decl.signature = DeclSigState::Exact(pointer.clone());
        assert_eq!(checked_foreign_declaration_signature(&decl).unwrap(), None);
        let mut module = Module::new("foreign-pointer");
        assert!(append_declarations(&mut module, &[decl.clone()], &mut Vec::new()).is_empty());
        assert_eq!(module.func_types[0], pointer);
        pointer.params[1] = Ty::U8;
        decl.signature = DeclSigState::Exact(pointer);
        assert!(checked_foreign_declaration_signature(&decl).is_err());
    }

    #[test]
    fn absent_or_contradictory_declaration_abi_never_uses_the_c_default() {
        use crate::calling_convention::FunctionAbi;
        for abi in [FunctionAbi::UNKNOWN, FunctionAbi::CONFLICT] {
            let mut row = probe_decl_record(0, "unknown:abi", "abi-probe");
            row.abi = abi;
            row.params = crate::ParamSignature::Signed(Vec::new());
            let mut module = Module::new("abi-absent");
            let errors = append_declarations(&mut module, &[row], &mut Vec::new());
            assert!(errors.iter().any(|e| e.contains("source calling convention")), "{errors:?}");
        }
    }

    #[test]
    fn rust_cold_keeps_the_original_unsigned_rust_declaration_refusal() {
        use crate::calling_convention::FunctionAbi;
        use rustc_abi::{CanonAbi, ExternAbi};
        let mut row = probe_decl_record(0, "extern:cold", "cold-probe");
        row.abi = FunctionAbi::test_only(ExternAbi::RustCold, Some(CanonAbi::RustCold));
        row.params = crate::ParamSignature::Unsigned;
        let mut module = Module::new("cold-unsigned");
        let mut recorded = Vec::new();
        assert!(append_declarations(&mut module, &[row], &mut recorded).is_empty());
        assert_eq!(recorded.len(), 1, "the exact current declaration is recorded");
        assert_eq!(module.functions[0].calling_conv, trust_ir::CallingConv::RustCold);
        assert_eq!(surviving_unsignable_declarations(&module, &recorded).len(), 1);
        assert_eq!(unsignable_declaration_refusals(&module, &recorded, &BTreeSet::new()).len(), 1);
        let signed = module.add_func_type(FuncTy {
            params: vec![Ty::U64], returns: Vec::new(), is_vararg: false, abi: None,
        }).expect("genuinely recovered signature");
        module.functions[0].ty = signed;
        assert!(surviving_unsignable_declarations(&module, &recorded).is_empty());
        assert!(unsignable_declaration_refusals(&module, &recorded, &BTreeSet::new()).is_empty());
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
            [
                "VarRef(unbound)",
                "Borrow(unbound local)",
                "AssignOp(unbound local)",
                "Borrow(inner unlowered)",
            ],
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
            // Carved out of `Borrow(non-local place)` 2026-08-11: a genuine refusal by
            // `shared_reborrow_arm` after the reborrow reached `ReborrowTarget::Ptr`. Its echo
            // sibling `Borrow(inner unlowered)` went the other way, into `CASCADE_TAGS`.
            "Borrow(ptr reborrow refused)",
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
            pointer_width: false,
            site_args: None,
            str_global: global,
            static_global: None,
            promoted_global: None,
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
            section: None,
            visibility: trust_ir::Visibility::Default,
            retained: false,
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

    /// Trust (vtable slice 15): `def_field_ok` admits a first-class array FIELD exactly when
    /// its types entry is TABLE-FREE (the scalar-element spelling pass 1 pre-interns before
    /// the def tables); a struct-referencing entry stays refused (the cross-table cycle the
    /// pre-slice-15 refusal guarded), as does an out-of-range id.
    #[test]
    fn test_def_field_ok_scalar_element_array_field() {
        let mut r = minimal_record();
        r.types = vec![Ty::U8, Ty::Struct(StructId::new(0))];
        let b = def_field_entry_bounds(&r);
        assert!(def_field_ok(&r, &Ty::Array(TyId::new(0), 4), 0, &b), "scalar-element: admitted");
        assert!(
            def_field_ok(&r, &Ty::Array(TyId::new(0), 0), 0, &b),
            "zero-length scalar: admitted"
        );
        assert!(
            !def_field_ok(&r, &Ty::Array(TyId::new(1), 0), 0, &b),
            "unregistered struct-referencing entry: refused"
        );
        assert!(!def_field_ok(&r, &Ty::Array(TyId::new(9), 4), 0, &b), "out of range: refused");
        // The enum sibling keeps refusing arrays outright — parity with the producer's
        // enum_variant_field_admissible, which has no array arm either.
        assert!(!enum_def_field_ok(&r, &Ty::Array(TyId::new(0), 4)));
    }

    fn one_field_struct(id: u32, ty: Ty) -> trust_ir::StructDef {
        trust_ir::StructDef {
            id: StructId::new(id),
            name: format!("S{id}"),
            fields: vec![trust_ir::FieldDef { name: "f".into(), ty, offset: None }],
            size: None,
            align: None,
            repr: trust_ir::StructRepr::Rust,
            origin: None,
        }
    }

    /// Trust (2026-09-23): an array FIELD whose element entry is not table-free is admitted by
    /// the rules `def_field_ok` applies to the element as a field — exactly the fields the old
    /// `Ty::Tuple([T; N])` spelling carried inline and admitted through the tuple arm: a nested
    /// array, an array of tuples of arrays, an array of tuples naming an EARLIER struct (the
    /// nested-first `sid < i` rule, now a bound) or a resolvable enum. An entry that IS a
    /// direct struct element now carries that same earlier-struct bound explicitly;
    /// direct enum elements, forward references and out-of-range IDs stay refused.
    #[test]
    fn test_def_field_ok_array_field_admits_what_the_tuple_spelling_admitted() {
        let mut r = minimal_record();
        r.structs = vec![one_field_struct(0, Ty::U8)];
        r.enums = vec![trust_ir::EnumDef::new(
            trust_ir::EnumId::new(0),
            "K",
            vec![trust_ir::EnumVariant { name: "A".into(), fields: vec![], field_names: vec![] }],
        )];
        r.types = vec![
            Ty::U32,                                                     // 0
            Ty::Array(TyId::new(0), 2),                                  // 1: [u32; 2]
            Ty::Tuple(vec![Ty::Array(TyId::new(1), 2), Ty::U8]),         // 2: ([[u32; 2]; 2], u8)
            Ty::Struct(StructId::new(0)),                                // 3: S
            Ty::Array(TyId::new(3), 2),                                  // 4: [S; 2]
            Ty::Array(TyId::new(6), 2),                                  // 5: a FORWARD reference
            Ty::U8,                                                      // 6
            Ty::Tuple(vec![Ty::Struct(StructId::new(0)), Ty::U8]),       // 7: (S, u8)
            Ty::Tuple(vec![Ty::Enum(trust_ir::EnumId::new(0)), Ty::U8]), // 8: (E, u8)
        ];
        let b = def_field_entry_bounds(&r);
        assert_eq!(
            b,
            vec![Some(0), Some(0), Some(0), Some(1), Some(1), None, Some(0), Some(1), Some(0)]
        );
        let arr = |k: u32| Ty::Array(TyId::new(k), 2);
        assert!(def_field_ok(&r, &arr(1), 0, &b), "[[u32; 2]; 2]");
        assert!(def_field_ok(&r, &arr(2), 0, &b), "[([[u32; 2]; 2], u8); 2]");
        assert!(def_field_ok(&r, &arr(8), 0, &b), "[(E, u8); 2]");
        assert!(!def_field_ok(&r, &arr(7), 0, &b), "[(S, u8); 2] in struct 0: S is not earlier");
        assert!(def_field_ok(&r, &arr(7), 1, &b), "[(S, u8); 2] in struct 1: S is earlier");
        assert!(def_field_ok(&r, &arr(3), 1, &b), "[S; 2]: exact earlier registered struct");
        assert!(def_field_ok(&r, &arr(4), 1, &b), "[[S; 2]; 2]: same transitive bound");
        assert!(!def_field_ok(&r, &arr(3), 0, &b), "[Self; 2]: not earlier");
        assert!(!def_field_ok(&r, &arr(4), 0, &b), "[[Self; 2]; 2]: not earlier");
        assert!(!def_field_ok(&r, &arr(5), 1, &b), "forward reference");
        assert!(!def_field_ok(&r, &arr(9), 1, &b), "out of range");
    }

    #[test]
    fn nonempty_struct_array_elements_require_resolved_earlier_positional_ids() {
        let mut r = minimal_record();
        r.structs = vec![one_field_struct(0, Ty::U8), one_field_struct(1, Ty::U16)];
        r.enums = vec![trust_ir::EnumDef::new(
            trust_ir::EnumId::new(0), "E",
            vec![trust_ir::EnumVariant { name: "A".into(), fields: vec![], field_names: vec![] }],
        )];
        r.types = vec![
            Ty::Struct(StructId::new(0)),
            Ty::Struct(StructId::new(1)),
            Ty::Struct(StructId::new(2)),
            Ty::Enum(trust_ir::EnumId::new(0)),
        ];
        let bounds = def_field_entry_bounds(&r);
        let array = |k| Ty::Array(TyId::new(k), 2);
        assert!(def_field_ok(&r, &array(0), 1, &bounds));
        assert!(!def_field_ok(&r, &array(1), 1, &bounds), "self/forward dependency");
        assert!(!def_field_ok(&r, &array(2), 1, &bounds), "unregistered element");
        assert!(!def_field_ok(&r, &array(3), 1, &bounds), "direct enum lane stays closed");
        assert!(!def_field_ok(&r, &array(0), 1, &[]), "no computed earlier-entry bound");
        r.structs[0].id = StructId::new(9);
        let wrong = def_field_entry_bounds(&r);
        assert!(!def_field_ok(&r, &array(0), 1, &wrong), "wrong positional definition ID");
    }

    /// Trust: the typed registered-struct extension preserves every historical refusal for
    /// other table-indexed zero-array elements. It also requires an exact earlier declaration,
    /// never a self/forward reference or merely an in-range number with the wrong row ID.
    #[test]
    fn test_def_field_ok_zero_array_struct_keeps_other_indexed_elements_closed() {
        let mut r = minimal_record();
        r.structs = vec![one_field_struct(0, Ty::U8)];
        r.types = vec![
            Ty::U8,                                                // 0
            Ty::Tuple(vec![Ty::Struct(StructId::new(0)), Ty::U8]), // 1: (S, u8)
            Ty::Ref(Box::new(Ty::Struct(StructId::new(0)))),       // 2: &S
            Ty::Array(TyId::new(0), 2),                            // 3: [u8; 2]
            Ty::Tuple(vec![Ty::U8, Ty::U16]),                      // 4: (u8, u16)
            Ty::Array(TyId::new(1), 0),                            // 5: [(S, u8); 0] as an ENTRY
            Ty::Struct(StructId::new(0)),                         // 6: exact registered S
        ];
        let b = def_field_entry_bounds(&r);
        let zero = |k: u32| Ty::Array(TyId::new(k), 0);
        assert!(def_field_ok(&r, &zero(0), 1, &b), "[u8; 0]: table-free element, pin admitted");
        assert!(def_field_ok(&r, &zero(4), 1, &b), "[(u8, u16); 0]: table-free, pin admitted");
        assert!(!def_field_ok(&r, &zero(1), 1, &b), "[(S, u8); 0]: pin refused");
        assert!(!def_field_ok(&r, &zero(2), 1, &b), "[&S; 0]: pin refused");
        assert!(!def_field_ok(&r, &zero(3), 1, &b), "[[u8; 2]; 0]: pin refused");
        assert!(def_field_ok(&r, &zero(6), 1, &b), "[S; 0]: exact earlier registered struct");
        assert!(!def_field_ok(&r, &zero(6), 0, &b), "[Self; 0]: not earlier");
        assert!(def_field_ok(&r, &Ty::Array(TyId::new(6), 1), 1, &b),
            "[S; 1]: exact earlier registered struct in the nonempty lane");
        let mut wrong_id = minimal_record();
        wrong_id.structs = vec![one_field_struct(1, Ty::U8)];
        wrong_id.types = r.types.clone();
        let bad_bounds = def_field_entry_bounds(&wrong_id);
        assert!(!def_field_ok(&wrong_id, &zero(6), 1, &bad_bounds), "wrong positional definition ID");
        assert!(!def_field_ok(&wrong_id, &Ty::Array(TyId::new(6), 1), 1, &bad_bounds),
            "nonempty array also refuses the wrong positional definition ID");
        // Nested: a non-zero array over the zero-length entry 5 is refused through the bound too.
        assert_eq!(b[5], None, "[(S, u8); 0] is no admissible element entry");
        assert!(!def_field_ok(&r, &Ty::Array(TyId::new(5), 2), 1, &b), "[[(S, u8); 0]; 2]");
    }

    /// Trust (2026-09-23): a fn-pointer / closure SIGNATURE is table-free exactly when the old
    /// `Ty::Tuple([T; N])` spelling made it so: an array of tuples, units or nested such arrays
    /// is (it was carried inline), an array of scalars or structs, or of length 0, is not (it was
    /// already a first-class `Ty::Array`). And two signatures from DIFFERENT bodies compare
    /// equal through their own types tables, never by raw `TyId`.
    #[test]
    fn test_signature_arrays_are_table_free_as_the_tuple_spelling_was_and_compare_across_tables() {
        let mut r = minimal_record();
        r.types = vec![
            Ty::U8,                          // 0
            Ty::Tuple(vec![Ty::U8, Ty::U8]), // 1
            Ty::Array(TyId::new(1), 2),      // 2: [(u8, u8); 2]
            Ty::Array(TyId::new(0), 2),      // 3: [u8; 2]
            Ty::Struct(StructId::new(0)),    // 4
            Ty::Array(TyId::new(4), 2),      // 5: [S; 2]
            Ty::Unit,                        // 6
            Ty::Array(TyId::new(2), 3),      // 7: [[(u8, u8); 2]; 3]
            Ty::Array(TyId::new(9), 2),      // 8: a forward reference
        ];
        let v = tuple_spelled_table_free_entries(&r);
        assert_eq!(v, vec![true, true, true, false, false, false, true, true, false]);
        let tf = |t: Ty| table_free_as_tuple_spelled(&r, &t, &v);
        assert!(tf(Ty::Array(TyId::new(1), 2)), "[(u8, u8); 2]");
        assert!(tf(Ty::Array(TyId::new(6), 3)), "[(); 3]");
        assert!(tf(Ty::Array(TyId::new(2), 3)), "[[(u8, u8); 2]; 3]");
        assert!(tf(Ty::Tuple(vec![Ty::Array(TyId::new(1), 2), Ty::U64])), "inside a tuple");
        assert!(!tf(Ty::Array(TyId::new(0), 2)), "[u8; 2] was already Ty::Array");
        assert!(!tf(Ty::Array(TyId::new(4), 2)), "[S; 2] was already Ty::Array");
        assert!(!tf(Ty::Array(TyId::new(1), 0)), "a zero-length array was already Ty::Array");
        assert!(!tf(Ty::Array(TyId::new(8), 2)), "a forward reference");

        // The same `fn([(u8, u8); 2]) -> u8` numbered in two bodies' tables.
        let mut ra = minimal_record();
        ra.types = vec![Ty::Tuple(vec![Ty::U8, Ty::U8])];
        let mut rb = minimal_record();
        rb.types =
            vec![Ty::Bool, Ty::Tuple(vec![Ty::U8, Ty::U8]), Ty::Tuple(vec![Ty::U8, Ty::U16])];
        let sig = |tid: u32, n: u64| FuncTy {
            params: vec![Ty::Array(TyId::new(tid), n)],
            returns: vec![Ty::U8],
            is_vararg: false,
            abi: None,
        };
        assert!(func_ty_eq_across(&sig(0, 2), &ra, &sig(1, 2), &rb), "same type, other ids");
        assert!(!func_ty_eq_across(&sig(0, 2), &ra, &sig(1, 3), &rb), "other length");
        assert!(!func_ty_eq_across(&sig(0, 2), &ra, &sig(2, 2), &rb), "other element");
        assert!(!func_ty_eq_across(&sig(0, 2), &ra, &sig(7, 2), &rb), "unresolvable id");
    }

    /// Trust (2026-09-23): the promoted-global array arm splices per element EXACTLY what the
    /// old `Ty::Tuple([T; N])` spelling spliced through the tuple arm — a tuple element and a
    /// nested-array element — and nothing more: a struct element, which wave-NSA already
    /// spelled `(Ty::Array, Constant::Array)` and this arm refused, stays refused, although a
    /// struct global on its own is admitted.
    #[test]
    fn test_global_const_ok_array_elements_keep_tuple_spelling_parity() {
        let mut r = minimal_record();
        r.types = vec![
            Ty::Tuple(vec![Ty::U8, Ty::U16]),
            Ty::U8,
            Ty::Array(TyId::new(1), 2),
            Ty::Struct(StructId::new(0)),
        ];
        r.structs = vec![one_field_struct(0, Ty::U8)];
        let pair = |a, b| Constant::Aggregate(vec![Constant::Int(a), Constant::Int(b)]);
        let row = |a, b| Constant::Array(vec![Constant::Int(a), Constant::Int(b)]);
        assert!(global_const_ok(
            &r,
            &Ty::Array(TyId::new(0), 2),
            &Constant::Array(vec![pair(1, 2), pair(3, 4)])
        ));
        assert!(global_const_ok(
            &r,
            &Ty::Array(TyId::new(2), 2),
            &Constant::Array(vec![row(1, 2), row(3, 4)])
        ));
        let one = |a| Constant::Aggregate(vec![Constant::Int(a)]);
        assert!(global_const_ok(&r, &Ty::Struct(StructId::new(0)), &one(1)));
        assert!(!global_const_ok(
            &r,
            &Ty::Array(TyId::new(3), 2),
            &Constant::Array(vec![one(1), one(2)])
        ));
    }

    /// Ratification review 2026-09-28 (the RED this restores): a LENGTH-ZERO array global keeps
    /// the pin's rule — admitted only for the scalar element families — because the old spelling
    /// never tuple-spelled `[T; 0]`. At `2b05b645a1` a vacuous `all()` over no elements admitted
    /// `[(u8, u8); 0]`, `[[u8; 2]; 0]` and `[&str; 0]`, which the pin refused. A scalar element at
    /// length zero was admitted by both and still is; the same tuple element at length two still
    /// is too (the tuple-spelling parity).
    #[test]
    fn test_global_const_ok_zero_length_array_keeps_the_pins_scalar_rule() {
        let mut r = minimal_record();
        r.types = vec![
            Ty::U8,                                          // 0
            Ty::Tuple(vec![Ty::U8, Ty::U8]),                 // 1
            Ty::Array(TyId::new(0), 2),                      // 2: [u8; 2]
            Ty::FatPtr(trust_ir::FatPtrKind::Str),           // 3: &str
        ];
        let empty = Constant::Array(Vec::new());
        assert!(global_const_ok(&r, &Ty::Array(TyId::new(0), 0), &empty), "[u8; 0]");
        assert!(!global_const_ok(&r, &Ty::Array(TyId::new(1), 0), &empty), "[(u8, u8); 0]");
        assert!(!global_const_ok(&r, &Ty::Array(TyId::new(2), 0), &empty), "[[u8; 2]; 0]");
        assert!(!global_const_ok(&r, &Ty::Array(TyId::new(3), 0), &empty), "[&str; 0]");
        let pair = Constant::Aggregate(vec![Constant::Int(1), Constant::Int(2)]);
        assert!(!global_const_ok(
            &r,
            &Ty::Array(TyId::new(1), 0),
            &Constant::Splat { elem: Box::new(pair.clone()), len: 0 }
        ), "a zero-length Splat is refused exactly like the empty list");
        assert!(global_const_ok(
            &r,
            &Ty::Array(TyId::new(1), 2),
            &Constant::Array(vec![pair.clone(), pair])
        ), "control: [(u8, u8); 2] keeps its tuple-spelling parity");
    }

    /// Trust (vtable slice 15): the global Array arm, widened from Int-elements-only to the
    /// variant-matched scalar family — a promoted `&[1.5f32, 2.5]` global arrives spelled
    /// `(Ty::Array, Constant::Array)` now and must stay admissible; a variant-mismatched
    /// element (Float under an int element, Int under a float one) stays refused.
    #[test]
    fn test_global_const_ok_array_scalar_family() {
        let mut r = minimal_record();
        r.types = vec![Ty::U8, Ty::F32, Ty::Bool];
        let ints = Constant::Array(vec![Constant::Int(1), Constant::Int(2)]);
        let floats = Constant::Array(vec![Constant::Float(1.5), Constant::Float(2.5)]);
        let bools = Constant::Array(vec![Constant::Bool(true), Constant::Bool(false)]);
        assert!(global_const_ok(&r, &Ty::Array(TyId::new(0), 2), &ints));
        assert!(global_const_ok(&r, &Ty::Array(TyId::new(1), 2), &floats));
        assert!(global_const_ok(&r, &Ty::Array(TyId::new(2), 2), &bools));
        assert!(!global_const_ok(&r, &Ty::Array(TyId::new(0), 2), &floats), "variant mismatch");
        assert!(!global_const_ok(&r, &Ty::Array(TyId::new(1), 2), &ints), "variant mismatch");
        assert!(!global_const_ok(&r, &Ty::Array(TyId::new(0), 3), &ints), "length mismatch");
    }

    /// Trust (2026-09-28, trust-ir v50): the `Constant::Splat` arm of `global_const_ok` admits a
    /// uniform array EXACTLY when the list arm admits the same array spelled element by element:
    /// the same variant-matched scalar family, the same tuple / nested-array recursion, the same
    /// struct-element refusal, and the declared length. It reads the element once, so the
    /// answer is the same at any length (`u64::MAX` included) and costs nothing for it.
    #[test]
    fn test_global_const_ok_splat_admits_exactly_what_the_list_admits() {
        let mut r = minimal_record();
        r.types = vec![
            Ty::U8,
            Ty::F32,
            Ty::Bool,
            Ty::Tuple(vec![Ty::U8, Ty::U16]),
            Ty::Struct(StructId::new(0)),
        ];
        r.structs = vec![one_field_struct(0, Ty::U8)];
        let pair = Constant::Aggregate(vec![Constant::Int(1), Constant::Int(2)]);
        let one = Constant::Aggregate(vec![Constant::Int(1)]);
        let cases: [(u32, Constant, bool); 7] = [
            (0, Constant::Int(7), true),
            (1, Constant::Float(1.5), true),
            (2, Constant::Bool(true), true),
            (3, pair.clone(), true),
            (0, Constant::Float(1.5), false),
            (1, Constant::Int(7), false),
            (4, one.clone(), false),
        ];
        for (tid, elem, admitted) in cases {
            let list = Constant::Array(vec![elem.clone(), elem.clone()]);
            assert_eq!(
                global_const_ok(&r, &Ty::Array(TyId::new(tid), 2), &list),
                admitted,
                "list {elem:?}"
            );
            for len in [2, 1 << 20, u64::MAX] {
                let splat = Constant::Splat { elem: Box::new(elem.clone()), len };
                assert_eq!(
                    global_const_ok(&r, &Ty::Array(TyId::new(tid), len), &splat),
                    admitted,
                    "splat {elem:?} x {len}"
                );
                assert!(
                    !global_const_ok(&r, &Ty::Array(TyId::new(tid), len - 1), &splat),
                    "a length mismatch refuses: {elem:?} x {len}"
                );
            }
        }
        // A struct element is admitted on its own and still refused as an array element.
        assert!(global_const_ok(&r, &Ty::Struct(StructId::new(0)), &one));
    }

    /// Trust (2026-09-28, trust-ir v50): a `Constant::Splat` is FuncId-free exactly when its one
    /// element is — so a splat of a function identity is refused by the splice as the list of
    /// it would be, and a data splat is admitted, at any length.
    #[test]
    fn test_constant_funcid_free_splat_follows_its_element() {
        for len in [2, u64::MAX] {
            let data = Constant::Splat { elem: Box::new(Constant::Int(0)), len };
            assert!(constant_funcid_free(&data));
            let callable = Constant::Splat { elem: Box::new(Constant::FnDef(FuncId::new(0))), len };
            assert!(!constant_funcid_free(&callable));
            let nested = Constant::Splat { elem: Box::new(data.clone()), len };
            assert!(constant_funcid_free(&nested));
        }
        assert_eq!(
            constant_funcid_free(&Constant::Array(vec![Constant::FnDef(FuncId::new(0)); 2])),
            constant_funcid_free(&Constant::Splat {
                elem: Box::new(Constant::FnDef(FuncId::new(0))),
                len: 2
            }),
            "list and splat spellings of one array agree"
        );
    }

    /// Trust (vtable slice 15): `remap_ty` over the now-Option types map — a filled entry
    /// remaps, a HOLE fails closed (the two-phase pass-1 contract: struct-def fields may only
    /// reference pre-interned table-free entries).
    #[test]
    fn test_remap_ty_option_ty_map_holes_fail_closed() {
        let ty_map: Vec<Option<TyId>> = vec![Some(TyId::new(7)), None];
        assert_eq!(
            remap_ty(&Ty::Array(TyId::new(0), 3), &[], &[], &ty_map, &[]),
            Some(Ty::Array(TyId::new(7), 3))
        );
        assert_eq!(remap_ty(&Ty::Array(TyId::new(1), 3), &[], &[], &ty_map, &[]), None);
        assert_eq!(remap_ty(&Ty::Array(TyId::new(2), 3), &[], &[], &ty_map, &[]), None);
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
            generated_ungated: false,
            coroutine_frame_ptr: false,
            abi: crate::calling_convention::FunctionAbi::RUST,
            def_index: 0,
            definition: crate::lineage::DefinitionIdentity::test_only(0xC0DE, 0),
            kind: BodyKind::Fn,
            symbolic: false,
            union_lane: false,
            storage_value_traffic: false,
            layout_withheld_structs: Vec::new(),
            enum_param_lane: false,
            def_path: "probe".to_string(),
            place_path_carrier: false,
            zst_closure_arg: false,
            fnptr_adapter: false,
            adapters: Vec::new(),
            function: None,
            func_ty: None,
            files: Vec::new(),
            closure_types: Vec::new(),
            closure_layouts: Vec::new(),
            structs: Vec::new(),
            enums: Vec::new(),
            types: Vec::new(),
            tuple_layouts: Vec::new(),
            target_info: None,
            globals: Vec::new(),
            global_origins: Vec::new(),
            unsupported: Vec::new(),
            unsupported_details: Vec::new(),
            enum_declines: Vec::new(),
            collect_primary: Vec::new(),
            collect_cascade: Vec::new(),
            instr_count: 0,
            callees: Vec::new(),
            func_types: Vec::new(),
            pending_consts: Vec::new(),
            contains_call: false,
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
            link_symbol: None,
            callee_links: Vec::new(),
        }
    }
}

/// Trust (B8 step 1): the declaration-blocker taxonomy — the split of what used to be one
/// anonymous `clean-skip-extern-callee` string.
///
/// Two of these tests guard the SPLIT (that the classes are recoverable and rendered
/// deterministically). The third guards something more important and easier to lose: that
/// routing the five keys through [`decl_key`] did not change a single byte of any key. Keys are
/// declaration IDENTITY — [`decl_id`] interns on the whole string — so a one-character drift
/// re-partitions a module's declarations, which changes real IR, which moves clean/Agreed. This
/// slice is instrumentation and is required to move neither.
#[cfg(test)]
mod decl_kind_tests {
    use super::*;

    #[test]
    fn decl_kind_round_trips() {
        for kind in DeclKind::ALL {
            // A `def_path`-shaped remainder, which itself contains the split character.
            let key = decl_key(kind, "core::option::Option::<T>::unwrap|ret:U64");
            assert_eq!(
                DeclKind::from_key(&key),
                Some(kind),
                "{kind:?} did not round-trip through {key:?}"
            );
        }
    }

    #[test]
    fn decl_kind_prefixes_are_distinct_and_colon_free() {
        // `from_key` splits on the first `:`, so a prefix containing one would alias.
        for kind in DeclKind::ALL {
            assert!(!kind.prefix().contains(':'), "{kind:?} prefix contains the split character");
        }
        let mut seen: Vec<&str> = DeclKind::ALL.iter().map(|k| k.prefix()).collect();
        seen.sort_unstable();
        let n = seen.len();
        seen.dedup();
        assert_eq!(seen.len(), n, "two DeclKind variants share a prefix");
    }

    /// A key this taxonomy does not know is `None` — reported as `unclassified`, never rounded
    /// into a neighbouring class.
    #[test]
    fn decl_kind_rejects_a_stranger() {
        assert_eq!(DeclKind::from_key("some-new-class:foo"), None);
        assert_eq!(DeclKind::from_key("no-colon-at-all"), None);
        // A prefix that merely SHARES a leading substring with a real one must not match.
        assert_eq!(DeclKind::from_key("externally:foo"), None);
        assert_eq!(DeclKind::from_key("local:foo"), None);
    }

    /// THE REGRESSION THAT MATTERS. Pinned against the literal `format!` spellings
    /// `resolve_callee` carried before this slice, transcribed from the pre-change source.
    #[test]
    fn decl_key_is_byte_identical_to_legacy_spelling() {
        let def_path = "alloc::vec::Vec::<T>::push";
        let ret_key = "|ret:Unit";
        let callee_index: u32 = 12363;
        let ret_suffix = "|ret:U64";

        assert_eq!(
            decl_key(DeclKind::Havoc, format!("{def_path}{ret_key}")),
            format!("havoc:{def_path}{ret_key}")
        );
        assert_eq!(
            decl_key(DeclKind::LocalUnlowered, format!("{def_path}{ret_key}")),
            format!("local-unlowered:{def_path}{ret_key}")
        );
        assert_eq!(
            decl_key(DeclKind::Extern, format!("{def_path}{ret_key}")),
            format!("extern:{def_path}{ret_key}")
        );
        assert_eq!(decl_key(DeclKind::Unknown, callee_index), format!("unknown:{callee_index}"));
        assert_eq!(
            decl_key(DeclKind::Ambiguous, format!("{callee_index}{ret_suffix}")),
            format!("ambiguous:{callee_index}{ret_suffix}")
        );
    }

    /// The call site may append `|nres:{n}` to a key AFTER `resolve_callee` returns it, and
    /// Trust (wave-RETSPLIT) `decl_id` may append `|ret:{spelling}` to a CONCRETE key at intern
    /// time. The class must survive both, or every split declaration would land in
    /// `unclassified`.
    #[test]
    fn decl_kind_survives_the_nres_suffix() {
        let key = format!("{}|nres:0", decl_key(DeclKind::Extern, "core::mem::drop|ret:U64"));
        assert_eq!(DeclKind::from_key(&key), Some(DeclKind::Extern));
        let split = format!(
            "{}|ret:{:?}",
            decl_key(DeclKind::LocalUnlowered, "probe::make|concrete-v1:key"),
            Ty::Struct(StructId::new(14)),
        );
        assert_eq!(DeclKind::from_key(&split), Some(DeclKind::LocalUnlowered));
        assert_eq!(
            split.split('|').next(),
            Some("local-unlowered:probe::make"),
            "the Clean-origin join reads the display path up to the FIRST `|`"
        );
    }

    fn assembled_with(decls: &[(u32, &str)]) -> Assembled {
        Assembled {
            module: Module::new("test"),
            errors: Vec::new(),
            coverage_rows: Vec::new(),
            lowered: 0,
            spliced: 0,
            declarations: decls.len(),
            assigned: Vec::new(),
            decl_keys: decls
                .iter()
                .map(|(id, key)| crate::clean_origin_join::DeclarationLinkIdentity {
                    func_id: FuncId::new(*id),
                    key: (*key).to_string(),
                    local_def_index: key.starts_with("local-unlowered:").then_some(*id),
                })
                .collect(),
            // Trust (v41 `RustAbiVararg`): this blocker-census fixture asserts nothing
            // about declaration signing, so an empty list is the honest value — but it
            // has to be SPELLED. A `#[cfg(test)]` initializer that falls behind its
            // struct is precisely the cfg-test caller skew
            // `scripts/check_cfg_test_caller_skew.py` exists to catch, and it is
            // invisible to any rung that does not compile the test targets (measured
            // here: E0063 in the lib TEST target only, with the lib itself green).
            unsignable_declarations: Vec::new(),
            codegen_declarations: Vec::new(),
        }
    }

    #[test]
    fn blocker_summary_counts_and_orders_deterministically() {
        let a = assembled_with(&[
            (0, "local-unlowered:krate::helper"),
            (1, "extern:core::fmt::write"),
            (2, "extern:core::panicking::panic"),
            (3, "havoc:krate::generic::<T>"),
        ]);
        // Presented OUT of taxonomy order on purpose: the output must not depend on walk order.
        let ids = [FuncId::new(3), FuncId::new(0), FuncId::new(2), FuncId::new(1)];
        assert_eq!(blocker_summary(&a, &ids), "extern=2, havoc=1, local-unlowered=1");
    }

    #[test]
    fn blocker_summary_reports_a_single_class_alone() {
        let a = assembled_with(&[(0, "extern:core::fmt::write")]);
        assert_eq!(blocker_summary(&a, &[FuncId::new(0)]), "extern=1");
    }

    /// An unparsable key, and a `FuncId` with no `decl_keys` entry at all (the closure member the
    /// step-2 filter admits through `unwrap_or(true)`), both land in `unclassified` — and do not
    /// disturb the classes that DID parse.
    #[test]
    fn blocker_summary_never_folds_a_stranger_into_a_neighbour() {
        let a = assembled_with(&[(0, "extern:core::fmt::write"), (1, "brand-new-class:x")]);
        assert_eq!(
            blocker_summary(&a, &[FuncId::new(0), FuncId::new(1), FuncId::new(99)]),
            "extern=1, unclassified=2"
        );
    }
}

/// Trust (gap G9, 2026-09-01): the producer's whole-module `validate_module` walk must run
/// BELOW the Clean-origin append and link, and below direct-obligation birth.
///
/// WHY A SOURCE-ORDER TEST AND NOT A BEHAVIOURAL ONE. The regression this pins COMPILES
/// CLEANLY and changes no type: hoisting the walk back above `append_clean_origin` is a legal
/// edit that silently restores the exact defect it closed — a validator that has never once
/// seen a cross-producer call edge, because at that point in `finalize` no Clean-origin
/// definition has been appended and no declaration edge has been re-pointed onto one. Nothing
/// else in this file would notice: the walk touches no `errors`, changes no verdict, and its
/// output is a `tracing` event. A behavioural check needs a `TyCtxt`, a Clean-origin record
/// set and a stage-2 build; this one needs the file.
///
/// The two orderings are NOT symmetric, which is why the assertion has a direction. The seam
/// differential must run BEFORE the append (its population is the THIR records and must not
/// see appended rows), and the validator must run AFTER it — so "somewhere in the middle" is
/// not a third option.
///
/// The needles are BUILT rather than written out, because this module is itself inside
/// `include_str!("crate_module.rs")` and a literal needle would match itself.
///
/// MERGED 2026-09-14: the log-only `validate_module` tripwire these tests were written for was
/// superseded upstream by the UNCONDITIONAL `final_module_validation_errors` gate at the same
/// seam (an invalid module now fails finalization). The anchors pin that call instead, and
/// both orderings G9 established still have to hold for it.
#[cfg(test)]
mod validation_tripwire_order_tests {
    const SRC: &str = include_str!("crate_module.rs");

    /// Byte offset of an anchor that must occur EXACTLY once. A second occurrence is a
    /// failure, not a tie-break: the test would otherwise quietly start measuring a different
    /// site than the one it was written for.
    fn sole_offset(needle: &str) -> usize {
        let mut hits = SRC.match_indices(needle);
        let (at, _) = hits.next().unwrap_or_else(|| panic!("anchor vanished: {needle}"));
        assert!(hits.next().is_none(), "anchor is no longer unique: {needle}");
        at
    }

    #[test]
    fn the_module_validator_runs_below_the_clean_origin_link() {
        // The FIRST occurrence is the production call — the unconditional final validation
        // gate that superseded the log-only tripwire at this seam. Later occurrences are other
        // tests' literal needles, which sit below `finalize_and_dump` in this file.
        let validate = SRC
            .find(concat!("errors.extend(final_module_", "validation_errors(&assembled.module));"))
            .expect("the final module validation gate vanished");
        let append = sole_offset(concat!(
            "crate::clean_origin_join::", "prepare_clean_origin_with_rust_callees("
        ));
        let link = sole_offset(concat!("crate::clean_origin_join::", "link_prepared_clean_origin("));
        assert!(
            append < link,
            "the clean-origin append must precede the link (append at {append}, link at {link})"
        );
        assert!(
            link < validate,
            "the `validate_module` tripwire moved back ABOVE the clean-origin link (link at \
             {link}, validate at {validate}). It would then run on a module containing no \
             cross-producer call edge, so `CallArgTypeMismatch`'s caller_producer/\
             callee_producer would again never fire — the defect G9 closed."
        );
    }

    /// Below obligation birth too, so the v34 `ObligationSite` backrefs — which
    /// `validate_module` hard-rejects when dangling or scope-contradicting — are inside the
    /// window the walk inspects.
    #[test]
    fn the_module_validator_runs_below_direct_obligation_birth() {
        // The FIRST occurrence is the production call — the unconditional final validation
        // gate that superseded the log-only tripwire at this seam. Later occurrences are other
        // tests' literal needles, which sit below `finalize_and_dump` in this file.
        let validate = SRC
            .find(concat!("errors.extend(final_module_", "validation_errors(&assembled.module));"))
            .expect("the final module validation gate vanished");
        let install = sole_offset(concat!("install_direct_", "obligations("));
        assert!(
            install < validate,
            "direct-obligation birth moved below the tripwire (install at {install}, validate \
             at {validate}); the walk would then inspect a module with no obligation rows"
        );
    }
}

/// Trust (gap G2): the codegen license and the symbol map, pinned by test.
///
/// Both failure modes this guards COMPILE CLEANLY. A license that licensed a
/// Clean-origin body, and a symbol map that resolved an ambiguous name to
/// whichever function came first, are perfectly well-typed programs — the only
/// thing that tells them from the correct ones is a test that builds a module
/// with the hazard in it and asserts the refusal.
///
/// These are pure functions over `trust_ir` types with no `rustc` dependency,
/// which is deliberate: `trust-thir-lower` needs `rustc_private` and cannot be
/// built from the plain `crates/` workspace, so keeping the license decidable
/// from `trust_ir` alone is what makes it measurable outside the compiler build
/// at all. Measured 2026-09-01 by compiling these bodies VERBATIM against
/// `first-party/trust-ir` at the recorded pin (fecd740): 9/9 pass, and
/// `one_clean_origin_body_refuses_the_whole_module` FAILED when leg 4 was
/// deleted. Plan step 3.4 (owner ruling D37) made leg 4 per function for
/// Clean-origin bodies; the tests that pinned the whole-module withholding for
/// a Clean body now pin the per-function stamp, and an appended body of any
/// other producer still withdraws the whole module
/// (`an_appended_body_of_any_producer_refuses_the_whole_module`). The ledger
/// half is `crate_module/carrier_ledger_tests.rs`.
#[cfg(test)]
mod codegen_license_tests {
    use super::*;
    use trust_ir::{Block, Producer};

    fn pending_source_fixture() -> (
        crate::clean_origin_join::PendingRustCallSource,
        std::sync::Weak<trust_certify::clean_island::KernelEnvironment>,
    ) {
        use trust_certify::clean_island::{CleanIslandSession, RustCallee};
        let mut session = CleanIslandSession::new();
        session.declare_rust_callees(&[RustCallee {
            clean_name: "f".into(), params: vec![trust_types::Ty::u64()],
            result: trust_types::Ty::u64(),
        }]).unwrap();
        assert!(!session.check("def answer (x : UInt64) : UInt64 := f x").is_rejected());
        let environment = std::sync::Arc::new(session.environment().unwrap().clone());
        let weak = std::sync::Arc::downgrade(&environment);
        let plan = trust_clean_origin::plan_clean_origin_body_with_rust_callees(
            &environment, "answer", &[trust_clean_origin::RustCalleeRef {
                clean_name: "f".into(), def_path: "rust::f".into(),
                params: vec![trust_types::Ty::u64()], result: trust_types::Ty::u64(),
            }],
        ).unwrap();
        (crate::clean_origin_join::PendingRustCallSource {
            def_index: 42, func_id: FuncId::new(1), link_symbol: "clean".into(),
            source: trust_clean_ir_gate::rust_calls::RetainedRustCallSource::retain(
                environment, std::sync::Arc::new(plan),
            ),
            bindings: vec![trust_clean_ir_gate::rust_calls::RustCallBinding {
                plan_index: 0, function: FuncId::new(0),
            }],
        }, weak)
    }

    #[test]
    fn retained_call_context_is_published_beside_its_module_without_a_license() {
        let module = module_of(vec![defined(0, "rust", Producer::TRust),
            defined(1, "clean", Producer::Clean)]);
        let decision = stamp_then_publish("retained", module, &assigned(1), &[]);
        let (pending, weak) = pending_source_fixture();
        let published = retain_pending_rust_call_sources(decision, vec![pending]).unwrap_or_else(|e| panic!("{e}"));
        assert_eq!(published.pending_rust_call_source(42).unwrap().func_id, FuncId::new(1));
        assert!(published.pending_rust_call_source(43).is_none());
        assert_eq!(published.codegen_inventory(), &[FuncId::new(0)]);
        assert!(!published.is_codegen_licensed(FuncId::new(1)));
        assert!(weak.upgrade().is_some());
        drop(published);
        assert!(weak.upgrade().is_none(), "snapshot lifetime follows its publication");
    }

    #[test]
    fn failed_or_ambiguous_publication_drops_every_retained_call_context() {
        for mutation in 0..8 {
            let mut module = module_of(vec![defined(0, "rust", Producer::TRust),
                defined(1, "clean", Producer::Clean), defined(2, "other", Producer::Clean)]);
            if mutation == 6 { module.functions[1].blocks.clear(); }
            if mutation == 7 { module.functions[1].producer = Some(Producer::TRust); }
            let errors = if mutation == 0 { vec!["forced semantic refusal".into()] } else { vec![] };
            let decision = stamp_then_publish("retained", module, &assigned(1), &errors);
            if mutation != 0 { assert!(decision.is_ok(), "fixture must reach retention validation: {mutation}"); }
            let (mut pending, weak) = pending_source_fixture();
            if mutation == 1 { pending.link_symbol = "wrong".into(); }
            if mutation == 5 { pending.func_id = FuncId::new(99); }
            let mut rows = vec![pending];
            if (2..=4).contains(&mutation) {
                let mut duplicate = rows[0].clone();
                if mutation == 3 { duplicate.def_index = 43; }
                if mutation == 4 { duplicate.func_id = FuncId::new(2); duplicate.link_symbol = "other".into(); }
                rows.push(duplicate);
            }
            assert!(retain_pending_rust_call_sources(decision, rows).is_err(), "mutation {mutation}");
            assert!(weak.upgrade().is_none(), "refusal must not retain a partial source snapshot");
        }
    }

    /// A body-bearing function: one empty block is a body
    /// (`is_declaration` is `blocks.is_empty()`).
    fn defined(id: u32, name: &str, producer: Producer) -> Function {
        let mut f = Function::new(FuncId::new(id), name, FuncTyId::new(0), BlockId::new(0))
            .with_producer(producer);
        f.blocks.push(Block::new(BlockId::new(0)));
        f
    }

    fn declaration(id: u32, name: &str) -> Function {
        Function::new(FuncId::new(id), name, FuncTyId::new(0), BlockId::new(0))
            .with_producer(Producer::TRust)
    }

    fn module_of(functions: Vec<Function>) -> Module {
        let mut m = Module::new("k");
        m.functions = functions;
        m
    }

    fn assigned(n: u32) -> Vec<(u32, FuncId)> {
        (0..n).map(|i| (i, FuncId::new(i))).collect()
    }

    /// Trust (WS5.2): a bodyless declaration now carries its callee's REAL producer (`Clean`,
    /// `TRust`, or `None` = unrecorded) where every declaration used to be stamped `TRust`.
    /// Nothing DECIDES on it: the license reads a producer only for the direct set (leg 3,
    /// definitions), and trust-ir's validator reads one only to attribute a call mismatch. So
    /// the license verdict and the validator's error classes are identical under all three.
    #[test]
    fn a_declarations_producer_decides_neither_the_license_nor_validation() {
        let producers = [Some(Producer::TRust), Some(Producer::Clean), None];
        let verdicts: Vec<(String, Vec<String>)> = producers
            .into_iter()
            .map(|producer| {
                let mut callee = declaration(1, "_RNvCs0_5probe6callee");
                callee.producer = producer;
                let mut m =
                    module_of(vec![defined(0, "_RNvCs0_5probe6caller", Producer::TRust), callee]);
                let unit = FuncTy {
                    params: Vec::new(),
                    returns: Vec::new(),
                    is_vararg: false,
                    abi: None,
                };
                m.func_types.push(unit);
                let license = compute_codegen_license(&m, &assigned(1));
                let classes = trust_ir_build::validate_module(&m)
                    .iter()
                    .map(validation_error_class)
                    .collect();
                (format!("{license:?}"), classes)
            })
            .collect();
        assert!(verdicts[0].0.starts_with("Ok("), "{:?}", verdicts[0]);
        assert_eq!(verdicts[0], verdicts[1]);
        assert_eq!(verdicts[0], verdicts[2]);
    }

    /// The REAL composition `finalize_and_dump` performs: stamp the v41
    /// license into the module, then publish carrying the stamp's verdict.
    /// Tests go through this rather than calling `decide_publication` with a
    /// hand-made refusal, because the property under test is that the
    /// inventory a consumer receives is READ BACK off the stamps.
    fn stamp_then_publish(
        name: &str,
        mut module: Module,
        assigned: &[(u32, FuncId)],
        errors: &[String],
    ) -> Result<PublishedCrateModule, String> {
        let refusal = stamp_codegen_license(&mut module, assigned, &BTreeSet::new());
        decide_publication(name, module, assigned, errors, refusal)
    }

    /// No session-ledger entry: the plain stamp (plan step 3.4's per-function leg 4 with an
    /// empty ledger).
    fn stamp(module: &mut Module, assigned: &[(u32, FuncId)]) -> Option<String> {
        stamp_codegen_license(module, assigned, &BTreeSet::new())
    }

    #[test]
    fn direct_bodies_are_licensed_when_no_ungated_body_is_present() {
        let m = module_of(vec![
            defined(0, "a", Producer::TRust),
            defined(1, "b", Producer::TRust),
            declaration(2, "ext"),
        ]);
        let licensed = compute_codegen_license(&m, &assigned(2)).expect("license granted");
        assert_eq!(licensed, vec![FuncId::new(0), FuncId::new(1)]);
    }

    #[test]
    fn a_crate_with_no_spliceable_body_has_an_empty_license_and_no_refusal() {
        let m = module_of(vec![declaration(0, "ext")]);
        assert_eq!(compute_codegen_license(&m, &assigned(0)), Ok(Vec::new()));
    }

    /// THE HARD CONSTRAINT, per function since plan step 3.4 (D37). Until then
    /// one appended Clean-origin definition disqualified the WHOLE module,
    /// direct bodies included. Now the direct license stands and the Clean body
    /// is licensed only through an authenticated ledger entry
    /// (`crate_module/carrier_ledger_tests.rs`); with none it is `Ungated`.
    #[test]
    fn one_clean_origin_body_no_longer_refuses_the_direct_license() {
        let m = module_of(vec![
            defined(0, "a", Producer::TRust),
            declaration(1, "clean::f"),
            defined(2, "clean::g", Producer::Clean),
        ]);
        assert_eq!(compute_codegen_license(&m, &assigned(1)), Ok(vec![FuncId::new(0)]));
        assert!(clean_carrier_licensed(&m, &assigned(1), &BTreeSet::new()).is_empty());
    }

    /// The gate does NOT key on `Producer::Clean`: an appended body from any
    /// future lane is equally unlicensed, because the license is a positive
    /// record of the direct set, not a deny-list of known-bad producers.
    #[test]
    fn an_appended_body_of_any_producer_refuses_the_whole_module() {
        let m = module_of(vec![
            defined(0, "a", Producer::TRust),
            defined(1, "later-lane", Producer::TRust),
        ]);
        let refusal = compute_codegen_license(&m, &assigned(1)).expect_err("must refuse");
        assert!(refusal.contains("outside the direct-lane set"), "{refusal}");
        assert!(refusal.contains("other than Clean"), "{refusal}");
    }

    /// Declarations are unlicensed WITHOUT being disqualifying: an opaque
    /// external symbol has nothing to emit, and a call to one is not a leak.
    #[test]
    fn declarations_are_unlicensed_but_not_disqualifying() {
        let m = module_of(vec![
            defined(0, "a", Producer::TRust),
            declaration(1, "ext1"),
            declaration(2, "ext2"),
        ]);
        assert_eq!(compute_codegen_license(&m, &assigned(1)), Ok(vec![FuncId::new(0)]));
    }

    #[test]
    fn a_renumbered_module_licenses_nothing() {
        let mut m =
            module_of(vec![defined(0, "a", Producer::TRust), defined(1, "b", Producer::TRust)]);
        m.functions[1].id = FuncId::new(7);
        let refusal = compute_codegen_license(&m, &assigned(2)).expect_err("must refuse");
        assert!(refusal.contains("dense-FuncId invariant broken"), "{refusal}");
    }

    /// Leg 3: position and provenance are two INDEPENDENT signals, and a
    /// disagreement is a refusal rather than a tie-break.
    #[test]
    fn a_direct_slot_holding_a_non_trust_producer_licenses_nothing() {
        let m = module_of(vec![defined(0, "a", Producer::TRust), defined(1, "b", Producer::Clean)]);
        let refusal = compute_codegen_license(&m, &assigned(2)).expect_err("must refuse");
        assert!(refusal.contains("position and provenance disagree"), "{refusal}");
    }

    #[test]
    fn a_bodyless_function_in_the_direct_set_licenses_nothing() {
        let m = module_of(vec![defined(0, "a", Producer::TRust), declaration(1, "b")]);
        let refusal = compute_codegen_license(&m, &assigned(2)).expect_err("must refuse");
        assert!(refusal.contains("position and body disagree"), "{refusal}");
    }

    fn err_of(decision: &Result<PublishedCrateModule, String>) -> &str {
        match decision {
            Ok(_) => panic!("expected a refusal, got a published module"),
            Err(reason) => reason,
        }
    }

    fn ok_of(decision: &Result<PublishedCrateModule, String>) -> &PublishedCrateModule {
        match decision {
            Ok(published) => published,
            Err(reason) => panic!("expected a published module, got refusal: {reason}"),
        }
    }

    #[test]
    fn publication_carries_the_module_the_license_and_the_symbol_map() {
        let m = module_of(vec![defined(0, "a", Producer::TRust), declaration(1, "ext")]);
        let decision = stamp_then_publish("k", m, &assigned(1), &[]);
        let published = ok_of(&decision);
        assert_eq!(published.crate_name(), "k");
        assert_eq!(published.module().functions.len(), 2);
        assert_eq!(published.codegen_inventory(), &[FuncId::new(0)]);
        assert!(published.is_codegen_licensed(FuncId::new(0)));
        assert!(!published.is_codegen_licensed(FuncId::new(1)));
        assert_eq!(published.resolve_symbol("ext"), Some(FuncId::new(1)));
        assert_eq!(published.resolve_symbol("nope"), None);
        assert_eq!(published.codegen_license_refusal(), None);
    }

    #[test]
    fn publication_preserves_exact_definitions_beside_ambiguous_display_paths() {
        let mut functions = vec![
            defined(0, "_RNvCs1_5probe4same", Producer::TRust),
            defined(1, "__trust_init_00000000000000000000000000000002", Producer::TRust),
        ];
        for function in &mut functions {
            function.display_path = Some("probe::{constant#0}::same".to_string());
        }
        let decision = stamp_then_publish(
            "k", module_of(functions), &[(9, FuncId::new(0)), (71, FuncId::new(1))], &[],
        );
        let published = ok_of(&decision);
        assert_eq!(published.direct_function_for_definition(9), Some(FuncId::new(0)));
        assert_eq!(published.direct_function_for_definition(71), Some(FuncId::new(1)));
        assert_eq!(published.direct_function_for_definition(0), None);
        assert_eq!(published.resolve_symbol("probe::{constant#0}::same"), None);
        assert_eq!(published.ambiguous_display_paths(), &["probe::{constant#0}::same"]);
        assert_eq!(published.codegen_inventory(), &[FuncId::new(0), FuncId::new(1)]);
    }

    /// Plan step 3.4 (D37): a module holding a below-`gate` Clean-origin body
    /// publishes with the DIRECT inventory intact and no refusal; the Clean
    /// body is in no inventory. (Until 3.4: an empty inventory and a refusal.)
    #[test]
    fn a_clean_origin_body_publishes_the_module_with_the_direct_inventory() {
        let m = module_of(vec![
            defined(0, "a", Producer::TRust),
            defined(1, "clean::g", Producer::Clean),
        ]);
        let decision = stamp_then_publish("k", m, &assigned(1), &[]);
        let published = ok_of(&decision);
        assert_eq!(published.module().functions.len(), 2);
        assert_eq!(published.codegen_inventory(), &[FuncId::new(0)]);
        assert!(published.is_codegen_licensed(FuncId::new(0)));
        assert!(!published.is_codegen_licensed(FuncId::new(1)));
        assert_eq!(published.codegen_license_refusal(), None);
    }

    #[test]
    fn finalization_errors_refuse_publication_outright() {
        let m = module_of(vec![defined(0, "a", Producer::TRust)]);
        let decision = stamp_then_publish("k", m, &assigned(1), &["boom".to_string()]);
        assert!(err_of(&decision).contains("recorded 1 error"), "{}", err_of(&decision));
    }

    /// The artifact writer's tripwire, re-run unconditionally: a sentinel is a
    /// placeholder for a value the finalizer failed to evaluate, and emitting
    /// code for it would emit the wrong value silently.
    #[test]
    fn a_leftover_pending_const_sentinel_refuses_publication() {
        let mut f = defined(0, "a", Producer::TRust);
        f.blocks[0].body.push(InstrNode::new(Inst::Const {
            ty: Ty::I32,
            value: Constant::PhantomData,
        }));
        let decision = stamp_then_publish("k", module_of(vec![f]), &assigned(1), &[]);
        assert!(err_of(&decision).contains("pending-const sentinel"), "{}", err_of(&decision));
    }

    #[test]
    fn asking_before_any_publication_gets_a_reason_rather_than_silence() {
        let state = PublishedCrateModuleState::default();
        assert!(state.published.is_none());
        assert_eq!(
            state.refusal.as_deref().unwrap_or(NO_PUBLISHED_CRATE_MODULE),
            NO_PUBLISHED_CRATE_MODULE
        );
    }

    #[test]
    fn a_refusal_is_recorded_so_a_consumer_learns_why_it_got_nothing() {
        let mut state = PublishedCrateModuleState::default();
        install_published_crate_module(&mut state, "k", Err("because".to_string()));
        assert!(state.published.is_none());
        assert_eq!(state.refusal.as_deref(), Some("because"));
    }

    /// A second finalization makes BOTH candidates suspect, so the first is
    /// WITHDRAWN — not kept (silently the wrong crate) and not replaced
    /// (silently the wrong crate the other way round).
    #[test]
    fn a_second_publication_withdraws_the_first() {
        let ok = |name: &str| {
            stamp_then_publish(name, module_of(vec![defined(0, "a", Producer::TRust)]), &assigned(1), &[])
        };
        let mut state = PublishedCrateModuleState::default();
        install_published_crate_module(&mut state, "k", ok("k"));
        assert!(state.published.is_some());
        install_published_crate_module(&mut state, "k2", ok("k2"));
        assert!(state.published.is_none());
        assert!(state.refusal.as_deref().unwrap().contains("already published"));
    }

    // -- the v41 STAMP ------------------------------------------------------
    //
    // Every failure these guard COMPILES CLEANLY. A stamp that licensed a
    // Clean-origin body, one that left a body claim-less (the grandfather
    // state a consumer PERMITS), and one that silently disagreed with the
    // inventory are all well-typed programs; only a test that builds the
    // module and reads the field back tells them from the correct one.

    fn gate_of(module: &Module, id: u32) -> Option<&BodyGate> {
        module.function_by_id(FuncId::new(id)).expect("function").body_gate.as_ref()
    }

    #[test]
    fn a_licensed_direct_body_is_stamped_gated_under_the_structural_authority() {
        let mut m = module_of(vec![
            defined(0, "a", Producer::TRust),
            defined(1, "b", Producer::TRust),
            declaration(2, "ext"),
        ]);
        assert_eq!(stamp(&mut m, &assigned(2)), None, "license must be granted");
        for id in [0, 1] {
            assert_eq!(
                gate_of(&m, id),
                Some(&BodyGate::Gated {
                    authority: TRUST_DIRECT_LANE_AUTHORITY.to_string(),
                    evidence: None,
                }),
                "FuncId {id} is licensed, so it must carry the producer's positive claim"
            );
        }
        // A declaration produces no code, so it needs no license and makes no
        // claim. It is NOT `Ungated`: that would tell a consumer a gate was
        // withheld from something that was never a codegen subject.
        assert_eq!(gate_of(&m, 2), None);
    }

    /// THE HAZARD THE STAMP CLOSED (before it, an appended below-tier
    /// Clean-origin definition went out with `body_gate: None`, which
    /// `trust_cg_lower::CodegenLicensePolicy` PERMITS by default), stamped per
    /// function since plan step 3.4 (D37): the Clean body is affirmatively
    /// `Ungated`, the direct body keeps its license. (Until 3.4 the direct body
    /// was `Ungated` too, and the crate-module lane refused a Rust-only body of
    /// a Clean-island crate, measured `[crate-module-unavailable]`.)
    #[test]
    fn a_clean_origin_body_is_stamped_ungated_and_the_direct_ones_keep_their_license() {
        let mut m = module_of(vec![
            defined(0, "a", Producer::TRust),
            defined(1, "clean::g", Producer::Clean),
        ]);
        assert_eq!(stamp(&mut m, &assigned(1)), None, "the direct license is granted");
        assert_eq!(
            gate_of(&m, 0),
            Some(&BodyGate::Gated { authority: TRUST_DIRECT_LANE_AUTHORITY.to_string(), evidence: None })
        );
        assert_eq!(gate_of(&m, 1), Some(&BodyGate::Ungated));
        assert_eq!(inventory_from_stamps(&m), vec![FuncId::new(0)]);
    }

    /// THE INVENTORY IS THE STAMP. Not "agrees with" — IS. An unstamped module
    /// licenses nothing, which is what makes dropping the stamp fail closed
    /// instead of falling back to a second computation.
    #[test]
    fn an_unstamped_module_licenses_nothing() {
        let m = module_of(vec![
            defined(0, "a", Producer::TRust),
            defined(1, "b", Producer::TRust),
        ]);
        assert!(m.functions.iter().all(|f| f.body_gate.is_none()), "fixture must be unstamped");
        assert!(inventory_from_stamps(&m).is_empty());
    }

    /// A FOREIGN license is not permission. Possession of someone else's gate
    /// authority never puts a body in this producer's inventory.
    #[test]
    fn a_foreign_gate_authority_is_not_in_the_inventory() {
        let mut m = module_of(vec![defined(0, "a", Producer::TRust)]);
        m.functions[0].body_gate =
            Some(BodyGate::Gated { authority: "clean-kernel-tv".to_string(), evidence: None });
        assert!(inventory_from_stamps(&m).is_empty());
    }

    /// The published inventory is read back off the stamps, so the module a
    /// consumer is handed and the work list it is handed cannot disagree.
    #[test]
    fn publication_hands_out_the_inventory_the_stamps_spell() {
        let decision = stamp_then_publish(
            "k",
            module_of(vec![
                defined(0, "a", Producer::TRust),
                defined(1, "b", Producer::TRust),
                declaration(2, "ext"),
            ]),
            &assigned(2),
            &[],
        );
        let published = ok_of(&decision);
        assert_eq!(published.codegen_inventory(), &[FuncId::new(0), FuncId::new(1)]);
        for id in published.codegen_inventory() {
            assert!(
                matches!(
                    published.module().function_by_id(*id).unwrap().body_gate.as_ref(),
                    Some(BodyGate::Gated { authority, .. })
                        if authority == TRUST_DIRECT_LANE_AUTHORITY
                ),
                "every inventory member must carry the claim the inventory was read from"
            );
        }
    }

    /// A GRANTED license is pass 1's direct prefix. Stamps that do not match
    /// that arity are an internal inconsistency, and publication refuses
    /// outright rather than hand out an inventory it cannot attribute.
    #[test]
    fn stamps_that_drift_from_the_direct_prefix_refuse_publication() {
        let mut m = module_of(vec![
            defined(0, "a", Producer::TRust),
            defined(1, "b", Producer::TRust),
        ]);
        // Stamp honestly, then tamper with ONE claim the way a later pass
        // could: the license verdict says "granted", the stamps say otherwise.
        assert_eq!(stamp(&mut m, &assigned(2)), None);
        m.functions[1].body_gate = Some(BodyGate::Ungated);
        let decision = decide_publication("k", m, &assigned(2), &[], None);
        assert!(err_of(&decision).contains("stamps license"), "{}", err_of(&decision));
    }

    /// THE PREMISE, MACHINE-CHECKED: tier `gate` is a live variant (the stamp's
    /// docs once rested on the false "it does not exist"). Since plan step 3.4
    /// leg 4 still does not read the tier: a Clean body is licensed only through
    /// an authenticated ledger entry, so a body the tier calls `gate` but with
    /// no entry is stamped exactly like a `structural` row — that identity IS
    /// the property, and the direct license stands either way.
    #[test]
    fn the_gate_tier_this_gate_refuses_below_is_a_live_variant() {
        use crate::clean_origin_join::CleanOriginTier;
        assert_eq!(CleanOriginTier::Gate.tag(), "gate");
        let mut m = module_of(vec![
            defined(0, "direct", Producer::TRust),
            defined(1, "cleanWsum", Producer::Clean),
        ]);
        assert_eq!(stamp(&mut m, &assigned(1)), None);
        assert_eq!(gate_of(&m, 1), Some(&BodyGate::Ungated), "no ledger entry, no license");
        assert_eq!(inventory_from_stamps(&m), vec![FuncId::new(0)]);
    }

    /// A REFUSED LICENSE LICENSES NOTHING — checked STRUCTURALLY, not inferred
    /// from the call order. The arity re-check used to run only on the granted
    /// path (`if codegen_license_refusal.is_none()`), so the one direction
    /// where that sentence is load-bearing was the one direction with no
    /// re-check, and a pass that mutated `body_gate` after the stamp could hand
    /// a consumer a non-empty `codegen_inventory()` next to a refusal.
    ///
    /// The forgery below is exactly that shape: stamp honestly (leg 4 refuses,
    /// both bodies become `Ungated`), then write a `Gated` claim under this
    /// producer's own authority — the one `inventory_from_stamps` counts.
    /// Before the fix this PUBLISHED, with `codegen_inventory() == [FuncId(1)]`
    /// and `codegen_license_refusal().is_some()`. (The appended body is a
    /// non-Clean producer's: since plan step 3.4 a Clean one no longer refuses.)
    #[test]
    fn a_forged_gate_written_after_a_refused_stamp_refuses_publication() {
        let mut m = module_of(vec![
            defined(0, "direct", Producer::TRust),
            defined(1, "appended", Producer::TRust),
        ]);
        let refusal = stamp(&mut m, &assigned(1)).expect("leg 4 must refuse");
        assert!(inventory_from_stamps(&m).is_empty(), "the honest stamp licenses nothing");
        m.functions[1].body_gate =
            Some(BodyGate::Gated { authority: TRUST_DIRECT_LANE_AUTHORITY.to_string(), evidence: None });
        let decision = decide_publication("k", m, &assigned(1), &[], Some(refusal));
        let err = err_of(&decision);
        assert!(err.contains("license was REFUSED"), "{err}");
        assert!(err.contains("licenses NOTHING"), "{err}");
        assert!(err.contains("FuncId 1"), "{err}");
    }

    /// The other direction of the same re-check, so the new leg cannot be a
    /// blanket refusal: an HONESTLY refused license publishes fine, with an
    /// empty inventory and the refusal carried. Possession is not a license.
    #[test]
    fn an_honestly_refused_license_still_publishes_with_an_empty_inventory() {
        let decision = stamp_then_publish(
            "k",
            module_of(vec![
                defined(0, "direct", Producer::TRust),
                defined(1, "appended", Producer::TRust),
            ]),
            &assigned(1),
            &[],
        );
        let published = ok_of(&decision);
        assert!(published.codegen_inventory().is_empty());
        assert!(published.codegen_license_refusal().is_some());
        // The module is still handed over — a consumer needs it as lowering
        // context and for disclosure. Publication and license are separate.
        assert_eq!(published.module().functions.len(), 2);
    }

    /// An ambiguous name resolves to NO ONE. `Module::function_by_name` hands
    /// back the FIRST match; a consumer routing an intra-module call through
    /// that would call the wrong function, silently.
    #[test]
    fn an_ambiguous_symbol_is_removed_from_the_map_and_reported() {
        let m = module_of(vec![
            defined(0, "dup", Producer::TRust),
            defined(1, "uniq", Producer::TRust),
            declaration(2, "dup"),
        ]);
        let (symbols, ambiguous) = build_symbol_map(&m);
        assert_eq!(symbols.get("uniq"), Some(&FuncId::new(1)));
        assert_eq!(symbols.get("dup"), None);
        assert_eq!(ambiguous, vec!["dup".to_string()]);
        // The hazard this exists to refuse, stated as the contrast it is:
        assert_eq!(m.function_by_name("dup").map(|f| f.id), Some(FuncId::new(0)));
    }
}

/// Trust (WS5.2): the frozen-file claims of WS5.2, each backed by a test that fails if it is
/// false. `scripts/frozen-waivers.txt` cites them: the MIR oracle's input and the seam
/// differential's verdicts did not move when `Function.name` became the link-time symbol (the
/// two ORACLE-ADJACENT hunks), the finalizer's symbol stamping only names splice candidates and
/// only ever ADDS a refusal, the temporal-action identity check is exactly as strong as it was,
/// and the WS5.2 refusals join the per-body refusal fixpoint without removing anything from it.
#[cfg(test)]
mod ws5_2_oracle_input_tests {
    use super::*;

    fn function(name: &str, display_path: Option<&str>) -> Function {
        let mut f = Function::new(FuncId::new(0), name, FuncTyId::new(0), BlockId::new(0));
        f.display_path = display_path.map(str::to_string);
        f
    }

    /// The expected-absent set `build_expected_absent_bundle` hands the MIR oracle is keyed by
    /// the DEF PATH the oracle names a callee by. Before WS5.2 that string was `Function.name`;
    /// now the name is the link-time symbol and the def path is `display_path`. A row with no
    /// display path (the identity-less declarations) still answers with its name.
    #[test]
    fn the_oracle_names_a_callee_by_its_def_path_never_its_link_symbol() {
        let symbol_named = function("_RNvCs0_7fixture3add", Some("fixture::add"));
        assert_eq!(oracle_callee_name(&symbol_named), "fixture::add");
        let identity_less = function("!unknown_callee_3", None);
        assert_eq!(oracle_callee_name(&identity_less), "!unknown_callee_3");
    }

    /// Every note is the same coverage-only SKIP; WS5.2 split the note by cause and nothing
    /// else. The unsignable-edge note keeps precedence over the link-identity one, so the
    /// scorecard buckets that existed before WS5.2 count exactly what they counted, and a body
    /// with neither cause keeps the const-resolution note.
    #[test]
    fn the_seam_skip_note_splits_by_cause_and_is_always_a_coverage_only_skip() {
        let reasons = |tags: &[&str]| -> Vec<(String, u64)> {
            tags.iter().map(|tag| (format!("{tag}detail)"), 1)).collect()
        };
        let link = unsupported_body_skip_note(&reasons(&[crate::link_symbol::NO_LINK_SYMBOL_TAG]));
        assert!(link.contains("link-time symbol identity"), "{link}");
        let collision =
            unsupported_body_skip_note(&reasons(&[crate::link_symbol::LINK_SYMBOL_COLLISION_TAG]));
        assert_eq!(collision, link);
        let unsignable = unsupported_body_skip_note(&reasons(&[UNSIGNABLE_BODY_REASON_TAG]));
        assert!(unsignable.contains("unsignable Rust-ABI call edge"), "{unsignable}");
        assert_eq!(
            unsupported_body_skip_note(&reasons(&[
                crate::link_symbol::NO_LINK_SYMBOL_TAG,
                UNSIGNABLE_BODY_REASON_TAG,
            ])),
            unsignable,
            "the pre-WS5.2 unsignable-edge bucket keeps every body it counted"
        );
        let other = unsupported_body_skip_note(&reasons(&["PendingConstUnresolved("]));
        assert!(other.contains("finalizer const resolution failed"), "{other}");
        for note in [link, unsignable, other] {
            assert!(
                note.starts_with("seam-deferred body: ") && note.ends_with("; coverage-only skip"),
                "{note}"
            );
        }
    }

    fn row(id: u32, name: &str, display_path: Option<&str>, body: bool) -> Function {
        let mut f = Function::new(FuncId::new(id), name, FuncTyId::new(0), BlockId::new(0));
        f.display_path = display_path.map(str::to_string);
        if body {
            f.blocks.push(trust_ir::Block::new(BlockId::new(0)));
        }
        f
    }

    fn module_of(functions: Vec<Function>) -> Module {
        let mut m = Module::new("ws5_2_probe");
        m.functions = functions;
        m
    }

    /// The temporal-action identity check binds the assigned row only when it is a DEFINITION
    /// displaying exactly the action's def path — never a declaration, never another row, never
    /// the link-time symbol (the pre-WS5.2 check compared the name, which WAS the def path).
    #[test]
    fn a_temporal_action_binds_only_a_definition_displaying_its_def_path() {
        let def = "probe::Counter::step";
        let m = module_of(vec![
            row(0, "_RNvMCs0_5probe7Counter4step", Some(def), true),
            row(1, "_RNvMCs0_5probe7Counter5reset", Some("probe::Counter::reset"), true),
            // A declaration displaying the same path does not count: pass 2's collision set
            // ranged over spliced bodies only.
            row(2, "_RNvCs0_5other4step", Some(def), false),
        ]);
        assert!(temporal_action_row_corroborates(&m, FuncId::new(0), def));
        assert!(!temporal_action_row_corroborates(&m, FuncId::new(1), def));
        assert!(!temporal_action_row_corroborates(&m, FuncId::new(2), def));
        assert!(!temporal_action_row_corroborates(&m, FuncId::new(9), def));
        assert!(
            !temporal_action_row_corroborates(&m, FuncId::new(0), "_RNvMCs0_5probe7Counter4step"),
            "the link-time symbol is not the def path"
        );
    }

    /// The refusal the pre-WS5.2 collision rename made, kept: pass 2 renamed EVERY member of a
    /// display-path collision set to `!trust_definition::<path>::<definition>`, so an action
    /// whose def path two spliced bodies shared matched neither. Symbols are injective, so the
    /// rename is gone and `temporal_action_row_corroborates` refuses the collision itself.
    /// Mutation control: dropping its uniqueness conjunct makes both asserts below fail.
    #[test]
    fn a_def_path_two_definitions_display_binds_neither_as_the_collision_rename_refused() {
        let def = "probe::Counter::step";
        let m = module_of(vec![
            row(0, "_RNvMCs0_5probe7Counter4step", Some(def), true),
            row(1, "_RNvMs_Cs0_5probe7Counter4step", Some(def), true),
        ]);
        assert!(!temporal_action_row_corroborates(&m, FuncId::new(0), def));
        assert!(!temporal_action_row_corroborates(&m, FuncId::new(1), def));
    }

    /// `stamp_link_symbols` NAMES splice candidates and only ever ADDS a refusal: it asks for a
    /// symbol only for a fn body `splice_ok` admits, names an initializer by its reserved
    /// spelling without asking, refuses a symbol-less body by name (one `NoLinkTimeSymbol(` row,
    /// which `splice_ok` then refuses on), and leaves every other record untouched. No record
    /// loses an `unsupported` row and no record `splice_ok` refused before is admitted after.
    #[test]
    fn stamping_names_only_splice_candidates_and_only_ever_adds_refusals() {
        use super::authority_tests::lineage_body_record;
        let unstamped = |def_index: u32, def_path: &str| {
            let mut r = lineage_body_record(def_index, def_path);
            r.link_symbol = None;
            r
        };
        let mut initializer = unstamped(3, "probe::INIT::{const-init}");
        initializer.kind = BodyKind::ConstInit;
        let mut placeholder = unstamped(4, "probe::placeholder");
        placeholder.union_lane = true;
        let mut records = vec![
            unstamped(1, "probe::named"),
            unstamped(2, "probe::unnamed"),
            initializer,
            placeholder,
        ];
        let spliceable_before: Vec<bool> = records.iter().map(|r| splice_ok(r, &records)).collect();
        assert_eq!(spliceable_before, vec![true, true, true, false], "fixture premise");
        let unsupported_before: Vec<Vec<(String, u64)>> =
            records.iter().map(|r| r.unsupported.clone()).collect();

        let mut asked = Vec::new();
        let refused = stamp_link_symbols_with(
            &mut records,
            |def_index, def_path| {
                asked.push(def_index);
                if def_index == 2 {
                    Err(crate::link_symbol::no_link_symbol_reason(def_path, "fixture"))
                } else {
                    Ok(format!("_Rfixture_{def_index}"))
                }
            },
            |_| CalleeLink::default(),
        );

        assert_eq!(asked, vec![1, 2], "only fn splice candidates are asked for a symbol");
        assert_eq!(records[0].link_symbol.as_deref(), Some("_Rfixture_1"));
        assert_eq!(records[0].callee_links.len(), records[0].callees.len());
        assert_eq!(records[1].link_symbol, None);
        assert_eq!(refused.len(), 1);
        assert_eq!(refused[0].def_index, 2);
        assert!(refused[0].reason.starts_with(crate::link_symbol::NO_LINK_SYMBOL_TAG));
        assert_eq!(
            records[2].link_symbol,
            Some(crate::link_symbol::initializer_symbol(records[2].definition))
        );
        assert_eq!(records[3].link_symbol, None, "a body splice_ok refuses is never named");
        assert!(records[3].callee_links.is_empty());

        let spliceable_after: Vec<bool> = records.iter().map(|r| splice_ok(r, &records)).collect();
        assert_eq!(spliceable_after, vec![true, false, true, false]);
        for (index, (before, after)) in spliceable_before.iter().zip(&spliceable_after).enumerate()
        {
            assert!(!after || *before, "record {index} was refused before and admitted after");
            let kept = unsupported_before[index]
                .iter()
                .all(|row| records[index].unsupported.contains(row));
            assert!(kept, "record {index} lost an unsupported row");
        }
        assert_eq!(records[1].unsupported.len(), unsupported_before[1].len() + 1);
        for index in [0, 2, 3] {
            assert_eq!(records[index].unsupported, unsupported_before[index]);
        }
    }

    /// `decl_id` treats a declaration row's link facts as a CHECKED fact, like its name, ABI and
    /// source identity: two observations of one callee identity that disagree about its symbol
    /// or its producer poison the row (`DeclSigState::Conflict`, a fatal assembly error at
    /// append) — never first- or last-writer wins — and an agreeing observation changes nothing.
    #[test]
    fn a_declaration_whose_observations_disagree_on_link_facts_is_poisoned() {
        let definition = crate::lineage::DefinitionIdentity::test_only(0xD3C2, 3);
        let concrete = crate::lineage::ConcreteCalleeKey::test_only(
            definition,
            crate::lineage::ConcreteInstanceKind::Item,
            Vec::new(),
        );
        let link = |symbol: &str| CalleeLink {
            symbol: Some(symbol.to_string()),
            producer: Some(trust_ir::Producer::TRust),
            instance_lane_spelling: false,
            foreign_signature: None,
            foreign_source: None,
        };
        let observe = |decls: &mut Vec<DeclRecord>, link: CalleeLink| {
            decl_id(
                decls,
                1,
                "extern:probe::callee|concrete-v1:key".to_string(),
                "probe::callee".to_string(),
                None,
                crate::calling_convention::FunctionAbi::RUST,
                Some(definition),
                Some(&concrete),
                None,
                None,
                crate::ParamSignature::Unsigned,
                link,
            )
        };
        let mut agreeing = Vec::new();
        let first = observe(&mut agreeing, link("_RNvCs0_5probe6callee"));
        assert_eq!(observe(&mut agreeing, link("_RNvCs0_5probe6callee")), first);
        assert_eq!(agreeing.len(), 1);
        assert!(matches!(agreeing[0].signature, DeclSigState::Unknown));

        let mut symbol_split = Vec::new();
        observe(&mut symbol_split, link("_RNvCs0_5probe6callee"));
        observe(&mut symbol_split, link("_RNvCs0_5probe5other"));
        assert_eq!(symbol_split.len(), 1, "one identity, one row");
        assert!(matches!(symbol_split[0].signature, DeclSigState::Conflict));

        let mut producer_split = Vec::new();
        observe(&mut producer_split, link("_RNvCs0_5probe6callee"));
        observe(
            &mut producer_split,
            CalleeLink { producer: None, ..link("_RNvCs0_5probe6callee") },
        );
        assert!(matches!(producer_split[0].signature, DeclSigState::Conflict));
    }

    /// Source text, the same instrument `validation_tripwire_order_tests` uses (needles BUILT,
    /// because this module is itself inside `include_str!`): in `finalize_and_dump` every record
    /// is stamped AFTER the pending constants resolve and BEFORE the first assembly, and the
    /// per-body refusal fixpoint's refused set is `unsignable_minting_bodies` EXTENDED by
    /// `symbol_collision_minting_bodies` — a union, so the WS5.2 refusal removes nothing the
    /// fixpoint refused before.
    #[test]
    fn the_ws5_2_refusals_join_the_finalize_fixpoint_without_removing_any() {
        let src = crate::source_scan::sibling_source("crate_module.rs");
        let sole = |needle: &str| {
            let mut hits = src.match_indices(needle);
            let (at, _) = hits.next().unwrap_or_else(|| panic!("anchor vanished: {needle}"));
            assert!(hits.next().is_none(), "anchor is no longer unique: {needle}");
            at
        };
        let resolve = sole(concat!("    resolve_pending_consts(tcx, ", "&mut records);"));
        // `assemble_query_body` stamps its one-body record too: pin the `finalize_and_dump` call.
        let stamp =
            sole(concat!("let link_symbol_refusals = stamp_link_", "symbols(tcx, &mut records);"));
        let first_assembly = sole(concat!(
            "let mut assembled = ",
            "assemble(&crate_name, &records, &spliced_veto);"
        ));
        assert!(resolve < stamp && stamp < first_assembly, "{resolve} {stamp} {first_assembly}");
        let unsignable = sole(concat!(
            "let mut refused = unsignable_minting_",
            "bodies(&assembled, &clean_origin_local_defs);"
        ));
        let union =
            sole(concat!("refused.extend(symbol_collision_", "minting_bodies(&assembled));"));
        let dedup = sole(concat!("        refused.sort();\n        refused.", "dedup();"));
        assert!(unsignable < union && union < dedup, "{unsignable} < {union} < {dedup}");
        assert!(stamp < unsignable);
    }
}

/// Trust (gap G2): publication is the LAST step of `finalize_and_dump`.
///
/// Source-text ordering, the same instrument (and the same
/// `include_str!`/`sole_offset` idiom) `validation_tripwire_order_tests` uses,
/// for the same reason: the regression compiles cleanly. A publication that
/// drifted ABOVE the clean-origin link would intern a module with no
/// cross-producer call edge in it — the very edge that is the point — and one
/// that drifted above the `validate_module` tripwire would publish bytes the
/// tripwire never saw.
#[cfg(test)]
mod crate_module_publication_order_tests {
    const SRC: &str = include_str!("crate_module.rs");

    fn sole_offset(needle: &str) -> usize {
        let mut hits = SRC.match_indices(needle);
        let (at, _) = hits.next().unwrap_or_else(|| panic!("anchor vanished: {needle}"));
        assert!(hits.next().is_none(), "anchor is no longer unique: {needle}");
        at
    }

    /// Trust (v41 codegen license): the STAMP is the LAST mutation, and
    /// everything that CONSUMES the module runs below it.
    ///
    /// Same instrument and the same reason as the test below: a stamp that
    /// drifted below the validator would ship a claim the validator never saw;
    /// below the F1 handoff clone or the artifact render it would ship bytes
    /// with `body_gate: None` on every function — which is the exact
    /// "the license licenses nothing on the wire" hole the stamp closes, and it
    /// would come back silently, because both spellings compile.
    #[test]
    fn the_license_stamp_runs_above_everything_that_consumes_the_module() {
        let stamp = sole_offset(concat!("stamp_codegen_license(&mut ", "assembled.module"));
        // FIRST occurrences: the production call sites. Later ones are other
        // tests' literal needles, which sit below `finalize_and_dump`.
        let validate = SRC
            .find(concat!("errors.extend(final_module_", "validation_errors(&assembled.module));"))
            .expect("the final module validation gate vanished");
        let handoff = SRC
            .find(concat!("crate::AssembledCrateModuleForCodegen::", "checked_with_ledger("))
            .expect("the F1 codegen handoff vanished");
        // The artifact pair is rendered (and the F-099 text companion guarded) by
        // `render_publication_bytes`, the one serialization site of the assembled module.
        let render = SRC
            .find(concat!("render_publication_", "bytes(&assembled.module)"))
            .expect("the artifact render vanished");
        let publish = sole_offset(concat!("ANCHOR-PUBLICATION", "-LAST (read by"));
        for (name, at) in [
            ("the module validator", validate),
            ("the F1 codegen handoff", handoff),
            ("the artifact render", render),
            ("publication", publish),
        ] {
            assert!(
                stamp < at,
                "{name} moved above the v41 license stamp ({name} at {at}, stamp at {stamp}); it \
                 would consume a module whose every function still claims nothing"
            );
        }
    }

    #[test]
    fn publication_runs_below_every_mutation_of_the_assembled_module() {
        let publish = sole_offset(concat!("ANCHOR-PUBLICATION", "-LAST (read by"));
        let append = sole_offset(concat!(
            "crate::clean_origin_join::", "prepare_clean_origin_with_rust_callees("
        ));
        let link = sole_offset(concat!("crate::clean_origin_join::", "link_prepared_clean_origin("));
        let install = sole_offset(concat!("install_direct_", "obligations("));
        // The FIRST occurrence is the production call — the unconditional final validation
        // gate that superseded the log-only tripwire at this seam. Later occurrences are other
        // tests' literal needles, which sit below `finalize_and_dump` in this file.
        let validate = SRC
            .find(concat!("errors.extend(final_module_", "validation_errors(&assembled.module));"))
            .expect("the final module validation gate vanished");
        for (name, at) in
            [("append", append), ("link", link), ("obligation birth", install), ("validate", validate)]
        {
            assert!(
                at < publish,
                "publication drifted above {name} ({name} at {at}, publish at {publish}); it \
                 would intern a module that is still being built"
            );
        }
    }
}

/// Trust (2026-09-25, the `FatPtr(ContainerVtable)` spelling): `ty_table_free`'s fat-pointer
/// classification, pinned kind by kind. The splice may move a type verbatim only when it carries
/// no index into this body's tables. The id-less kinds (`Str`, both container kinds and
/// `TraitObject`, whose `trait_id` is a content hash) are table-free; `Slice(TyId)` names the type
/// table and is not. Refusing an id-less kind is not the safe direction here: it declines the
/// SPLICE of every body whose signature mentions one, so those types are never emitted to validate
/// (the "green from emitting nothing" shape the `ContainerLen` note records).
#[cfg(test)]
mod ty_table_free_fat_kind_tests {
    use trust_ir::{FatPtrKind, Ty, TyId};

    use super::ty_table_free;

    #[test]
    fn the_id_less_fat_kinds_are_table_free_and_the_table_indexed_one_is_not() {
        for kind in [
            FatPtrKind::Str,
            FatPtrKind::ContainerLen,
            FatPtrKind::ContainerVtable,
            FatPtrKind::TraitObject { trait_id: 7 },
        ] {
            let t = Ty::FatPtr(kind.clone());
            assert!(ty_table_free(&t), "{kind:?} is id-less and must splice verbatim");
            assert!(
                ty_table_free(&Ty::Tuple(vec![Ty::U64, t.clone()])),
                "{kind:?} nested in a tuple is still table-free"
            );
        }
        assert!(
            !ty_table_free(&Ty::FatPtr(FatPtrKind::Slice(TyId::new(3)))),
            "a Slice fat pointer names the type table and must be remapped, never moved"
        );
    }

}
