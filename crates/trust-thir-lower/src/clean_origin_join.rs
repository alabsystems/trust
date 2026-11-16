// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0 or the MIT license.

//! Clean-origin functions joining the per-crate direct Module — increments
//! IR-1 (append), IR-2/kernel-tv (faithfulness tier), and IR-5 (call-edge
//! linking) of `docs/design/2026-08-27-two-language-direct-to-trust-ir.md`.
//!
//! The collection side lives in `rustc_mir_transform::clean_origin_ir` (it
//! needs the kernel session, the plan pipeline, and the faithfulness gate —
//! none of which this crate may depend on). This module owns the OTHER half:
//! appending the collected records to the assembled Module while preserving
//! every invariant `crate_module` established, deciding each row's honest
//! TIER, re-pointing the caller's declaration edges onto the appended
//! definitions, and disclosing all of it in-band.
//!
//! # The invariants, restated as this module's contract
//!
//! * `module.functions[i].id == i` stays dense: ids are minted here, as
//!   `functions.len()` at push; the link pass moves no rows (orphaned
//!   declaration rows stay — deleting would renumber).
//! * ZERO claim channels in the PUBLISHED module: no summary, no proofs, no
//!   obligations, no certificates. The kernel-tv obligation/certificate live
//!   in a SCRATCH mini-module only (the tripwire's beside-the-module rule);
//!   the caller re-runs `direct_authority_inventory_errors` after the append
//!   AND the link as defense in depth.
//! * Every appended function is validated per-function over a one-function
//!   mini-module (structural), and — when the collection minted a TV payload —
//!   the SAME mini-module, now carrying the obligation + CleanCic certificate,
//!   is put through `trust_ir_build::validate_module` a second time, which
//!   routes it to the `clean_backend_tv` re-checker: the emitted side's
//!   denotation is RE-DERIVED from the mini-module and the CIC kernel decides
//!   the `CleanTV.<fn>.denotes` equation on theorem insertion. Empty errors =
//!   tier `kernel-tv`. For historical non-target rows, a re-check failure
//!   DEMOTES to `structural` with a loud `tv-refused` note (its own class —
//!   never conflated with a fragment skip) and does not fail the compile. The
//!   bounded WrappingBinOp target is different: its TV is an independent
//!   companion to carrier authority, so a missing/refused companion is a fatal
//!   compiler disagreement and is never demoted.
//! * Tier honesty (docs/TCB.md rows bind): `kernel-tv` records a kernel-decided
//!   defeq of two MINTED Nat-mod-2^w denotations — trusted, unmechanized
//!   checker-spec maps with correlated authorship — and carrier faithfulness is
//!   NOT established (G3). Every kernel-tv row keeps `body_gate: ungated`, so a
//!   tier-ignorant consumer still refuses. Unknown tier values must be treated
//!   as ungated by consumers (fail-closed default). The strictly bounded
//!   `gate` rung exists for exactly the shapes `trust_clean_ir_gate::gate_targets`
//!   targets — `wrapping-binop` (Add/Sub/Mul), `projection`, `constant-uint` and
//!   `composed`, at exact UInt8/16/32/64 with a direct source and no erased
//!   hypothesis (`GATED_SHAPE_TAGS`): an independent reflector inspected the
//!   actual Function, the Clean kernel decided carrier-level defeq, and this
//!   seam authenticated a private digest-bound token before publishing it.
//!   (This paragraph said "only for WrappingBinOp" until plan step 3.4; the
//!   reflector has covered four shapes since the W2 widening.)
//!
//! # The carrier and the ledger (plan step 3.4, owner rulings D36/D37)
//!
//! A `gate` row's published Function carries
//! `body_gate = Gated { authority: "clean-carrier-gate" }`
//! (`trust_clean_ir_gate::CLEAN_CARRIER_GATE_AUTHORITY`), stamped HERE before the
//! final authentication, so the published subject digest binds the stamp. The
//! token also binds the kernel environment the verdict was decided in: the
//! record carries the collector's `GateEnvironment` and the append refuses a
//! token minted in another one (fatal, like every targeted disagreement). The
//! authenticated `PublishedTrustIrFaithful` of every `gate` row is handed to the
//! finalize in [`CleanOriginJoinSummary::gated`]; `crate_module`'s per-function
//! leg 4 re-authenticates it against the Function before honoring the stamp, and
//! the F1 handoff keeps it as the session's ledger. The stamp alone proves
//! nothing (trust-ir never interprets `BodyGate`), it is a codegen license and
//! never a proof grade, and no lane may honor it without its ledger entry
//! (`docs/design/2026-10-02-step3-lean-through-trust-ir.md` §4). Every other
//! row's Function still publishes with no licensing claim of its own; the
//! codegen license stamps it `Ungated`.
//!
//! # Call-edge linking (IR-5)
//!
//! Assemble pass 2 minted a fail-closed bodyless `local-unlowered` declaration
//! for every admitted Rust→Clean call edge. [`link_clean_origin_edges`] re-points
//! those edges onto the appended definitions — post-append, per the design's
//! chosen shape — under six guards:
//!
//! * matching requires the ledger's exact same-crate source `DefIndex`; the
//!   normalized `def_path` is checked only as corroborating display identity,
//!   and a same-path/different-identity candidate is fatal rather than linkable;
//! * the bodyless declaration and appended definition must name the same
//!   calling convention; a convention change stays declared and is disclosed
//!   before any direct or reified edge is considered;
//! * an already-signed declaration with a direct call must carry the appended
//!   definition's exact module-local `FuncTyId`; a same-arity or structurally
//!   equal but separately interned signature cannot authorize that rewrite;
//! * every edge is arity- AND type-guarded (`results.len()` / `args.len()`, and
//!   then each argument's and result's type, against the target signature) — a
//!   site that binds a different result count, or passes a differently-typed
//!   operand, stays declared, disclosed per edge. The bullet above covers an
//!   already-SIGNED declaration by exact `FuncTyId`; this one is what guards the
//!   ordinary UNSIGNED declaration (`params: []` + `is_vararg`), which is the
//!   encoding a Clean `def` that never lowered through THIR actually gets, and
//!   where arity used to be the whole check. A position the seam cannot DECIDE
//!   (a refinement, a `Ty::Error` hole, an unreconstructable SSA value, or two
//!   ids under one table-indexed constructor) is linked but disclosed in
//!   `type_unchecked`, never refused: a refusal here is a fatal finalization
//!   error, and "not established" is not "wrong";
//! * every reified function-pointer edge carries a resolvable `Ty::Func` whose
//!   exact `FuncTyId` equals the target's id (thereby binding parameters,
//!   returns, and the vararg bit); a mismatch stays on the declaration and is
//!   disclosed;
//! * every touched function must pass the EXECUTABLE remap-shape certificate
//!   (`remap_certificate::certify_remap_shape` — discriminants, results,
//!   blocks, params, spans all unchanged; only callee ids may move), making
//!   "pass 3 writes callee ids and nothing else" a checked property rather
//!   than the argument pass 2 rides on. A certificate failure restores the
//!   function untouched and discloses.
//!
//! The currently admitted edge set is direct `Inst::Call` plus a top-level
//! `Constant::FnDef`. Producer confinement refuses `Invoke`, closure/nested
//! function identities, and global function references before this seam;
//! admitting any of those shapes requires extending this rewrite first.

use std::collections::{BTreeMap, BTreeSet};

use rustc_hir::def_id::LocalDefId;
use rustc_middle::ty::TyCtxt;
use trust_clean_ir_gate::{GateEnvironment, PublishedTrustIrFaithful, TrustIrFaithful};
use trust_ir::ty::{FuncTy, Ty};
use trust_ir::value::{FuncId, FuncTyId, TyId, ValueId};
use trust_ir::{Constant, Function, Inst, Module, Producer, SpecInvariant, SpecModule};

mod checked_ids;

/// The disclosure SpecModule name. Reserved; a user module colliding with it
/// is an error (same rule as the deferred-verification disclosure).
pub const CLEAN_ORIGIN_DISCLOSURE_NAME: &str = "@trust-internal::clean-origin-disclosure-v1";

/// The kernel-tv payload minted at the collection seam: the
/// `TranslationValidation` obligation and its `CleanCic` certificate. These
/// enter a SCRATCH mini-module only — never the published Module (the
/// authority tripwire's beside-the-module rule).
pub struct CleanTvMint {
    pub obligation: trust_ir::proof::ProofObligation,
    pub certificate: trust_ir::proof::ProofCertificate,
}

/// The faithfulness tier of a recorded row (design §4). Ordered weakest-first.
/// `Gate` is carrier-faithful evidence for one bounded same-crate slice; it is
/// not by itself a G5 cross-crate link or a G7 codegen certificate.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum CleanOriginTier {
    /// Emitted from the sealed plan, per-function validation passed, no
    /// symbolic gate on the body.
    Structural,
    /// Additionally: the CIC kernel decided `CleanTV.<fn>.denotes` — defeq of
    /// two minted denotations at Nat mod 2^w. NOT carrier faithfulness (G3);
    /// still `body_gate: ungated`.
    KernelTv,
    /// The actual emitted Function was independently reflected, kernel-checked
    /// at the exact carrier, and authenticated against a private SHA-256
    /// digest-bound token at this append seam.
    Gate,
}

impl CleanOriginTier {
    pub fn tag(self) -> &'static str {
        match self {
            CleanOriginTier::Structural => "structural",
            CleanOriginTier::KernelTv => "kernel-tv",
            CleanOriginTier::Gate => "gate",
        }
    }
}

/// Plan step 3.5 (docs/design/2026-10-02-step3-lean-through-trust-ir.md §5.1; owner ruling D37
/// part 1, "state the F1 rows' authority in the disclosure"): whether the recorder re-earned the
/// kernel verdict of the def's emitted MIR body at the finalize seam, as the disclosure's
/// `mir_gate` field states.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MirGateAtSeam {
    /// The MIR lane (verification on, not F1): the emitted MIR body was demanded and its kernel
    /// `Faithful` re-earned at this seam.
    Reearned,
    /// F1 (plan step 3.5): the recorder demanded no MIR body and re-earned no MIR verdict. F1
    /// ships this trust-ir Function, whose authority is its tier (the carrier gate for a `gate`
    /// row, none below it).
    NotOnF1,
}

impl MirGateAtSeam {
    /// The disclosure's `mir_gate` text. `Reearned`'s is byte-identical to the text every row
    /// carried before plan step 3.5.
    pub fn disclosure(self) -> &'static str {
        match self {
            MirGateAtSeam::Reearned => {
                "kernel Faithful earned for the emitted MIR body at the finalize seam"
            }
            MirGateAtSeam::NotOnF1 => {
                "not earned on F1 (plan step 3.5): the recorder demanded no MIR body and \
                 re-earned no MIR verdict at the finalize seam; F1 ships this trust-ir Function, \
                 whose authority is its tier (the carrier gate for a `gate` row, none below it)"
            }
        }
    }
}

/// One Clean-origin def whose trust-ir spelling was emitted under a freshly
/// re-earned kernel verdict (for the emitted MIR body on the MIR lane, for the
/// published Function on F1 — see the tier wording and [`MirGateAtSeam`]).
pub struct CleanOriginIrRecord {
    /// `DefIndex` of the minted def, for coverage rows.
    pub def_index: u32,
    /// The Rust-side path (`with_no_trimmed_paths` `def_path_str`) — the
    /// shared-namespace spelling AND the IR-5 linkage key.
    pub def_path: String,
    /// The Clean declaration name as the kernel knows it.
    pub clean_name: String,
    /// Stable shape tag (e.g. `"wrapping-binop"`).
    pub shape: &'static str,
    /// Whether the sealed plan is a carrier-gate TARGET
    /// (`trust_clean_ir_gate::gate_targets`): computed by the collector from
    /// the plan, which the join cannot see. The join enforces the exact-set
    /// contract against it: a target MUST carry `gate`, a non-target MUST NOT,
    /// and a `gate` on a shape outside `GATED_SHAPE_TAGS` is refused outright.
    pub gate_target: bool,
    /// The signature as `trust-clean-ir` derives it from the carrier
    /// signature. Interned into `module.func_types` at append.
    pub signature: FuncTy,
    /// The emitted function. `id`/`ty` are placeholders until append.
    pub function: Function,
    /// Private permission for the exact gated Function/signature. Must be
    /// `Some` exactly when `gate_target`; missing, surplus, or stale evidence
    /// is a fatal semantic-finalization error, never a demotion.
    pub gate: Option<TrustIrFaithful>,
    /// Plan step 3.4 (design §4.2): the kernel environment the collector says
    /// this row comes from (the island batch's dependency-closure digest of the
    /// declaration and the Clean kernel version). `Some` exactly when `gate`
    /// is; the append refuses a token whose verdict environment differs.
    pub gate_environment: Option<GateEnvironment>,
    /// The kernel-tv payload, when the mint's fragment covered the shape.
    pub tv: Option<CleanTvMint>,
    /// Why kernel-tv was not attempted (fragment skip, with v7/D3 options).
    pub tv_note: Option<String>,
    /// Plan step 3.5: what the recorder did with the def's MIR body, for the disclosure.
    pub mir_gate: MirGateAtSeam,
}

/// One Clean-origin def the producer could not spell — a capability gap, never
/// a verdict. `reason` carries fix options (v7/D3).
pub struct CleanOriginIrSkip {
    pub def_index: u32,
    pub def_path: String,
    pub clean_name: String,
    pub shape: &'static str,
    /// See `CleanOriginIrRecord::gate_target`. A targeted plan never arrives
    /// here (its precursor refusals are fatal in the collector); the flag is
    /// carried so the append belt can refuse one that does.
    pub gate_target: bool,
    pub reason: String,
}

/// A sealed call plan awaiting targets owned by the actual assembled module.
/// It carries no gate token, effect summary, or kernel-TV authority.
#[derive(Clone)]
pub struct CleanOriginRustCallRecord {
    pub def_index: u32,
    pub def_path: String,
    /// Trust (WS5.2): the minted Rust item's LINK-TIME SYMBOL, computed by the collector (which
    /// has `tcx`). The emitted row is NAMED by it; the Lean spelling becomes `display_path`.
    pub link_symbol: String,
    pub clean_name: String,
    /// Shared immutable kernel snapshot and plan; this is not gate authority.
    pub source: trust_clean_ir_gate::rust_calls::RetainedRustCallSource,
    pub callees: Vec<CleanOriginRustCallee>,
    /// Plan step 3.5: what the recorder did with the def's MIR body, for the disclosure.
    pub mir_gate: MirGateAtSeam,
}

/// The collector's exact plan-row to registered Rust definition binding.
/// Extractor spelling and the full Rust path are deliberately separate.
#[derive(Clone)]
pub struct CleanOriginRustCallee {
    pub plan_index: usize,
    pub def_index: u32,
    pub definition: crate::lineage::DefinitionIdentity,
    pub def_path: String,
    pub signature: FuncTy,
    pub plan_def_path: String,
    pub clean_name: String,
}

impl CleanOriginRustCallee {
    pub fn from_def_id(
        tcx: TyCtxt<'_>,
        plan_index: usize,
        def: LocalDefId,
        signature: FuncTy,
        callee: &trust_clean_origin::RustCalleeRef,
    ) -> Self {
        Self {
            plan_index,
            def_index: def.local_def_index.as_u32(),
            definition: crate::lineage::DefinitionIdentity::from_def_id(tcx, def.to_def_id()),
            def_path: rustc_middle::ty::print::with_no_trimmed_paths!(
                tcx.def_path_str(def.to_def_id())
            ),
            signature,
            plan_def_path: callee.def_path.clone(),
            clean_name: callee.clean_name.clone(),
        }
    }
}

/// A Rust body actually spliced by assembly, before any Clean append.
#[derive(Clone)]
pub struct RustBodyIdentity {
    pub def_index: u32,
    pub definition: crate::lineage::DefinitionIdentity,
    pub func_id: FuncId,
    pub abi: crate::calling_convention::FunctionAbi,
    pub kind: crate::BodyKind,
    pub def_path: String,
}

/// Outcome per Clean-origin def, in registry order.
pub enum CleanOriginIrOutcome {
    Emitted(CleanOriginIrRecord),
    RustCalls(CleanOriginRustCallRecord),
    Skipped(CleanOriginIrSkip),
    /// The GENERAL lane's product (totality campaign): every computational
    /// island declaration compiled through clean-compiler's full pipeline,
    /// as one module + per-decl rows. At most one per crate.
    General(GeneralCleanIr),
}

/// One island declaration's general-lane outcome.
pub struct GeneralRow {
    pub clean_name: String,
    pub outcome: GeneralOutcome,
}

pub enum GeneralOutcome {
    /// Entered the compiled batch; its function(s) are in the general module.
    Compiled { tv_mint_certified: bool },
    /// The kernel holds no computational value (theorem/axiom/opaque/ctor) —
    /// per the 08-04 §2 ruling a disposition, not a gap.
    NotComputational,
    /// A capability gap, with the reason (v7/D3: options included).
    Skipped { reason: String },
}

/// The general lane's product: per-decl rows plus (when any decl compiled)
/// the emitted module — TV-rechecked in-tree and PROOF-CHANNEL-STRIPPED by
/// the collector before it reaches this crate.
pub struct GeneralCleanIr {
    pub rows: Vec<GeneralRow>,
    pub module: Option<Module>,
}

/// One published row, for disclosure/coverage.
pub struct EmittedRow {
    pub def_index: u32,
    pub def_path: String,
    pub clean_name: String,
    pub shape: &'static str,
    pub func_id: u32,
    pub tier: CleanOriginTier,
    /// SHA-256 subject identity authenticated after the Function received its
    /// final published id, type id, and Clean producer stamp.
    pub gate_subject_digest: Option<String>,
    /// Exact Clean carrier named by the authenticated gate.
    pub gate_carrier: Option<&'static str>,
    /// Kernel method named by the authenticated gate.
    pub gate_method: Option<&'static str>,
    /// Plan step 3.4 (design §4.2): the gate verdict's environment digest,
    /// kernel version and ledger digest, disclosed beside the subject digest.
    /// `Some` exactly for a `gate` row.
    pub gate_environment_digest: Option<String>,
    pub gate_kernel_version: Option<&'static str>,
    pub gate_ledger_digest: Option<String>,
    /// `tv_note` for structural rows (fragment skip with options), or the loud
    /// `tv-refused:` note when the kernel re-check demoted the row.
    pub tv_note: Option<String>,
}

/// Plan step 3.4 (design §4.1 part 3): one `gate` row's authenticated
/// published token, handed to the finalize. `crate_module` re-authenticates it
/// against the Function at `func_id` (leg 4) and installs it, with the source
/// definition identity, as the F1 handoff's session ledger entry. Not `Clone`:
/// the token is affine, and a row is never duplicated into a second ledger.
#[derive(Debug)]
pub struct GatedCleanRow {
    /// The published `FuncId` the stamp sits on.
    pub func_id: FuncId,
    /// The token `authenticate_published` returned for that exact Function.
    pub published: PublishedTrustIrFaithful,
}

/// Unlicensed context retained beside its exact published source module.
/// Function ids refer to that module, never a relocated codegen module.
#[derive(Clone)]
pub struct PendingRustCallSource {
    pub def_index: u32,
    pub func_id: FuncId,
    pub link_symbol: String,
    pub source: trust_clean_ir_gate::rust_calls::RetainedRustCallSource,
    pub bindings: Vec<trust_clean_ir_gate::rust_calls::RustCallBinding>,
}

/// One assembled declaration's identity at the Clean-origin relink seam.
///
/// `local_def_index` is `Some` exactly for a `local-unlowered` declaration. It is the
/// same-compilation source identity shared with [`EmittedRow::def_index`]; `key` remains the
/// declaration-class/display ledger used for census and diagnostics, never linking authority.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeclarationLinkIdentity {
    /// Dense id of the declaration whose incoming edges may be rewritten.
    pub func_id: FuncId,
    /// Declaration-class/census key, including the normalized display path.
    pub key: String,
    /// Exact same-compilation source `DefIndex`, present only for `local-unlowered`.
    pub local_def_index: Option<u32>,
}

/// One re-pointed (or refused) declaration edge set, for disclosure/coverage.
#[derive(Debug)]
pub struct LinkedRow {
    pub decl_func_id: u32,
    pub decl_key: String,
    /// Exact same-compilation source identity that authorized this link.
    pub source_def_index: u32,
    pub target_func_id: u32,
    pub def_path: String,
    pub edges_repointed: u32,
    /// Declaration-level calling-convention refusals, per-edge refusals (call arity, call
    /// operand/result TYPE, or function-pointer signature), and per-function certificate
    /// refusals, each disclosed rather than silently linked or skipped.
    pub refusals: Vec<String>,
    /// Operand positions on RE-POINTED edges this seam declined to DECIDE rather than
    /// silently pass: a refinement (trust-ir decides those in `validate_refinements`), a
    /// `Ty::Error` typing hole, an SSA value `typed_values` could not reconstruct, or two
    /// spellings under the same table-indexed constructor whose ids are not comparable
    /// across two separately interned signatures.
    ///
    /// DISCLOSURES, not refusals. The edge WAS linked, and — unlike [`Self::refusals`], every
    /// one of which is fatal since WS5.2 — these deliberately do not refuse the module, which
    /// is the wrong outcome for a program this seam merely could not check.
    ///
    /// A consumer that wants a TYPED link must require this EMPTY: an empty `refusals`
    /// alone no longer means "type-checked".
    pub type_unchecked: Vec<String>,
    /// ALWAYS `None` since WS5.2; the field (and its `retired_declaration` disclosure key) is
    /// kept so the disclosure schema does not move.
    ///
    /// It used to name the orphan declaration row the append left behind once the appended
    /// definition fully shadowed it, renamed `<def_path>::<shadowed-by-clean-origin:FuncId(N)>`
    /// out of the function namespace because dense ids forbade deleting it (measured
    /// 2026-09-11: a crate-root island's `ctrl_min` declaration and definition otherwise shared
    /// one name). That rename minted a name that is no symbol at all, which trust-ir's
    /// `SyntheticSymbolName` refuses (WS4.17). Since `Function.name` is the link-time symbol,
    /// the declaration and the definition of one Rust item carry ONE symbol, so `append` puts
    /// the definition IN the declaration's row and there is no orphan to retire.
    pub retired_declaration: Option<String>,
}

/// What the append did, for the coverage sidecar.
pub struct CleanOriginJoinSummary {
    pub recorded: bool,
    pub emitted: Vec<EmittedRow>,
    /// (def_index, def_path, clean_name, shape, reason)
    pub skipped: Vec<(u32, String, String, &'static str, String)>,
    /// IR-5 link outcomes (empty until [`link_clean_origin_edges`] runs).
    pub linked: Vec<LinkedRow>,
    /// General-lane rows: (clean_name, disposition, tv_mint_certified, reason).
    /// disposition ∈ {"compiled", "not-computational", "skipped",
    /// "merge-refused"}.
    pub general: Vec<(String, &'static str, bool, String)>,
    /// Function names merged from the general module (defined bodies only).
    pub general_functions: Vec<String>,
    /// ALWAYS EMPTY since WS5.2 (kept so the coverage schema does not move): general-lane
    /// definitions used to be recorded under a `general::` namespace when another row held
    /// their name; a symbol collision now refuses the whole general module instead.
    pub general_renamed: Vec<(String, String)>,
    /// Plan step 3.4: the authenticated published token of every `gate` row, in
    /// emission order, for the finalize ([`Self::take_gated`]). Empty when the
    /// transaction did not publish.
    pub gated: Vec<GatedCleanRow>,
    /// Data only; no gate row, summary, codegen inventory entry or permission.
    pub pending_rust_calls: Vec<PendingRustCallSource>,
    /// Plan step 3.5: what the recorder did with each recorded def's MIR body, by `def_index`,
    /// for the disclosure's `mir_gate` field.
    pub mir_gate: BTreeMap<u32, MirGateAtSeam>,
}

impl CleanOriginJoinSummary {
    pub fn not_recorded() -> Self {
        Self {
            recorded: false,
            emitted: Vec::new(),
            skipped: Vec::new(),
            linked: Vec::new(),
            general: Vec::new(),
            general_functions: Vec::new(),
            general_renamed: Vec::new(),
            gated: Vec::new(),
            pending_rust_calls: Vec::new(),
            mir_gate: BTreeMap::new(),
        }
    }

    /// Plan step 3.4: hand the published tokens to the finalize, once. The
    /// summary keeps every disclosure row.
    pub fn take_gated(&mut self) -> Vec<GatedCleanRow> {
        std::mem::take(&mut self.gated)
    }
}

/// Append the collected Clean-origin functions to the assembled module and
/// install the in-band disclosure.
pub fn append_clean_origin(
    module: &mut Module,
    outcomes: Vec<CleanOriginIrOutcome>,
    errors: &mut Vec<String>,
) -> CleanOriginJoinSummary {
    append_clean_origin_with_rust_callees(module, outcomes, errors, &[])
}

/// Append pending call plans only after binding their callees to the module's
/// owned Rust body inventory. The legacy entry supplies no such authority.
pub fn append_clean_origin_with_rust_callees(
    module: &mut Module,
    outcomes: Vec<CleanOriginIrOutcome>,
    errors: &mut Vec<String>,
    rust_bodies: &[RustBodyIdentity],
) -> CleanOriginJoinSummary {
    let prepared =
        prepare_clean_origin_with_rust_callees(module, outcomes, errors, rust_bodies, &[]);
    link_prepared_clean_origin(module, prepared, &[], errors)
}

/// An unpublished batch over a clone of the actual assembled module. Its
/// summary is available for the caller's pre-link identity/overlap checks;
/// neither bodies nor signed declarations are published by preparation.
pub struct PreparedCleanOriginJoin {
    original: Module,
    module: Module,
    summary: CleanOriginJoinSummary,
}

impl PreparedCleanOriginJoin {
    pub fn summary(&self) -> &CleanOriginJoinSummary {
        &self.summary
    }
}

/// Trust (WS5.2): `declarations` is the assembly's declaration ledger; a Clean definition whose
/// exact source identity matches one `local-unlowered` row is published IN that row (one
/// link-time symbol, one row), and [`link_prepared_clean_origin`] must be given the same ledger.
pub fn prepare_clean_origin_with_rust_callees(
    module: &Module,
    outcomes: Vec<CleanOriginIrOutcome>,
    errors: &mut Vec<String>,
    rust_bodies: &[RustBodyIdentity],
    declarations: &[DeclarationLinkIdentity],
) -> PreparedCleanOriginJoin {
    let mut candidate = module.clone();
    let summary =
        append_clean_origin_candidates(&mut candidate, outcomes, errors, rust_bodies, declarations);
    PreparedCleanOriginJoin { original: module.clone(), module: candidate, summary }
}

/// Complete the batch transaction only after every candidate has been staged.
/// Exact declaration linking can now sign fully shadowed unsigned rows from
/// any outcome, independent of registry order. Rust call plans are validated
/// against this whole linked module, including every original Rust body.
/// A failed transaction never publishes a partial batch or demotes gate evidence.
pub fn link_prepared_clean_origin(
    module: &mut Module,
    prepared: PreparedCleanOriginJoin,
    declarations: &[DeclarationLinkIdentity],
    errors: &mut Vec<String>,
) -> CleanOriginJoinSummary {
    if !errors.is_empty() {
        return CleanOriginJoinSummary::not_recorded();
    }
    let PreparedCleanOriginJoin { original, module: mut candidate, mut summary } = prepared;
    if *module != original {
        errors.push(
            "clean-origin transaction refused: assembled module changed after preparation".into(),
        );
        return CleanOriginJoinSummary::not_recorded();
    }
    link_clean_origin_edges(&original, &mut candidate, declarations, &mut summary, errors);
    let rust_call_ids: BTreeSet<u32> = summary
        .emitted
        .iter()
        .filter(|row| row.shape == "rust-call-chain")
        .map(|row| row.func_id)
        .collect();
    // Structural validation alone cannot reject every semantic link refusal:
    // a variadic C declaration can remain structurally valid, for example.
    // A pending Rust call body is published only when its selected declaration
    // links actually passed the linker's identity, ABI, edge and shape guards.
    for row in &summary.linked {
        if rust_call_ids.contains(&row.target_func_id) && !row.refusals.is_empty() {
            errors.push(format!(
                "clean-origin Rust call transaction refused declaration `{}`: {}",
                row.decl_key,
                row.refusals.join("; ")
            ));
        }
    }
    if errors.is_empty() && !rust_call_ids.is_empty() {
        if let Err(reason) = render_validation(trust_ir_build::validate_module(&candidate)) {
            errors.push(format!("whole-module call validation refused: {reason}"));
        }
    }
    if !errors.is_empty() {
        return CleanOriginJoinSummary::not_recorded();
    }
    // Candidate diagnostics over the actual whole linked module, never a TV
    // companion or admission. Preserve every existing tier, body and token on
    // both outcomes: unsupported historical structural rows remain unlicensed.
    for pending in &summary.pending_rust_calls {
        let Some(row) = summary.emitted.iter_mut().find(|row| {
            row.def_index == pending.def_index
                && row.func_id == pending.func_id.index()
                && row.shape == "rust-call-chain"
                && row.tier == CleanOriginTier::Structural
        }) else {
            continue;
        };
        let result = pending.source.check_module_call_trace(
            &candidate,
            pending.func_id,
            &pending.bindings,
        );
        row.tv_note = Some(match result {
            Ok(()) => "linked-module candidate model/trace accepted; structural only: no \
                       independent kernel-TV companion, Rust semantic/effects evidence or \
                       codegen permission".into(),
            Err(refusal) => format!(
                "linked-module candidate model/trace refused ({}); structural only: no \
                 independent kernel-TV companion, Rust semantic/effects evidence or \
                 codegen permission",
                refusal.note(),
            ),
        });
    }
    *module = candidate;
    summary
}

fn append_clean_origin_candidates(
    module: &mut Module,
    outcomes: Vec<CleanOriginIrOutcome>,
    errors: &mut Vec<String>,
    rust_bodies: &[RustBodyIdentity],
    declarations: &[DeclarationLinkIdentity],
) -> CleanOriginJoinSummary {
    let mut summary = CleanOriginJoinSummary {
        recorded: true,
        emitted: Vec::new(),
        skipped: Vec::new(),
        linked: Vec::new(),
        general: Vec::new(),
        general_functions: Vec::new(),
        general_renamed: Vec::new(),
        gated: Vec::new(),
        pending_rust_calls: Vec::new(),
        mir_gate: BTreeMap::new(),
    };
    if module.spec_modules.iter().any(|spec| spec.name == CLEAN_ORIGIN_DISCLOSURE_NAME) {
        errors.push(format!(
            "reserved clean-origin disclosure name collision: {CLEAN_ORIGIN_DISCLOSURE_NAME}"
        ));
        return summary;
    }

    // Exact-set belt before any row is considered: one canonical Rust source
    // identity can contribute at most one emitted Clean body. This is a
    // population invariant, not token freshness — the affine token can be
    // minted independently twice for the same subject, so duplicated def paths
    // or definition indices make every colliding row fatal and unpublished.
    let mut seen_def_paths = BTreeSet::new();
    let mut duplicate_def_paths = BTreeSet::new();
    let mut seen_def_indices = BTreeSet::new();
    let mut duplicate_def_indices = BTreeSet::new();
    for outcome in &outcomes {
        let (def_path, def_index) = match outcome {
            CleanOriginIrOutcome::Emitted(record) => (&record.def_path, record.def_index),
            CleanOriginIrOutcome::RustCalls(record) => (&record.def_path, record.def_index),
            _ => continue,
        };
        if !seen_def_paths.insert(def_path.clone()) {
            duplicate_def_paths.insert(def_path.clone());
        }
        if !seen_def_indices.insert(def_index) {
            duplicate_def_indices.insert(def_index);
        }
    }
    for def_path in &duplicate_def_paths {
        errors.push(format!(
            "fatal clean-origin duplicate emitted canonical def_path `{def_path}`; every \
             colliding row was left unpublished (private gate evidence is not replay authority)"
        ));
    }
    for def_index in &duplicate_def_indices {
        errors.push(format!(
            "fatal clean-origin duplicate emitted source def_index `{def_index}`; every \
             colliding row was left unpublished (source identity must be injective)"
        ));
    }
    // Plan step 3.5 (D37 part 1): which lane earned the MIR gate, stated per row in the
    // disclosure. Disclosure only: nothing reads it as authority.
    for outcome in &outcomes {
        let (def_index, mir_gate) = match outcome {
            CleanOriginIrOutcome::Emitted(record) => (record.def_index, record.mir_gate),
            CleanOriginIrOutcome::RustCalls(record) => (record.def_index, record.mir_gate),
            _ => continue,
        };
        summary.mir_gate.insert(def_index, mir_gate);
    }

    for outcome in outcomes {
        match outcome {
            CleanOriginIrOutcome::Emitted(record) => {
                if duplicate_def_paths.contains(&record.def_path)
                    || duplicate_def_indices.contains(&record.def_index)
                {
                    continue;
                }
                let targeted = record.gate_target;
                if record.gate.is_some() && !trust_clean_ir_gate::gates_shape(record.shape) {
                    errors.push(format!(
                        "fatal clean-origin carrier-gate evidence on non-gated shape `{}` for \
                         `{}`; the gate reflects only {:?}. The row was not published.",
                        record.shape,
                        record.clean_name,
                        trust_clean_ir_gate::GATED_SHAPE_TAGS
                    ));
                    continue;
                }
                // The gate token is an exact-set contract, not optional
                // metadata. Authenticate while the Function still carries the
                // placeholder ids used at mint time; append mutates those ids.
                // Missing/surplus/stale evidence is a semantic-finalization
                // failure via `errors`, never a skip or tier demotion.
                match (targeted, record.gate.as_ref()) {
                    (true, Some(gate)) => {
                        // Plan step 3.4 (design §4.2): the token binds the
                        // environment its verdict was decided in; the record
                        // must name that same environment. Missing is fatal
                        // like a missing token.
                        let Some(environment) = record.gate_environment.as_ref() else {
                            errors.push(format!(
                                "fatal clean-origin carrier-gate environment missing for \
                                 targeted Clean `{}` `{}`; the row was not published and was \
                                 not demoted",
                                record.shape, record.clean_name
                            ));
                            continue;
                        };
                        let authenticated =
                            gate.authenticate_environment(environment).and_then(|()| {
                                gate.authenticate(
                                    &record.clean_name,
                                    record.def_index,
                                    &record.def_path,
                                    &record.signature,
                                    &record.function,
                                )
                            });
                        if let Err(refusal) = authenticated {
                            errors.push(format!(
                                "fatal clean-origin carrier-gate disagreement for targeted \
                                     Clean `{}` `{}`: {}. The row was not published and was \
                                     not demoted.",
                                record.shape,
                                record.clean_name,
                                refusal.note()
                            ));
                            continue;
                        }
                    }
                    (true, None) => {
                        errors.push(format!(
                            "fatal clean-origin carrier-gate evidence missing for targeted \
                                 Clean `{}` `{}`; the row was not published and was not \
                                 demoted",
                            record.shape, record.clean_name
                        ));
                        continue;
                    }
                    (false, Some(_)) => {
                        errors.push(format!(
                            "fatal clean-origin carrier-gate evidence attached to non-target \
                                 shape `{}` for `{}`; the private permission may not be widened",
                            record.shape, record.clean_name
                        ));
                        continue;
                    }
                    (false, None) => {
                        if record.gate_environment.is_some() {
                            errors.push(format!(
                                "fatal clean-origin carrier-gate environment attached to \
                                 non-target shape `{}` for `{}`; the exact-set contract is \
                                 token <=> environment",
                                record.shape, record.clean_name
                            ));
                            continue;
                        }
                    }
                }
                // A DEFINED (body-bearing) function already claiming this
                // link-time symbol would mean a THIR body and a Clean body claim one
                // def — a bijection break, refused (demoted to a skip). Trust (WS5.2): keyed
                // on the symbol the row is named by, which IS the def's identity, AND on the
                // def path the check compared before WS5.2 — now a row's `display_path` — so
                // nothing it refused is admitted (`defined_row_claims`).
                if defined_row_claims(module, &record.function.name, &record.def_path) {
                    if targeted {
                        errors.push(format!(
                            "fatal clean-origin append conflict for carrier-gated \
                             wrapping-binop `{}`: a defined function already claims `{}`; the \
                             gated row was not published and was not demoted",
                            record.clean_name, record.def_path
                        ));
                        continue;
                    }
                    summary.skipped.push((
                        record.def_index,
                        record.def_path.clone(),
                        record.clean_name,
                        record.shape,
                        format!(
                            "refused: a defined function already claims the name \
                             `{}` — a THIR body and a Clean body cannot claim one def. \
                             Report this; the registry and the HIR body-owner inventory \
                             are supposed to be disjoint.",
                            record.def_path
                        ),
                    ));
                    continue;
                }
                match validate_standalone(&record) {
                    Ok(()) => {
                        // Tier decision: the kernel-tv re-check, over the SAME
                        // mini-module now carrying the minted obligation +
                        // certificate. Empty errors = the CIC kernel accepted
                        // the `CleanTV.<fn>.denotes` equation (re-derived LHS).
                        let (tier, tv_note) = if targeted {
                            let Some(mint) = &record.tv else {
                                errors.push(format!(
                                    "fatal clean-origin evidence disagreement for carrier-gated \
                                     wrapping-binop `{}`: the expected kernel-TV companion is \
                                     missing ({})",
                                    record.clean_name,
                                    record.tv_note.as_deref().unwrap_or("no reason recorded")
                                ));
                                continue;
                            };
                            if let Err(reason) = recheck_kernel_tv(&record, mint) {
                                errors.push(format!(
                                    "fatal clean-origin evidence disagreement for carrier-gated \
                                     wrapping-binop `{}`: carrier gate authenticated but the \
                                     independent kernel-TV companion refused ({reason}); the row \
                                     was not published and was not demoted",
                                    record.clean_name
                                ));
                                continue;
                            }
                            (CleanOriginTier::Gate, None)
                        } else {
                            match &record.tv {
                                Some(mint) => match recheck_kernel_tv(&record, mint) {
                                    Ok(()) => (CleanOriginTier::KernelTv, None),
                                    Err(reason) => (
                                        CleanOriginTier::Structural,
                                        Some(format!(
                                            "tv-refused: the independent kernel re-check did \
                                             not accept the denotation equation ({reason}). \
                                             This is the signal the tier exists to surface — \
                                             the emitted trust-ir spelling could not be \
                                             kernel-identified with its source at Nat mod \
                                             2^w. The row publishes at tier structural; the \
                                             MIR lane's Faithful (the binary's gate) is \
                                             unaffected. Report this pairing."
                                        )),
                                    ),
                                },
                                None => (CleanOriginTier::Structural, record.tv_note.clone()),
                            }
                        };
                        // Compute the exact final Function without mutating the
                        // Module. The private gate then authenticates the
                        // placeholder subject, proves the relocation changed
                        // only id/ty/producer, reflects the final body again,
                        // and returns the digest that disclosure publishes.
                        let (ty, insert_ty) = match module
                            .func_types
                            .iter()
                            .position(|existing| existing == &record.signature)
                        {
                            Some(position) => (
                                FuncTyId::new(
                                    u32::try_from(position).expect("func_types exceeds u32"),
                                ),
                                false,
                            ),
                            None => (
                                FuncTyId::new(
                                    u32::try_from(module.func_types.len())
                                        .expect("func_types exceeds u32"),
                                ),
                                true,
                            ),
                        };
                        // Trust (WS5.2): the row this definition is published in — its Rust
                        // declaration's, when a Rust caller minted one (one link-time symbol,
                        // one row), else a fresh one at the end.
                        let slot = match declaration_slot(
                            module,
                            declarations,
                            record.def_index,
                            &record.function.name,
                        ) {
                            Ok(slot) => slot,
                            Err(reason) => {
                                errors.push(format!(
                                    "fatal clean-origin placement refusal for `{}` `{}`: \
                                     {reason}. The row was not published and was not demoted.",
                                    record.shape, record.clean_name
                                ));
                                continue;
                            }
                        };
                        let id = slot.unwrap_or_else(|| {
                            FuncId::new(
                                u32::try_from(module.functions.len())
                                    .expect("function count exceeds u32"),
                            )
                        });
                        let mut function = record.function.clone();
                        function.id = id;
                        function.ty = ty;
                        function.producer = Some(Producer::Clean);
                        // Plan step 3.4 (design §4.1 part 1, D37): a `gate`
                        // row carries the carrier stamp on the Function itself,
                        // written BEFORE the final authentication so the
                        // published digest binds it. Every other row keeps the
                        // emitter's (absent) claim; the codegen license stamps
                        // it `Ungated`.
                        if targeted {
                            function.body_gate =
                                Some(trust_clean_ir_gate::clean_carrier_gate_stamp());
                        }
                        let published = if targeted {
                            let gate = record
                                .gate
                                .as_ref()
                                .expect("target gate presence was checked above");
                            match gate.authenticate_published(
                                &record.clean_name,
                                record.def_index,
                                &record.def_path,
                                &record.signature,
                                &record.function,
                                &function,
                            ) {
                                Ok(published) => Some(published),
                                Err(refusal) => {
                                    errors.push(format!(
                                        "fatal clean-origin final-subject authentication \
                                         disagreement for targeted Clean `{}` `{}`: {}. \
                                         The row was not published and was not demoted.",
                                        record.shape,
                                        record.clean_name,
                                        refusal.note()
                                    ));
                                    continue;
                                }
                            }
                        } else {
                            None
                        };
                        let gate_subject_digest = published
                            .as_ref()
                            .map(|published| published.subject_digest().to_string());
                        let gate_carrier =
                            published.as_ref().map(|published| published.carrier_tag());
                        let gate_method =
                            published.as_ref().map(|published| published.method_tag());
                        let gate_environment_digest = published.as_ref().map(|published| {
                            published.environment().environment_digest().to_string()
                        });
                        let gate_kernel_version = published
                            .as_ref()
                            .map(|published| published.environment().kernel_version());
                        let gate_ledger_digest = published
                            .as_ref()
                            .map(|published| published.ledger_digest().to_string());
                        if insert_ty {
                            module.func_types.push(record.signature.clone());
                        }
                        if let Err(reason) = publish_clean_row(module, function) {
                            errors.push(format!(
                                "fatal clean-origin placement refusal for `{}` `{}`: {reason}. \
                                 The row was not published and was not demoted.",
                                record.shape, record.clean_name
                            ));
                            continue;
                        }
                        if let Some(published) = published {
                            summary.gated.push(GatedCleanRow { func_id: id, published });
                        }
                        summary.emitted.push(EmittedRow {
                            def_index: record.def_index,
                            def_path: record.def_path,
                            clean_name: record.clean_name,
                            shape: record.shape,
                            func_id: id.index(),
                            tier,
                            gate_subject_digest,
                            gate_carrier,
                            gate_method,
                            gate_environment_digest,
                            gate_kernel_version,
                            gate_ledger_digest,
                            tv_note,
                        });
                    }
                    Err(reason) => {
                        if targeted {
                            errors.push(format!(
                                "fatal clean-origin structural validation disagreement for \
                                 carrier-gated wrapping-binop `{}`: {reason}; the row was not \
                                 published and was not demoted",
                                record.clean_name
                            ));
                            continue;
                        }
                        summary.skipped.push((
                            record.def_index,
                            record.def_path,
                            record.clean_name,
                            record.shape,
                            format!(
                                "per-function validation refused the emitted trust-ir \
                                 spelling: {reason}. The row is skipped, never published \
                                 unvalidated. Options: report this (the emitter and the \
                                 validator disagree about well-formedness), or re-run with \
                                 the trust-ir validator's debug output to see the exact rule."
                            ),
                        ));
                    }
                }
            }
            CleanOriginIrOutcome::RustCalls(record) => {
                if duplicate_def_paths.contains(&record.def_path)
                    || duplicate_def_indices.contains(&record.def_index)
                {
                    continue;
                }
                if trust_clean_ir_gate::gate_targets(record.source.plan()) {
                    errors.push(format!(
                        "fatal clean-origin targeted Clean `{}` arrived as a pending Rust call \
                         plan; gate authority is never skipped or demoted",
                        record.clean_name
                    ));
                    continue;
                }
                match bind_rust_call_candidate(module, &record, rust_bodies, declarations) {
                    Ok((candidate, func_id, bindings)) => {
                        *module = candidate;
                        summary.pending_rust_calls.push(PendingRustCallSource {
                            def_index: record.def_index,
                            func_id,
                            link_symbol: record.link_symbol.clone(),
                            source: record.source.clone(),
                            bindings,
                        });
                        summary.emitted.push(EmittedRow {
                            def_index: record.def_index,
                            def_path: record.def_path,
                            clean_name: record.clean_name,
                            shape: "rust-call-chain",
                            func_id: func_id.index(),
                            tier: CleanOriginTier::Structural,
                            gate_subject_digest: None,
                            gate_carrier: None,
                            gate_method: None,
                            gate_environment_digest: None,
                            gate_kernel_version: None,
                            gate_ledger_digest: None,
                            tv_note: Some(
                                "not attempted: module-owned Rust calls are structurally \
                                 validated; no callee NoPanic, kernel-TV, or source-to-IR \
                                 refinement certificate is supplied"
                                    .into(),
                            ),
                        });
                    }
                    Err(reason) => summary.skipped.push((
                        record.def_index,
                        record.def_path,
                        record.clean_name,
                        "rust-call-chain",
                        format!(
                            "Rust call binding refused: {reason}. The plan was not appended. \
                             Options: supply the exact assembled Rust body and signature, or \
                             report a disagreement between collection and assembly."
                        ),
                    )),
                }
            }
            CleanOriginIrOutcome::Skipped(skip) => {
                if skip.gate_target {
                    errors.push(format!(
                        "fatal clean-origin targeted Clean `{}` `{}` arrived at append as a \
                         skip ({}) — targeted precursor/gate disagreements are never skipped, \
                         rerouted, or demoted",
                        skip.shape, skip.clean_name, skip.reason
                    ));
                    continue;
                }
                summary.skipped.push((
                    skip.def_index,
                    skip.def_path,
                    skip.clean_name,
                    skip.shape,
                    skip.reason,
                ));
            }
            CleanOriginIrOutcome::General(general) => {
                merge_general_module(module, general, &mut summary);
            }
        }
    }
    install_disclosure(module, &summary);
    summary
}

/// Bind against the complete actual module and stage the call body on a clone.
/// The batch transaction links exact declarations and validates the whole module
/// before publication. A declaration or guessed placeholder is never a Rust callee.
fn bind_rust_call_candidate(
    module: &Module,
    record: &CleanOriginRustCallRecord,
    rust_bodies: &[RustBodyIdentity],
    declarations: &[DeclarationLinkIdentity],
) -> Result<(Module, FuncId, Vec<trust_clean_ir_gate::rust_calls::RustCallBinding>), String> {
    let plan = record.source.plan();
    if !matches!(plan.shape(), trust_clean_origin::CleanOriginShape::RustCallChain { .. })
        || record.clean_name != plan.name()
        || record.def_path.is_empty()
    {
        return Err("the pending identity or shape disagrees with the sealed call plan".into());
    }
    if rust_bodies.iter().any(|body| body.def_index == record.def_index)
        || defined_row_claims(module, &record.link_symbol, &record.def_path)
    {
        return Err("an assembled Rust body already claims the pending Clean definition".into());
    }
    let mut targets = Vec::with_capacity(record.callees.len());
    for callee in &record.callees {
        let plan_callee = plan.callees().get(callee.plan_index).ok_or_else(|| {
            format!("callee index {} is outside the sealed roster", callee.plan_index)
        })?;
        if callee.plan_def_path != plan_callee.def_path
            || callee.clean_name != plan_callee.clean_name
            || callee.def_path.is_empty()
        {
            return Err(format!("callee {} has a mismatched plan-row identity", callee.plan_index));
        }
        let signature = trust_clean_ir::rust_callee_func_ty(plan_callee)
            .map_err(|refusal| format!("callee signature refused: {refusal:?}"))?;
        if signature != callee.signature {
            return Err(format!(
                "callee {} has a mismatched transported signature",
                callee.plan_index
            ));
        }
        let owners = rust_bodies
            .iter()
            .filter(|body| body.def_index == callee.def_index)
            .collect::<Vec<_>>();
        let [owner] = owners.as_slice() else {
            return Err(format!(
                "callee {} has {} assembled owners for DefIndex({})",
                callee.plan_index,
                owners.len(),
                callee.def_index
            ));
        };
        if owner.definition != callee.definition || owner.def_path != callee.def_path {
            return Err(format!(
                "callee {} has a mismatched assembled definition",
                callee.plan_index
            ));
        }
        if rust_bodies.iter().filter(|body| body.func_id == owner.func_id).count() != 1
            || rust_bodies.iter().filter(|body| body.definition == owner.definition).count() != 1
        {
            return Err(format!(
                "callee {} has an ambiguous module-owned identity",
                callee.plan_index
            ));
        }
        if owner.kind != crate::BodyKind::Fn || !owner.abi.is_plain_rust() {
            return Err(format!(
                "callee {} is not an assembled Rust ABI function",
                callee.plan_index
            ));
        }
        let function = module.functions.get(owner.func_id.index() as usize).ok_or_else(|| {
            format!("callee {} has no physical module function", callee.plan_index)
        })?;
        if function.id != owner.func_id
            || module.functions.iter().filter(|body| body.id == owner.func_id).count() != 1
            || function.is_declaration()
            || function.producer != Some(Producer::TRust)
            || function.calling_conv != trust_ir::CallingConv::Rust
        {
            return Err(format!(
                "callee {} is not a unique physical Rust producer",
                callee.plan_index
            ));
        }
        if module.func_types.get(function.ty.index() as usize) != Some(&signature) {
            return Err(format!(
                "callee {} has a mismatched actual module signature",
                callee.plan_index
            ));
        }
        targets.push(trust_clean_ir::RustCalleeTarget {
            plan_index: callee.plan_index,
            id: owner.func_id,
            signature,
        });
    }
    let signature = trust_clean_ir::trust_ir_func_ty(plan.signature())
        .map_err(|refusal| format!("caller signature refused: {refusal:?}"))?;
    let mut candidate = module.clone();
    // Trust (WS5.2): published in its Rust declaration's row when a Rust caller minted one.
    let slot = declaration_slot(module, declarations, record.def_index, &record.link_symbol)?;
    let id = match slot {
        Some(slot) => slot,
        None => FuncId::new(
            u32::try_from(candidate.functions.len()).map_err(|_| "function count exceeds u32")?,
        ),
    };
    let ty = intern_func_ty(&mut candidate, &signature);
    let mut function =
        trust_clean_ir::emit_clean_origin_rust_call_function(plan, id, ty, &targets)
            .map_err(|refusal| format!("sealed call emission refused: {refusal:?}"))?;
    crate::link_symbol::bind_clean_origin_link_symbol(&mut function, &record.link_symbol)?;
    if !function.attrs.is_empty()
        || !function.proofs.is_empty()
        || function.summary.is_some()
        || function.blocks.iter().flat_map(|block| &block.body).any(|node| {
            !node.proofs.is_empty()
                || node.proof_context.is_some()
                || (matches!(node.inst, Inst::Call { .. }) && !node.inst.has_side_effects())
        })
    {
        return Err(
            "the structural Rust call emitter supplied unsupported authority or effects".into()
        );
    }
    function.producer = Some(Producer::Clean);
    publish_clean_row(&mut candidate, function)?;
    let bindings = targets.iter().map(|target| trust_clean_ir_gate::rust_calls::RustCallBinding {
        plan_index: target.plan_index,
        function: target.id,
    }).collect();
    Ok((candidate, id, bindings))
}

/// Trust (WS5.2): does a DEFINED (body-bearing) row already claim the Clean definition of the
/// Rust item named `link_symbol`, displayed `def_path`?
///
/// Before WS5.2 both overlap guards compared `name == def_path`: a THIR body's name WAS its def
/// path, and an earlier Clean row's name was the spelling that is its `display_path` now. Both
/// spellings are kept — the link-time symbol (the def's identity: a second body of the SAME
/// item) and the display path (exactly the string the old guard compared) — so the guard
/// refuses everything it refused before, plus a same-symbol row whose display differs.
fn defined_row_claims(module: &Module, link_symbol: &str, def_path: &str) -> bool {
    module.functions.iter().any(|function| {
        !function.is_declaration()
            && (function.name == link_symbol || function.display_path.as_deref() == Some(def_path))
    })
}

/// Trust (WS5.2): the declaration row a Clean-origin definition is published IN, if any.
///
/// `Function.name` is the link-time symbol, and the Rust caller's `local-unlowered`
/// declaration of a Clean-origin item and the item's Clean definition carry ONE symbol — so the
/// definition takes the declaration's row instead of being appended beside it (which used to
/// leave an orphan the link pass renamed `<shadowed-by-clean-origin:…>`, a name that is no
/// symbol). Matching is by the exact same-crate source `DefIndex` (display paths are not linking
/// authority), and the matched row must be a bodyless declaration NAMED BY THE SAME SYMBOL — an
/// independent corroboration computed from the Rust side's own resolved instance.
///
/// `Ok(None)`: no Rust caller declared the item, so the definition is appended. `Err`: two
/// declaration rows claim one source identity (the assembly's symbol-collision refusal should
/// have removed their minting bodies), or the row is not a declaration of this symbol.
fn declaration_slot(
    module: &Module,
    declarations: &[DeclarationLinkIdentity],
    def_index: u32,
    link_symbol: &str,
) -> Result<Option<FuncId>, String> {
    let slots: Vec<&DeclarationLinkIdentity> = declarations
        .iter()
        .filter(|declaration| declaration.local_def_index == Some(def_index))
        .collect();
    let [slot] = slots.as_slice() else {
        return match slots.len() {
            0 => Ok(None),
            n => Err(format!(
                "{n} declaration rows claim source def_index {def_index}; one link-time symbol \
                 names one row, so the definition cannot choose between them"
            )),
        };
    };
    let rows: Vec<&Function> =
        module.functions.iter().filter(|function| function.id == slot.func_id).collect();
    match rows.as_slice() {
        [row] if row.is_declaration() && row.name == link_symbol => Ok(Some(slot.func_id)),
        [row] => Err(format!(
            "declaration FuncId({}) `{}` for source def_index {def_index} is {} named `{}`, but \
             the Clean definition's link-time symbol is `{link_symbol}`",
            slot.func_id.index(),
            slot.key,
            if row.is_declaration() { "a declaration" } else { "a BODY-BEARING row" },
            row.name,
        )),
        _ => Err(format!(
            "declaration FuncId({}) for source def_index {def_index} resolves to {} rows",
            slot.func_id.index(),
            rows.len()
        )),
    }
}

/// Trust (WS5.2): publish one Clean-origin row at its FINAL id — replacing the bodyless
/// declaration occupying that id ([`declaration_slot`]), or appended when the id is the next
/// dense one. Anything else is a producer defect the callers' placement already excludes; it is
/// still checked (and refused, never panicked on), so a stray id can never silently overwrite a
/// definition or punch a hole in the dense id space.
fn publish_clean_row(module: &mut Module, function: Function) -> Result<(), String> {
    let index = function.id.index() as usize;
    if index == module.functions.len() {
        module.functions.push(function);
        return Ok(());
    }
    match module.functions.get_mut(index) {
        Some(row) if row.is_declaration() && row.id == function.id && row.name == function.name => {
            *row = function;
            Ok(())
        }
        Some(row) => Err(format!(
            "clean-origin publication at FuncId({index}) would replace `{}`, which is not the \
             bodyless declaration of `{}`",
            row.name, function.name
        )),
        None => Err(format!(
            "clean-origin publication at FuncId({index}) is past the dense end ({})",
            module.functions.len()
        )),
    }
}

/// Merge the general lane's module into the crate Module (totality campaign).
///
/// Fail-closed at MODULE granularity: any un-remappable table content or
/// identity conflict refuses the WHOLE general module (every compiled row
/// demoted to `merge-refused`, disclosed) — a partial merge would break the
/// module-internal call graph. The per-decl rows always land in the summary.
fn merge_general_module(
    dst: &mut Module,
    general: GeneralCleanIr,
    summary: &mut CleanOriginJoinSummary,
) {
    // Rows first — they disclose regardless of the merge outcome.
    let mut compiled_names: Vec<(String, bool)> = Vec::new();
    for row in &general.rows {
        match &row.outcome {
            GeneralOutcome::Compiled { tv_mint_certified } => {
                compiled_names.push((row.clean_name.clone(), *tv_mint_certified));
            }
            GeneralOutcome::NotComputational => summary.general.push((
                row.clean_name.clone(),
                "not-computational",
                false,
                String::new(),
            )),
            GeneralOutcome::Skipped { reason } => {
                summary.general.push((row.clean_name.clone(), "skipped", false, reason.clone()))
            }
        }
    }
    let Some(mut src) = general.module else {
        for (name, _) in compiled_names {
            summary.general.push((
                name,
                "merge-refused",
                false,
                "the general module was withheld by the collector (batch refusal)".to_string(),
            ));
        }
        return;
    };
    let refuse =
        |summary: &mut CleanOriginJoinSummary, compiled: &[(String, bool)], reason: String| {
            for (name, _) in compiled {
                summary.general.push((name.clone(), "merge-refused", false, reason.clone()));
            }
        };

    // Claim-free precondition (the collector strips; this is the belt).
    if !src.proof_obligations.is_empty()
        || !src.proof_certificates.is_empty()
        || !src.obligation_diagnostics.is_empty()
        || src.functions.iter().any(|f| !f.proofs.is_empty() || f.summary.is_some())
    {
        refuse(
            summary,
            &compiled_names,
            "general module arrived with proof channels populated — the collector must strip them; refusing the merge keeps the published Module claim-free"
                .to_string(),
        );
        return;
    }
    // Target identity must agree exactly.
    if src.target_info != dst.target_info {
        refuse(
            summary,
            &compiled_names,
            format!(
                "target_info mismatch (general {:?} vs crate {:?}) — refusing rather than mixing ABIs in one artifact",
                src.target_info, dst.target_info
            ),
        );
        return;
    }
    // v1 refuses any table this merge does not remap. In practice the general
    // emitter boxes objects to thin pointers, so these are empty; a future
    // widening remaps them instead.
    // Trust (v1.2): `src.types` is REMAPPED now (equality-interned into `dst.types`, the
    // `func_types` discipline) — a `String`-valued island def (`clean_island_lexical_string`'s
    // `brace_text : String`) carries `Ty::Sequence(TyId)` in its signature, so the types
    // table is the ordinary spelling of sequences, not an exotic corner. The OTHER tables
    // stay refused: structs/enums/records/closure_types are nominal identities this merge
    // cannot equate, and spec/predicate/universe tables are claim-adjacent.
    if !src.structs.is_empty()
        || !src.enums.is_empty()
        || !src.records.is_empty()
        || !src.closure_types.is_empty()
        || !src.spec_modules.is_empty()
        || !src.predicates.is_empty()
        || !src.universes.is_empty()
        // trust-ir v55's drop-glue table keys glue FUNCTIONS by the type they drop; this
        // merge neither offsets those ids nor interns those types.
        || !src.drop_glue.is_empty()
        // trust-ir v58's closure-frame table keys a frame by its `ClosureTyId`, which this
        // merge does not remap (it refuses `closure_types` above for the same reason).
        || !src.closure_layouts.is_empty()
    {
        refuse(
            summary,
            &compiled_names,
            "general module carries type/spec/predicate tables this merge does not yet remap (v1 refuses rather than corrupting ids) — report which construct produced them"
                .to_string(),
        );
        return;
    }
    // Trust: trust-ir v70's content-addressed weight-blob table holds the bytes every
    // `Constant::TensorBlob` names by digest. This merge neither carries nor re-keys it, so
    // a joined module would keep the blob constants and lose their bytes. Refused by name.
    if !src.blobs.is_empty() {
        refuse(
            summary,
            &compiled_names,
            format!(
                "general module carries a trust-ir v70 tensor weight-blob table ({} row(s)), \
                 which the Clean-origin join does not carry: every Constant::TensorBlob in \
                 the joined module would name bytes it lacks",
                src.blobs.len()
            ),
        );
        return;
    }
    // Physical IDs are keys, not vector positions. Refuse duplicate, colliding,
    // or overflowing projected IDs before interning any destination type.
    let (func_offset, global_offset) = match checked_ids::validate_join(dst, &src) {
        Ok(offsets) => offsets,
        Err(reason) => {
            refuse(summary, &compiled_names, reason);
            return;
        }
    };
    // Name-identity guard. Trust (WS5.2): ANY general row — declaration or definition — whose
    // name an existing row already holds refuses the WHOLE general module (partial merges break
    // internal calls). General rows keep clean-compiler's own symbols; they are never link
    // targets (IR-5 links planner rows only), and every other row is now named by its Rust
    // link-time symbol, so a clash is a genuine symbol collision, not the display-name overlap
    // the retired `general::` rename used to paper over. That rename (measured 2026-08-30:
    // every Nat-recursion def's general spelling met the Rust item's `local-unlowered`
    // declaration, then named by its def path) minted `general::<name>`, which is no symbol
    // at all; a collision is refused instead of renamed.
    let renamed: Vec<(String, String)> = Vec::new();
    {
        let existing: std::collections::BTreeSet<String> =
            dst.functions.iter().map(|f| f.name.clone()).collect();
        if let Some(clash) = src.functions.iter().find(|f| existing.contains(&f.name)) {
            refuse(
                summary,
                &compiled_names,
                format!(
                    "general {} `{}` collides with an existing module row's link-time symbol — refusing the whole general module",
                    if clash.is_declaration() { "declaration" } else { "function" },
                    clash.name
                ),
            );
            return;
        }
    }

    // Id remaps: FuncId by offset, FuncTyId by equality-interning, GlobalId by
    // append offset. Spans/scopes are STRIPPED (v1): their file ids index the
    // general module's own file table, which this merge does not carry.
    // Function-type interning with RECURSIVE Ty::Func remapping (v1.1): a
    // higher-order signature (clean-compiler's apply/closure runtime spells
    // callables as Ty::Func(src-relative id)) is remapped id-by-id into the
    // destination table. Table-referencing variants other than Func
    // (Struct/Enum/Record/Closure/Array/Set/Sequence/Refine) cannot appear
    // here — the empty-tables belt above already refused any module that
    // could give their ids a referent — but the walk still names one on
    // sight rather than trusting that argument twice.
    let mut functy_map: Vec<FuncTyId> = Vec::with_capacity(src.func_types.len());
    let mut types_map: Vec<TyId> = Vec::with_capacity(src.types.len());
    {
        let mut cx = GeneralTyRemap {
            src_func_types: &src.func_types,
            src_types: &src.types,
            func_memo: vec![None; src.func_types.len()],
            func_in_progress: vec![false; src.func_types.len()],
            ty_memo: vec![None; src.types.len()],
            ty_in_progress: vec![false; src.types.len()],
        };
        let mut failure: Option<String> = None;
        for index in 0..src.func_types.len() {
            match remap_func_ty_id(index, &mut cx, dst) {
                Ok(id) => functy_map.push(id),
                Err(reason) => {
                    failure = Some(reason);
                    break;
                }
            }
        }
        if failure.is_none() {
            for index in 0..src.types.len() {
                match remap_ty_table_id(index, &mut cx, dst) {
                    Ok(id) => types_map.push(id),
                    Err(reason) => {
                        failure = Some(reason);
                        break;
                    }
                }
            }
        }
        if let Some(reason) = failure {
            refuse(summary, &compiled_names, reason);
            return;
        }
    }
    // BODY belt (v1.1): the signature remap above rewrites Ty::Func ids in
    // the func_types table, but an instruction or block param can embed a
    // Func-typed VALUE whose id this merge does not walk (the Inst grammar
    // has dozens of Ty fields). Rather than silently retyping a value with a
    // src-relative id, refuse the batch on sight. The Debug rendering is the
    // one complete traversal of every embedded field the format guarantees;
    // "Func(" cannot occur in a Clean identifier, so the scan cannot
    // false-positive on names. Higher-order value flow through an island body
    // is therefore v1-refused, never mis-merged; signatures alone carry the
    // runtime's callable spellings for first-order defs.
    // Trust (v1.1): types EMBEDDED in general bodies are remapped, not refused. The v1 belt
    // ("a Func-typed value flowing through a BODY is refused rather than silently retyped")
    // stopped the closure-based recursion defs (`countdownSum`, `addAcc` — the ExternCalls
    // runtime allocates closures, so `Ty::Func` values flow through their bodies) at
    // merge-refused and held the Lean side at 88.9% on the Clean corpus. The walk the belt
    // said was missing is here now, and it is EXHAUSTIVE BY CONSTRUCTION: `remap_general_ty`
    // matches every `Ty` variant and `remap_general_inst_tys` every `Inst` variant with no
    // catch-all arm, so a new variant is a compile error, never a silent skip. Fallible work
    // (a `Ty::Func` outside the general table; any TABLE-INDEXED type — `Struct`, `Enum`,
    // `Array`, `FatPtr(Slice)`, `Set`, `Sequence`, `Record`, `Closure`, `Refine` — whose id
    // could only dangle, since the src tables were refused non-empty above) runs in THIS
    // pre-pass over `src`, before `dst` is touched, so a refusal still merges nothing.
    {
        let mut failure: Option<String> = None;
        'funcs: for function in src.functions.iter_mut() {
            for block in &mut function.blocks {
                for (_, ty) in &mut block.params {
                    if let Err(reason) = remap_general_ty(ty, &functy_map, &types_map) {
                        failure = Some(format!("general `{}`: {reason}", function.name));
                        break 'funcs;
                    }
                }
                for node in &mut block.body {
                    if let Err(reason) =
                        remap_general_inst_tys(&mut node.inst, &functy_map, &types_map)
                    {
                        failure = Some(format!("general `{}`: {reason}", function.name));
                        break 'funcs;
                    }
                }
            }
        }
        if let Some(reason) = failure {
            refuse(summary, &compiled_names, reason);
            return;
        }
    }
    // Global initializer function identities and their types use the same
    // source tables as body constants. Keep both halves of that binding.
    for global in &mut src.globals {
        if let Err(reason) = remap_general_ty(&mut global.ty, &functy_map, &types_map) {
            refuse(summary, &compiled_names, format!("general global `{}`: {reason}", global.name));
            return;
        }
        // Trust: an initializer is a constant, so it gets the body's v70 blob check.
        if let Some(reason) =
            global.initializer.as_ref().and_then(general_const_tensor_blob_refusal)
        {
            refuse(summary, &compiled_names, format!("general global `{}`: {reason}", global.name));
            return;
        }
    }
    if let Err(reason) = crate::tuple_layout::merge(&src, dst, |ty| {
        let mut mapped = ty.clone();
        remap_general_ty(&mut mapped, &functy_map, &types_map).ok()?;
        Some(mapped)
    }) {
        refuse(summary, &compiled_names, reason);
        return;
    }
    for mut global in src.globals.drain(..) {
        if let Some(value) = &mut global.initializer {
            remap_general_const(value, func_offset);
        }
        dst.globals.push(global);
    }
    let defined: Vec<String> =
        src.functions.iter().filter(|f| !f.is_declaration()).map(|f| f.name.clone()).collect();
    for mut function in src.functions.drain(..) {
        function.id = FuncId::new(func_offset + function.id.index());
        function.ty = functy_map[function.ty.index() as usize];
        function.producer = Some(Producer::Clean);
        function.source_provenance = None;
        function.scopes = None;
        for block in &mut function.blocks {
            for node in &mut block.body {
                node.span = None;
                match &mut node.inst {
                    Inst::Call { callee, .. } | Inst::Invoke { callee, .. } => {
                        *callee = FuncId::new(func_offset + callee.index());
                    }
                    Inst::SeqMap { fwd, .. } => {
                        *fwd = FuncId::new(func_offset + fwd.index());
                    }
                    Inst::CallIndirect { sig, .. } => {
                        *sig = functy_map[sig.index() as usize];
                    }
                    Inst::Const { value, .. } => {
                        remap_general_const(value, func_offset);
                    }
                    Inst::Switch { cases, .. } => {
                        for case in cases.iter_mut() {
                            remap_general_const(&mut case.value, func_offset);
                        }
                    }
                    Inst::GlobalAddr { global } => {
                        *global = trust_ir::value::GlobalId::new(global_offset + global.index());
                    }
                    _ => {}
                }
            }
        }
        dst.functions.push(function);
    }
    summary.general_functions = defined;
    // Trust (WS5.2): nothing is renamed any more (a collision refused the module above), so
    // `general_renamed` stays empty and no compiled row carries a `recorded as` reason.
    summary.general_renamed = renamed;
    for (name, tv) in compiled_names {
        summary.general.push((name, "compiled", tv, String::new()));
    }
}

/// Remap one src-relative `FuncTyId` into `dst`'s table, remapping every
/// embedded `Ty::Func` id recursively (memoized; a self-referential signature
/// refuses — it could only arise from a corrupted table and has no finite
/// spelling).
/// Trust (v1.1): remap a `Ty` embedded in a general-lane BODY onto the destination module's
/// tables. `Ty::Func` goes through the equality-interned `functy_map`; a table-indexed type
/// (`Struct`, `Enum`, `Array`, `FatPtr(Slice)`, `Set`, `Sequence`, `Record`, `Closure`,
/// `Refine`) is refused — the general module's own tables were refused non-empty before this
/// runs, so such an id could only dangle. EXHAUSTIVE match, no catch-all: a new `Ty` variant
/// is a compile error here, never a silent skip.
fn remap_general_ty(
    ty: &mut trust_ir::ty::Ty,
    functy_map: &[FuncTyId],
    types_map: &[TyId],
) -> Result<(), String> {
    use trust_ir::ty::{FatPtrKind, Ty};
    fn remap_tid(id: &mut TyId, types_map: &[TyId]) -> Result<(), String> {
        match types_map.get(id.index() as usize) {
            Some(mapped) => {
                *id = *mapped;
                Ok(())
            }
            None => Err(format!(
                "general body type id types[{}] indexes outside the general types table",
                id.index()
            )),
        }
    }
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
        | Ty::Char
        | Ty::Error
        | Ty::F16
        | Ty::F32
        | Ty::F64
        | Ty::Bool
        | Ty::Ptr
        | Ty::Unit
        | Ty::Never
        // Geometry has no table references to remap and is not a value token.
        | Ty::Storage(_) => Ok(()),
        // Level R (trust-ir amendment S): a module type has no extension.
        Ty::Ext(e) => e.unreachable(),
        Ty::FatPtr(kind) => match kind {
            FatPtrKind::Slice(id) => remap_tid(id, types_map),
            _ => Ok(()),
        },
        Ty::Vector(inner, _)
        | Ty::Ref(inner)
        | Ty::RefMut(inner)
        | Ty::PtrConst(inner)
        | Ty::PtrMut(inner)
        | Ty::Rc(inner) => remap_general_ty(inner, functy_map, types_map),
        Ty::Tuple(elems) => {
            for e in elems.iter_mut() {
                remap_general_ty(e, functy_map, types_map)?;
            }
            Ok(())
        }
        Ty::Func(id) => match functy_map.get(id.index() as usize) {
            Some(mapped) => {
                *id = *mapped;
                Ok(())
            }
            None => Err(format!(
                "general body type Ty::Func({}) indexes outside the general func_types table",
                id.index()
            )),
        },
        Ty::Array(id, _) | Ty::Sequence(id) | Ty::Set(id, _) => remap_tid(id, types_map),
        Ty::Struct(_) | Ty::Enum(_) | Ty::Record(_) | Ty::Closure(_) | Ty::Refine(..) => {
            Err(format!(
                "general body type {ty:?} indexes a table the general module was refused for carrying"
            ))
        }
        // Trust: trust-ir v43 nominal opaque runtime handles. Nothing here to remap
        // either (the identity is `(name, runtime)`, not a table index), and the reason
        // to refuse is SHARPER than the dialect one. A handle's ONLY legal origins are
        // its runtime's pinned entry-point DECLARATIONS, and this join re-mints every
        // `FuncId` and rewrites the edges. Carrying a handle-typed body without also
        // carrying those declarations and re-pointing its call edges at them yields a
        // joined module whose handle has no pinned origin — `validate_module` refuses it
        // (`HandleForeignDeclaration`), and an unrewritten edge resolves to whichever
        // function happens to hold the index. Refusing costs no capability today: the
        // Clean-origin producer mints a handle only through
        // `trust_clean_ir::declare_pinned_nat_runtime`, which this seam does not call.
        Ty::Handle(handle) => Err(format!(
            "general body type Ty::Handle({}, {}) is not admitted by the Clean-origin join: \
             a handle's only origins are its runtime's pinned entry-point declarations, and \
             this join re-mints function ids without carrying them. Carry the pinned \
             declarations through the join and re-point the call edges at them, or emit \
             this declaration at a carrier that needs no runtime",
            handle.name, handle.runtime
        )),
        // Trust: trust-ir d1f4a2f nominal dialect types. Nothing here to remap (the
        // identity is namespace/name/version, not a table index), but the Clean-origin
        // producer has never minted one and no consumer of the joined module has an
        // admission schema for it, so admit-by-no-op would smuggle an uninterpreted
        // type past every downstream gate. Refuse, naming the fix.
        Ty::Dialect(dialect) => Err(format!(
            "general body type Ty::Dialect({}::{} v{}) is not admitted by the Clean-origin \
             join: legalize the dialect type to a Core carrier in the producer, or extend \
             the join with a checked admission schema for this dialect",
            dialect.namespace, dialect.name, dialect.version
        )),
        // Trust: trust-ir v67's tensor carrier. Nothing here to remap (its element is a
        // scalar), but the Clean-origin producer never mints one and no consumer of the
        // joined module has a layout for it, so admit-by-no-op would carry an
        // uninterpreted run-time-shaped value past every downstream gate. Refused by name.
        Ty::Tensor(_, rank) => Err(format!(
            "general body type Ty::Tensor(rank {rank}) is not admitted by the Clean-origin \
             join: no Clean-origin producer mints a trust-ir v67 tensor and no consumer of \
             the joined module has a layout for one"
        )),
    }
}
/// Trust (v1.1): remap every `Ty` field of one instruction. EXHAUSTIVE over the `Inst`
/// grammar with no catch-all arm — a new variant is a compile error, which is the belt the
/// v1 Debug-render scan approximated. `FuncId` / `GlobalId` / `Constant` rewrites stay in the
/// (infallible) drain loop; this pass is the fallible half and runs before `dst` is touched.
fn remap_general_inst_tys(
    inst: &mut Inst,
    functy_map: &[FuncTyId],
    types_map: &[TyId],
) -> Result<(), String> {
    match inst {
        // Runtime closure construction names both a ClosureTyId and a FuncId.
        // This join does not remap closure tables or constructor targets, so
        // refuse before the infallible drain can publish source-relative ids.
        Inst::MakeClosure { .. } => Err(
            "general body carries MakeClosure — its closure type and target are outside the general remap"
                .to_string(),
        ),
        // trust-ir WS3.5 `Inst::MakeAggregate` carries the aggregate type it
        // builds — one embedded `ty`, remapped like every other.
        Inst::MakeAggregate { ty, .. }
        // v50 `Inst::ArraySplat` carries its `Array(e, n)` type the same way; its one
        // operand is a function-local register.
        | Inst::ArraySplat { ty, .. }
        // v47 `Inst::Drop` names the dropped place's type.
        | Inst::Drop { ty, .. }
        | Inst::BinOp { ty, .. }
        | Inst::UnOp { ty, .. }
        | Inst::Overflow { ty, .. }
        | Inst::ICmp { ty, .. }
        | Inst::FCmp { ty, .. }
        | Inst::Load { ty, .. }
        | Inst::Store { ty, .. }
        | Inst::Alloca { ty, .. }
        | Inst::HeapAlloc { ty, .. }
        | Inst::AtomicLoad { ty, .. }
        | Inst::AtomicStore { ty, .. }
        | Inst::AtomicRMW { ty, .. }
        | Inst::CmpXchg { ty, .. }
        | Inst::ExtractField { ty, .. }
        | Inst::InsertField { ty, .. }
        | Inst::ExtractElement { ty, .. }
        | Inst::InsertElement { ty, .. }
        | Inst::Undef { ty }
        | Inst::Copy { ty, .. }
        | Inst::Select { ty, .. }
        | Inst::SeqMapAddK { ty, .. }
        | Inst::SeqMapNot { ty, .. }
        | Inst::SeqMap { ty, .. }
        | Inst::LoadSlot { ty, .. } => remap_general_ty(ty, functy_map, types_map),
        // Trust: a constant is also checked for a trust-ir v70 `Constant::TensorBlob`, at
        // any depth, before its type is remapped (see `general_const_tensor_blob_refusal`).
        Inst::Const { ty, value } => match general_const_tensor_blob_refusal(value) {
            Some(refusal) => Err(refusal),
            None => remap_general_ty(ty, functy_map, types_map),
        },
        Inst::GEP { pointee_ty, .. } => remap_general_ty(pointee_ty, functy_map, types_map),
        Inst::PtrData { ptr_ty, .. } => remap_general_ty(ptr_ty, functy_map, types_map),
        Inst::PtrMetadata { ptr_ty, metadata_ty, .. }
        | Inst::PtrFromParts { ptr_ty, metadata_ty, .. } => {
            remap_general_ty(ptr_ty, functy_map, types_map)?;
            remap_general_ty(metadata_ty, functy_map, types_map)
        }
        Inst::Cast { src_ty, dst_ty, .. } => {
            remap_general_ty(src_ty, functy_map, types_map)?;
            remap_general_ty(dst_ty, functy_map, types_map)
        }
        Inst::OpenFrame { def } => {
            for slot in def.slots.iter_mut() {
                remap_general_ty(&mut slot.ty, functy_map, types_map)?;
            }
            Ok(())
        }
        // Bulk memory carries only function-local SSA operands and the copy-overlap
        // policy, not module-relative types. Preserve all of them in this type-only pass.
        Inst::MemCopy { dst: _, src: _, bytes: _, overlap: _ }
        | Inst::MemSet { dst: _, byte: _, bytes: _ } => Ok(()),
        // Trust: a case value is a constant too, so it gets the same v70 blob check.
        Inst::Switch { cases, .. } => {
            match cases.iter().find_map(|case| general_const_tensor_blob_refusal(&case.value)) {
                Some(refusal) => Err(refusal),
                None => Ok(()),
            }
        }
        Inst::Fence { .. }
        | Inst::Br { .. }
        | Inst::CondBr { .. }
        | Inst::Call { .. }
        | Inst::CallIndirect { .. }
        | Inst::Invoke { .. }
        | Inst::Return { .. }
        | Inst::NullPtr
        | Inst::GlobalAddr { .. }
        | Inst::Assume { .. }
        // A siteless assert's kind operands (trust-ir v52) are function-local registers.
        | Inst::Assert { site: None, .. }
        | Inst::Unreachable
        | Inst::Borrow { .. }
        | Inst::BorrowMut { .. }
        | Inst::EndBorrow { .. }
        | Inst::Retain { .. }
        | Inst::Release { .. }
        | Inst::IsUnique { .. }
        | Inst::Dealloc { .. }
        | Inst::BindSlot { .. }
        | Inst::CloseFrame { .. }
        | Inst::CoroSuspend { .. }
        | Inst::LandingPad { .. }
        | Inst::Resume { .. } => Ok(()),
        // A sited assert (trust-ir v54) names its panic entry (a `FuncId`) and possibly a
        // location global (a `GlobalId`); the unwinding and no-unwind twins (v53/v55/v56)
        // name a callee, a signature or a drop type. The drain loop below offsets only the
        // ids of the shapes it lists, so none of these is merged with a src-relative id:
        // each refuses the batch by name.
        Inst::Assert { site: Some(_), .. } => {
            Err("general body carries a sited Assert — its panic entry and location are \
                 outside the v1.1 remap"
                .to_string())
        }
        Inst::AssertInvoke { .. }
        | Inst::CallCannotUnwind { .. }
        | Inst::CallIndirectCannotUnwind { .. }
        | Inst::DropInvoke { .. }
        | Inst::InvokeIndirect { .. } => Err(format!(
            "general body carries {} — its callee, signature or drop type is outside the \
             v1.1 remap",
            general_inst_name(inst)
        )),
        // A dialect op's payload is opaque to this walk; nothing the ExternCalls pipeline
        // emits, so refuse rather than guess at what its embedded types index.
        Inst::DialectOp(_) => {
            Err("general body carries a DialectOp — its embedded types are outside the v1.1 remap"
                .to_string())
        }
        // Trust: trust-ir v67-v69's six tensor instructions. Each one computes over a
        // run-time-shaped tensor value (element arithmetic, folds, index expressions, or
        // reads and writes at run-time coordinates) that no Clean-origin producer emits
        // and no consumer of the joined module lowers. Refused by name, never remapped.
        Inst::TensorContract { .. }
        | Inst::TensorMap { .. }
        | Inst::TensorReduce { .. }
        | Inst::TensorView { .. }
        | Inst::TensorGather { .. }
        | Inst::TensorScatter { .. } => Err(format!(
            "general body carries {} — a trust-ir v67-v69 tensor instruction the Clean-origin \
             join does not admit",
            general_inst_name(inst)
        )),
    }
}
/// The name of an instruction [`remap_general_inst_tys`] refuses by variant.
fn general_inst_name(inst: &Inst) -> &'static str {
    match inst {
        Inst::AssertInvoke { .. } => "an AssertInvoke",
        Inst::CallCannotUnwind { .. } => "a CallCannotUnwind",
        Inst::CallIndirectCannotUnwind { .. } => "a CallIndirectCannotUnwind",
        Inst::DropInvoke { .. } => "a DropInvoke",
        Inst::InvokeIndirect { .. } => "an InvokeIndirect",
        Inst::TensorContract { .. } => "a TensorContract",
        Inst::TensorMap { .. } => "a TensorMap",
        Inst::TensorReduce { .. } => "a TensorReduce",
        Inst::TensorView { .. } => "a TensorView",
        Inst::TensorGather { .. } => "a TensorGather",
        Inst::TensorScatter { .. } => "a TensorScatter",
        _ => "an instruction",
    }
}
/// Trust: the refusal of a trust-ir v70 `Constant::TensorBlob` anywhere in `value` (the root
/// or any child), or `None`. A blob constant names its bytes by digest in the module's blob
/// table, which this join refuses non-empty, so here it could only dangle. This is the
/// fallible half for constants: [`remap_general_const`] is infallible and runs after it.
fn general_const_tensor_blob_refusal(value: &Constant) -> Option<String> {
    let mut blob = None;
    value.visit_constants(|c| {
        if let Constant::TensorBlob { digest, dims } = c {
            if blob.is_none() {
                blob = Some(format!(
                    "general constant carries Constant::TensorBlob({digest}, dims {dims:?}), \
                     a trust-ir v70 tensor weight the Clean-origin join does not admit: it \
                     names bytes in a blob table the join does not carry"
                ));
            }
        }
    });
    blob
}
/// Trust (v1.1): rewrite the `FuncId`s a CONSTANT can carry (`FnDef`, `Closure { func }`)
/// by the append offset, recursing through the aggregate constants. Every target
/// and projected offset was checked before destination interning or draining.
fn remap_general_const(value: &mut Constant, func_offset: u32) {
    match value {
        Constant::FnDef(id) => *id = FuncId::new(func_offset + id.index()),
        Constant::Closure { func, captures } => {
            *func = FuncId::new(func_offset + func.index());
            for c in captures.iter_mut() {
                remap_general_const(c, func_offset);
            }
        }
        Constant::Aggregate(items)
        | Constant::Array(items)
        | Constant::Vector(items)
        | Constant::Sequence(items)
        | Constant::Set(items) => {
            for c in items.iter_mut() {
                remap_general_const(c, func_offset);
            }
        }
        Constant::Record(fields) => {
            for (_, c) in fields.iter_mut() {
                remap_general_const(c, func_offset);
            }
        }
        // v50 uniform array: its ONE element carries whatever `FuncId`s every lane
        // carries, so remapping it once remaps all `len` lanes (never walks `len`).
        Constant::Splat { elem, .. } => remap_general_const(elem, func_offset),
        Constant::Int(_)
        | Constant::U128(_)
        | Constant::Bytes { .. }
        | Constant::Float(_)
        | Constant::Bool(_)
        | Constant::SymbolAddr { .. }
        | Constant::PhantomData
        // v49: an unwritten lane carries no function identity.
        | Constant::Uninit
        // Trust: a v70 blob names bytes by digest and carries no function identity. Every
        // one was refused before the drain (`general_const_tensor_blob_refusal`).
        | Constant::TensorBlob { .. } => {}
        // Level R (trust-ir amendment S): a module constant has no extension.
        Constant::Ext(e) => e.unreachable(),
    }
}
/// Trust (v1.1/v1.2): the shared remap state for a general module's SIGNATURE-side types —
/// `func_types` and `types` interned into the destination by structural equality, mutually
/// recursive (a signature may carry `Ty::Func`, a func type may carry `Ty::Sequence`, a types
/// entry may carry either), each with its own memo and cycle refusal.
struct GeneralTyRemap<'a> {
    src_func_types: &'a [FuncTy],
    src_types: &'a [trust_ir::ty::Ty],
    func_memo: Vec<Option<FuncTyId>>,
    func_in_progress: Vec<bool>,
    ty_memo: Vec<Option<TyId>>,
    ty_in_progress: Vec<bool>,
}
fn remap_func_ty_id(
    index: usize,
    cx: &mut GeneralTyRemap<'_>,
    dst: &mut Module,
) -> Result<FuncTyId, String> {
    if let Some(id) = cx.func_memo[index] {
        return Ok(id);
    }
    if cx.func_in_progress[index] {
        return Err(format!(
            "general func_types[{index}] is self-referential through Ty::Func — refusing \
             (no finite signature spelling exists)"
        ));
    }
    cx.func_in_progress[index] = true;
    let src_ty = cx.src_func_types[index].clone();
    let mut remapped = FuncTy {
        params: Vec::with_capacity(src_ty.params.len()),
        returns: Vec::with_capacity(src_ty.returns.len()),
        is_vararg: src_ty.is_vararg,
        // trust-ir v60: the ABI record names no table id, so the remap carries it unchanged.
        abi: src_ty.abi.clone(),
    };
    for ty in &src_ty.params {
        remapped.params.push(remap_ty(ty, cx, dst)?);
    }
    for ty in &src_ty.returns {
        remapped.returns.push(remap_ty(ty, cx, dst)?);
    }
    cx.func_in_progress[index] = false;
    let id = intern_func_ty(dst, &remapped);
    cx.func_memo[index] = Some(id);
    Ok(id)
}
/// Trust (v1.2): intern one `types`-table entry, remapping what it references first.
fn remap_ty_table_id(
    index: usize,
    cx: &mut GeneralTyRemap<'_>,
    dst: &mut Module,
) -> Result<TyId, String> {
    if let Some(id) = cx.ty_memo[index] {
        return Ok(id);
    }
    if cx.ty_in_progress[index] {
        return Err(format!(
            "general types[{index}] is self-referential — refusing (no finite spelling exists)"
        ));
    }
    cx.ty_in_progress[index] = true;
    let src_ty = cx.src_types[index].clone();
    let remapped = remap_ty(&src_ty, cx, dst)?;
    cx.ty_in_progress[index] = false;
    let id = intern_type(dst, &remapped);
    cx.ty_memo[index] = Some(id);
    Ok(id)
}
fn remap_table_tid(
    id: &TyId,
    cx: &mut GeneralTyRemap<'_>,
    dst: &mut Module,
) -> Result<TyId, String> {
    let index = id.index() as usize;
    if index >= cx.src_types.len() {
        return Err(format!(
            "general signature references types[{index}] which the module does not define — \
             refusing a dangling id"
        ));
    }
    remap_ty_table_id(index, cx, dst)
}
fn remap_ty(
    ty: &trust_ir::ty::Ty,
    cx: &mut GeneralTyRemap<'_>,
    dst: &mut Module,
) -> Result<trust_ir::ty::Ty, String> {
    use trust_ir::ty::{FatPtrKind, Ty};
    Ok(match ty {
        Ty::Func(id) => {
            let index = id.index() as usize;
            if index >= cx.src_func_types.len() {
                return Err(format!(
                    "general signature references func_types[{index}] which the module does not \
                     define — refusing a dangling id"
                ));
            }
            Ty::Func(remap_func_ty_id(index, cx, dst)?)
        }
        Ty::Vector(inner, lanes) => Ty::Vector(Box::new(remap_ty(inner, cx, dst)?), *lanes),
        Ty::Tuple(elems) => {
            Ty::Tuple(elems.iter().map(|e| remap_ty(e, cx, dst)).collect::<Result<Vec<_>, _>>()?)
        }
        Ty::Ref(inner) => Ty::Ref(Box::new(remap_ty(inner, cx, dst)?)),
        Ty::RefMut(inner) => Ty::RefMut(Box::new(remap_ty(inner, cx, dst)?)),
        Ty::PtrConst(inner) => Ty::PtrConst(Box::new(remap_ty(inner, cx, dst)?)),
        Ty::PtrMut(inner) => Ty::PtrMut(Box::new(remap_ty(inner, cx, dst)?)),
        Ty::Rc(inner) => Ty::Rc(Box::new(remap_ty(inner, cx, dst)?)),
        // Trust (v1.2): the sequence-shaped table references remap through the interned
        // types table — `String` is `Sequence(TyId)`, the ordinary spelling.
        Ty::Array(id, len) => Ty::Array(remap_table_tid(id, cx, dst)?, *len),
        Ty::Sequence(id) => Ty::Sequence(remap_table_tid(id, cx, dst)?),
        Ty::Set(id, repr) => Ty::Set(remap_table_tid(id, cx, dst)?, *repr),
        Ty::FatPtr(FatPtrKind::Slice(id)) => {
            Ty::FatPtr(FatPtrKind::Slice(remap_table_tid(id, cx, dst)?))
        }
        Ty::Struct(_) | Ty::Enum(_) | Ty::Record(_) | Ty::Closure(_) | Ty::Refine(..) => {
            return Err(format!(
                "general signature carries a table-referencing type ({ty:?}) whose table \
                 the merge refuses to carry"
            ));
        }
        // Trust: same refusal as `remap_general_ty`, and for the same reason this lane
        // needs its own arm — it runs FIRST, so without one a Handle-typed param, return
        // or `types[i]` entry would be cloned into `dst` by the catch-all below and the
        // body-side refusal would never see it. That is the exact shape of the
        // admit-by-no-op smuggle: a handle carries no table index, so the catch-all is
        // CORRECT about remapping and silent about admission.
        Ty::Handle(handle) => {
            return Err(format!(
                "general signature carries Ty::Handle({}, {}), which the Clean-origin join \
                 does not admit: a handle's only origins are its runtime's pinned \
                 entry-point declarations, and this join re-mints function ids without \
                 carrying them. Carry the pinned declarations through the join and re-point \
                 the call edges at them, or emit this declaration at a carrier that needs \
                 no runtime",
                handle.name, handle.runtime
            ));
        }
        // Trust: same refusal as `remap_general_ty` — this lane runs FIRST (signatures and
        // the interned types table are remapped before the body pre-pass), so without this
        // arm a Dialect-typed param, return, or `types[i]` entry would be cloned into `dst`
        // by the catch-all below, and the body-side refusal would never see it.
        Ty::Dialect(dialect) => {
            return Err(format!(
                "general signature carries Ty::Dialect({}::{} v{}), which the Clean-origin \
                 join does not admit: legalize the dialect type to a Core carrier in the \
                 producer, or extend the join with a checked admission schema for this dialect",
                dialect.namespace, dialect.name, dialect.version
            ));
        }
        // Trust: same refusal as `remap_general_ty`'s trust-ir v67 tensor arm. This lane
        // runs FIRST, so without it a tensor-typed param, return or `types[i]` entry would
        // be interned into `dst` by the catch-all below, and a declaration (no body for the
        // body pre-pass to read) would carry it through the join.
        Ty::Tensor(_, rank) => {
            return Err(format!(
                "general signature carries Ty::Tensor(rank {rank}), which the Clean-origin \
                 join does not admit: no Clean-origin producer mints a trust-ir v67 tensor \
                 and no consumer of the joined module has a layout for one"
            ));
        }
        other => other.clone(),
    })
}
pub fn link_clean_origin_edges(
    before: &Module,
    module: &mut Module,
    declarations: &[DeclarationLinkIdentity],
    summary: &mut CleanOriginJoinSummary,
    errors: &mut Vec<String>,
) {
    if summary.emitted.is_empty() {
        return;
    }
    // The match map: declaration FuncId -> appended definition FuncId. The
    // `local-unlowered:{def_path}` key (which may carry `|ret:`/`|nres:` split
    // suffixes) supplies corroborating display identity only. The shared
    // same-crate DefIndex is authority: display paths are deterministic but
    // not injective, so a unique path match is insufficient.
    let mut matches: Vec<(FuncId, String, u32, u32, String)> = Vec::new();
    for declaration in declarations {
        let key = &declaration.key;
        let Some(rest) = key.strip_prefix("local-unlowered:") else { continue };
        let base = rest.split('|').next().unwrap_or(rest);
        let path_candidates: Vec<&EmittedRow> =
            summary.emitted.iter().filter(|row| row.def_path == base).collect();
        let Some(source_def_index) = declaration.local_def_index else {
            errors.push(format!(
                "clean-origin link refused: local-unlowered declaration key `{key}` has no exact \
                 source def_index; display identity is not linking authority"
            ));
            return;
        };
        let candidates: Vec<&EmittedRow> =
            summary.emitted.iter().filter(|row| row.def_index == source_def_index).collect();
        match candidates.as_slice() {
            [] if path_candidates.is_empty() => {}
            [] => {
                let candidate_indices = path_candidates
                    .iter()
                    .map(|row| row.def_index.to_string())
                    .collect::<Vec<_>>()
                    .join(", ");
                errors.push(format!(
                    "clean-origin link refused: source identity mismatch for declaration key \
                     `{key}`: expected def_index {source_def_index}, but same display path \
                     `{base}` belongs to emitted def_index candidate(s) [{candidate_indices}]; \
                     no edge was rewritten"
                ));
                return;
            }
            [row] => {
                if row.def_path != base {
                    errors.push(format!(
                        "clean-origin link refused: display identity mismatch for declaration \
                         key `{key}` and exact source def_index {source_def_index}: declaration \
                         path `{base}` differs from emitted path `{}`; no edge was rewritten",
                        row.def_path
                    ));
                    return;
                }
                if path_candidates.len() != 1 {
                    errors.push(format!(
                        "clean-origin link refused: declaration key `{key}` and exact source \
                         def_index {source_def_index} share display path `{base}` with {} emitted \
                         rows — duplicate display identity among Clean-origin rows",
                        path_candidates.len()
                    ));
                    return;
                }
                matches.push((
                    declaration.func_id,
                    key.clone(),
                    source_def_index,
                    row.func_id,
                    row.def_path.clone(),
                ));
            }
            many => {
                errors.push(format!(
                    "clean-origin link refused: declaration key `{key}` and source def_index \
                     {source_def_index} match {} appended definitions — duplicate exact source \
                     identity among Clean-origin rows",
                    many.len()
                ));
                return;
            }
        }
    }
    if matches.is_empty() {
        return;
    }

    // Trust (WS5.2): `Function.name` is the LINK-TIME SYMBOL, and a Rust caller's declaration
    // of a Clean-origin item and the item's Clean definition carry ONE symbol — so they are ONE
    // row. `append` published every matched definition IN its declaration's row; this pass
    // CHECKS the edges that now name the definition, exactly as strictly as it used to check
    // the edges it re-pointed, and any refusal is fatal (there is no separate declaration left
    // for a refused edge to stay on, and two rows under one symbol is `DuplicateFunctionSymbol`).
    // The declaration's own facts are read from `before`, the module as assembly left it.
    //
    // Keep an immutable snapshot of the (post-append, superset) type table so every reified
    // function-pointer edge can be checked against the definition's exact FuncTyId.
    let func_types = module.func_types.clone();
    for (decl_id, decl_key, source_def_index, target_index, def_path) in matches {
        let target_id = FuncId::new(target_index);
        if target_id != decl_id {
            errors.push(format!(
                "clean-origin link refused: the Clean definition of `{def_path}` (source \
                 def_index {source_def_index}) was published at FuncId({target_index}), not in \
                 the row of its declaration FuncId({}) `{decl_key}`. `Function.name` is the \
                 link-time symbol, so a declaration and the definition of one Rust item are ONE \
                 row — report this",
                decl_id.index()
            ));
            return;
        }
        let (
            declaration_ty,
            declaration_calling_conv,
            declaration_is_unsigned,
            declaration_returns,
        ) = {
            let declaration_rows: Vec<&Function> =
                before.functions.iter().filter(|f| f.id == decl_id).collect();
            match declaration_rows.as_slice() {
                [] => {
                    errors.push(format!(
                        "clean-origin link: declaration FuncId({}) for `{decl_key}` vanished \
                         before linking — report this",
                        decl_id.index()
                    ));
                    return;
                }
                [declaration] if declaration.is_declaration() => (
                    declaration.ty,
                    declaration.calling_conv,
                    // Trust (v41 `RustAbiVararg`): is this row still carrying the
                    // producer's UNKNOWN-signature encoding (`is_vararg`)? A
                    // signed row is left exactly as it is — the join is not a
                    // signature authority over a declaration some other pass
                    // already typed.
                    before
                        .func_types
                        .get(declaration.ty.index() as usize)
                        .is_some_and(|ft| ft.is_vararg),
                    // Trust (IR-5 type binding): the recovered Rust-side result type(s) —
                    // `decl_ret`, "the type its call sites agreed on", already remapped
                    // into THIS module's numbering, and KEPT even by the unknown-signature
                    // encoding, which drops `params` and keeps `returns`. EMPTY means
                    // "nothing survived", never "returns nothing", so the result check
                    // compares only positions both sides name.
                    before
                        .func_types
                        .get(declaration.ty.index() as usize)
                        .map(|ft| ft.returns.clone())
                        .unwrap_or_default(),
                ),
                [declaration] => {
                    errors.push(format!(
                        "clean-origin link: FuncId({}) for `{decl_key}` names body-bearing \
                         function `{}` rather than its bodyless declaration — refusing to \
                         rewrite any edge",
                        decl_id.index(),
                        declaration.name
                    ));
                    return;
                }
                many => {
                    errors.push(format!(
                        "clean-origin link: declaration FuncId({}) for `{decl_key}` resolves to \
                         {} function rows — refusing ambiguous identity",
                        decl_id.index(),
                        many.len()
                    ));
                    return;
                }
            }
        };
        let (target_ty, target_sig, target_calling_conv) = {
            let Some(target) = module.functions.iter().find(|f| f.id == target_id) else {
                errors.push(format!(
                    "clean-origin link: appended definition {target_index} vanished before \
                     linking — report this"
                ));
                return;
            };
            let Some(sig) = module.func_types.get(target.ty.index() as usize) else {
                errors.push(format!(
                    "clean-origin link: appended definition `{def_path}` has a dangling \
                     FuncTyId — report this"
                ));
                return;
            };
            (target.ty, sig.clone(), target.calling_conv)
        };
        // Trust (WS5.2): refused whether or not a direct edge names the declaration. The
        // definition now TAKES the declaration's row, so a signed declaration contradicting the
        // definition's exact FuncTyId would be overwritten — hiding a checked disagreement the
        // separate (retired) row used to keep visible. The join is a linking authority, not a
        // signature authority.
        if !declaration_is_unsigned && declaration_ty != target_ty {
            errors.push(format!(
                "clean-origin link refused: declaration `{decl_key}` carries signed \
                 FuncTyId({}), but its exact-source Clean definition `{def_path}` carries \
                 FuncTyId({}); direct calls require the same signature identity, not only \
                 name, arity, or structural equality. Rebuild the direct module with one \
                 checked signature identity for both rows",
                declaration_ty.index(),
                target_ty.index(),
            ));
            return;
        }
        let mut row = LinkedRow {
            decl_func_id: decl_id.index(),
            decl_key,
            source_def_index,
            target_func_id: target_index,
            def_path,
            edges_repointed: 0,
            refusals: Vec::new(),
            type_unchecked: Vec::new(),
            retired_declaration: None,
        };
        if declaration_calling_conv != target_calling_conv {
            row.refusals.push(format!(
                "declaration `{}` uses calling convention {}, but the Clean definition uses {}",
                row.decl_key, declaration_calling_conv, target_calling_conv
            ));
        } else {
            for index in 0..module.functions.len() {
                if module.functions[index].producer == Some(Producer::Clean) {
                    continue; // Clean rows carry no Rust edges; and never rewrite them.
                }
                if module.functions[index].is_declaration() {
                    continue;
                }
                // Trust (IR-5 type binding): a COST gate, not a guard — `function_references`
                // admits exactly the two edge shapes `repoint_edges` checks.
                if !function_references(&module.functions[index], decl_id) {
                    continue;
                }
                // The caller's own SSA types, read in `before` — the module in which the
                // callee is still the DECLARATION, so a call RESULT is typed by the Rust side's
                // own observation and the result check below compares two independent
                // spellings rather than the definition with itself. The Rust bodies are
                // identical in both modules; only the declaration's row changed.
                let Some(before_function) = before.functions.get(index) else {
                    errors.push(format!(
                        "clean-origin link: Rust body FuncId({index}) has no pre-append row — \
                         report this"
                    ));
                    return;
                };
                let value_tys: BTreeMap<ValueId, Ty> = before_function
                    .typed_values(before)
                    .into_iter()
                    .map(|entry| (entry.value, entry.ty))
                    .collect();
                let unchanged = module.functions[index].clone();
                // `target_id == decl_id`: the rewrite is the identity, so this is the CHECK
                // half of the historical re-point — every edge's arity, operand and result
                // types against the definition's exact signature, every reified edge against
                // its exact FuncTyId — with the refusals collected instead of left declared.
                let outcome = repoint_edges(
                    &mut module.functions[index],
                    &func_types,
                    &value_tys,
                    &declaration_returns,
                    decl_id,
                    target_id,
                    target_ty,
                    &target_sig,
                );
                if let Err(reason) = crate::remap_certificate::certify_remap_shape(
                    &unchanged,
                    &module.functions[index],
                ) {
                    let name = unchanged.name.clone();
                    module.functions[index] = unchanged;
                    row.refusals.push(format!(
                        "function `{name}`: remap-shape certificate refused the identity rewrite \
                         ({reason}); function restored untouched"
                    ));
                    continue;
                }
                row.edges_repointed += outcome.repointed;
                row.refusals.extend(outcome.refusals);
                row.type_unchecked.extend(outcome.unchecked);
            }
        }
        // No edge can stay declared: the declaration IS the definition's row now. A refusal is
        // therefore a disagreement between the Rust call sites of one link-time symbol and its
        // Clean definition, and the module is refused rather than published with an ill-typed
        // edge — where the old seam left the edge on a separately named declaration, that name
        // no longer exists (it was the same symbol).
        if !row.refusals.is_empty() {
            errors.push(format!(
                "clean-origin link refused for `{}` (source def_index {}): its Rust call sites and \
                 its Clean definition disagree ({}). `Function.name` is the link-time symbol, so \
                 the declaration and the definition are one row and no edge can stay declared; \
                 the crate module is refused. Options: make the Rust call sites bind the Clean \
                 definition's exact carriers, or report the disagreement.",
                row.def_path,
                row.source_def_index,
                row.refusals.join("; ")
            ));
        }
        summary.linked.push(row);
    }

    // Extend the installed disclosure with the link rows (in-band).
    if let Some(disclosure) =
        module.spec_modules.iter_mut().find(|spec| spec.name == CLEAN_ORIGIN_DISCLOSURE_NAME)
    {
        for row in &summary.linked {
            disclosure.invariants.push(SpecInvariant::new(
                format!("linked:{}", row.decl_func_id),
                format!(
                    "{{\"schema\":\"trust.clean-origin-disclosure.v1\",\"decl_key\":\"{}\",\
                     \"decl_func_id\":{},\"source_def_index\":{},\"target_func_id\":{},\
                     \"def_path\":\"{}\",\"edges_repointed\":{},\
                     \"refusals\":[{}],\"type_unchecked\":[{}],\
                     \"retired_declaration\":{}}}",
                    json_escape_min(&row.decl_key),
                    row.decl_func_id,
                    row.source_def_index,
                    row.target_func_id,
                    json_escape_min(&row.def_path),
                    row.edges_repointed,
                    row.refusals
                        .iter()
                        .map(|r| format!("\"{}\"", json_escape_min(r)))
                        .collect::<Vec<_>>()
                        .join(","),
                    row.type_unchecked
                        .iter()
                        .map(|r| format!("\"{}\"", json_escape_min(r)))
                        .collect::<Vec<_>>()
                        .join(","),
                    json_string_or_null(row.retired_declaration.as_deref()),
                ),
            ));
        }
    }
}

/// Whether `function` still names `id` through any edge shape the link pass
/// knows — a direct `Inst::Call` callee or a reified `Constant::FnDef`. The
/// same two shapes `repoint_edges` rewrites; a new admitted edge shape must be
/// added to BOTH, or a retirement could orphan a live reference.
fn function_references(function: &Function, id: FuncId) -> bool {
    function.blocks.iter().flat_map(|block| &block.body).any(|node| match &node.inst {
        Inst::Call { callee, .. } => *callee == id,
        Inst::Const { value: Constant::FnDef(target), .. } => *target == id,
        _ => false,
    })
}

/// `"<escaped>"` or the literal `null`, for the optional disclosure fields.
fn json_string_or_null(value: Option<&str>) -> String {
    match value {
        Some(value) => format!("\"{}\"", json_escape_min(value)),
        None => "null".to_string(),
    }
}

/// Can `==` decide this type WITHOUT consulting any module's tables?
///
/// Delegates to the producer's own [`crate::crate_module::ty_table_free`] with exactly
/// two deviations for THIS seam:
///
/// * `Ty::Handle` is ADMITTED. It carries an inline `(name, runtime)` pair and no table
///   id, and trust-ir's own structural comparator compares it by value. It is the one
///   non-scalar Clean carrier (`Nat`), so excluding it would blind this guard at exactly
///   the row the 2026-09-16 audit names.
/// * `Ty::FatPtr(TraitObject { .. })` is REFUSED. `ty_table_free` admits it because a
///   SPLICE copies it verbatim; here an id disagreement would become a fail-closed edge,
///   and `trait_id` is a module-local number two independently interned signatures need
///   not assign alike.
fn ty_link_decidable(ty: &Ty) -> bool {
    match ty {
        Ty::Handle(_) => true,
        Ty::FatPtr(trust_ir::FatPtrKind::TraitObject { .. }) => false,
        Ty::Vector(elem, _) => ty_link_decidable(elem),
        Ty::Tuple(elems) => elems.iter().all(ty_link_decidable),
        Ty::Ref(inner)
        | Ty::RefMut(inner)
        | Ty::PtrConst(inner)
        | Ty::PtrMut(inner)
        | Ty::Rc(inner) => ty_link_decidable(inner),
        other => crate::crate_module::ty_table_free(other),
    }
}

/// What this seam is willing to CLAIM about one (Rust spelling, Clean spelling) pair.
///
/// `Undecided` is a first-class outcome, not a failure. A refusal leaves the declaration
/// referenced AND unsigned, which `crate_module::unsignable_declaration_refusals` turns
/// into a finalization error and `rustc_mir_build` makes FATAL under a claiming policy —
/// so a refusal this seam cannot justify is a build break for a program that may be
/// perfectly well typed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum TyLink {
    Bound,
    Differs,
    Undecided(&'static str),
}

/// The refusal boundary: answer `Differs` exactly where trust-ir's OWN call-argument rule
/// would fire AND the comparison cannot be confounded by interning. Never stricter than
/// the IR it feeds; never weaker than a fact it can establish.
fn ty_link_verdict(rust: &Ty, clean: &Ty) -> TyLink {
    // trust-ir EXEMPTS refine-involving call edges (`trust-ir-build/src/validate.rs`:
    // `&& !(actual_ty.is_refine() || expected_ty.is_refine())`, "decided by
    // `validate_refinements`"). Refusing one here would make this seam STRICTER than the
    // module it produces — a manufactured build break on a legal module.
    if rust.is_refine() || clean.is_refine() {
        return TyLink::Undecided(
            "a refinement — trust-ir decides refine-involving call edges in `validate_refinements`",
        );
    }
    // `Ty::Error` is the producer's explicit typing hole, and trust-ir's structural
    // comparator answers `false` for it against EVERYTHING INCLUDING ITSELF. Reading that
    // `false` as a mismatch is the cheapest false refusal available.
    if matches!(rust, Ty::Error) || matches!(clean, Ty::Error) {
        return TyLink::Undecided("one side is the producer's `Ty::Error` typing hole");
    }
    if ty_link_decidable(rust) && ty_link_decidable(clean) {
        // Both spellings are table-free, so `==` and `ty_structurally_eq_across` provably
        // coincide and the answer is exact in BOTH directions.
        return if rust == clean { TyLink::Bound } else { TyLink::Differs };
    }
    if std::mem::discriminant(rust) != std::mem::discriminant(clean) {
        // Different type CONSTRUCTORS. No numbering of any table identifies a `Ty::Struct`
        // with a `Ty::U64`, or a `Ty::Handle` with a `Ty::Array`.
        return TyLink::Differs;
    }
    // Same table-indexed constructor on BOTH sides — the one case where ids are genuinely
    // not comparable: `append_clean_origin_candidates` pushes `record.signature` VERBATIM
    // with no `TyId` remap, so equal ids are not evidence of equal types and unequal ids
    // are not evidence of different ones.
    TyLink::Undecided("both sides name a module table under the same type constructor")
}

/// What [`repoint_edges`] did to one function's edges.
struct RepointOutcome {
    repointed: u32,
    /// Edges left DECLARED. Non-empty blocks retirement and re-signing, so it becomes a
    /// finalization error downstream — never use it for "not established".
    refusals: Vec<String>,
    /// Operand positions on RE-POINTED edges this seam declined to decide. Disclosed,
    /// deliberately non-blocking: see [`LinkedRow::type_unchecked`].
    unchecked: Vec<String>,
}

/// Rewrite the callee ids inside one function: `Inst::Call { callee }` and
/// `Constant::FnDef(id)` equal to `decl_id` become `target_id`.
///
/// A reified function pointer CARRIES a `FuncTyId`, so its check is an id comparison, and
/// structural equality is insufficient because the validator pins a statically resolved
/// `CallIndirect` edge to the target function's declared signature identity. A direct call
/// carries no id: its effective signature is RECONSTRUCTED — arguments from the caller's
/// own SSA value types (`value_tys`), results from `decl_returns`, the declaration's
/// recovered `returns` — and every position this seam can DECIDE must agree with the Clean
/// definition's.
///
/// `decl_returns` is the independent Rust-side result fact, and it is why the result half
/// needs no value map: a call's result types ARE its callee's declared returns, so a value
/// map would only echo the thing under test, whereas `decl_ret` is "the type its call sites
/// agreed on", already remapped into the assembled module and PRESERVED by the
/// unknown-signature encoding, which drops `params` and keeps `returns`.
///
/// Fail-closed on disagreement (the edge stays declared, disclosed per edge);
/// disclosed-but-linked on a position no interning can decide, because a refusal here
/// becomes a fatal finalization error and "not established" is not "wrong".
/// Signed-declaration identity is enforced BATCH-WIDE by `link_clean_origin_edges` before
/// any rewrite, so it is not repeated per edge.
fn repoint_edges(
    function: &mut Function,
    func_types: &[FuncTy],
    value_tys: &BTreeMap<ValueId, Ty>,
    decl_returns: &[Ty],
    decl_id: FuncId,
    target_id: FuncId,
    target_ty: FuncTyId,
    target_sig: &FuncTy,
) -> RepointOutcome {
    let mut repointed = 0u32;
    let mut refusals = Vec::new();
    let mut unchecked = Vec::new();
    let function_name = function.name.clone();
    for block in &mut function.blocks {
        for node in &mut block.body {
            match &mut node.inst {
                Inst::Call { callee, args } if *callee == decl_id => {
                    if node.results.len() != target_sig.returns.len() {
                        refusals.push(format!(
                            "function `{function_name}`: a call site binds {} result(s) but \
                             the Clean definition returns {} — the edge stays declared \
                             (fail-closed); rebind the results to link it",
                            node.results.len(),
                            target_sig.returns.len(),
                        ));
                        continue;
                    }
                    if args.len() != target_sig.params.len() {
                        refusals.push(format!(
                            "function `{function_name}`: a call site passes {} argument(s) \
                             but the Clean definition takes {} — the edge stays declared \
                             (fail-closed); fix the call arity to link it",
                            args.len(),
                            target_sig.params.len(),
                        ));
                        continue;
                    }
                    // Anything this edge discloses is rolled back if the edge is then
                    // refused: "the edge was re-pointed" must never be claimed about an
                    // edge that stayed declared.
                    let unchecked_mark = unchecked.len();
                    let mut edge_refusal: Option<String> = None;

                    // ── RESULTS — free, no value map ─────────────────────────────
                    // A LENGTH disagreement is not a mismatch: an empty `decl_returns`
                    // means "no Rust-side type survived" (a `ret_ty` conflict, or an id
                    // that would not remap), not "returns nothing". Only positions both
                    // sides name are compared.
                    if decl_returns.len() == target_sig.returns.len() {
                        for (position, (declared, clean)) in
                            decl_returns.iter().zip(&target_sig.returns).enumerate()
                        {
                            match ty_link_verdict(declared, clean) {
                                TyLink::Bound => {}
                                TyLink::Differs => {
                                    edge_refusal = Some(format!(
                                        "function `{function_name}`: every Rust call site of this \
                                         declaration agreed its result {position} is {declared:?}, \
                                         but the Clean definition returns {clean:?} — the edge \
                                         stays declared (fail-closed); give the Clean definition \
                                         the carrier the call sites use to link it"
                                    ));
                                    break;
                                }
                                TyLink::Undecided(why) => unchecked.push(format!(
                                    "function `{function_name}`: result {position} ({declared:?} \
                                     vs {clean:?}) NOT type-checked — {why}; the edge was \
                                     re-pointed on arity and identity alone"
                                )),
                            }
                        }
                    } else if !decl_returns.is_empty() {
                        unchecked.push(format!(
                            "function `{function_name}`: the declaration recovered {} result \
                             type(s) and the Clean definition returns {} — result types NOT \
                             checked; the edge was re-pointed on arity and identity alone",
                            decl_returns.len(),
                            target_sig.returns.len(),
                        ));
                    }

                    // ── ARGUMENTS — the paid half ────────────────────────────────
                    // An unsigned declaration carries `params: []`, so the caller's own
                    // SSA value table is the ONLY source of an argument's Rust-side type.
                    // An ABSENT value is the normal fail-safe, not an error:
                    // `Function::typed_values` omits a type it cannot resolve rather than
                    // guessing it.
                    if edge_refusal.is_none() {
                        for (position, (arg, param)) in
                            args.iter().zip(&target_sig.params).enumerate()
                        {
                            let Some(arg_ty) = value_tys.get(arg) else {
                                unchecked.push(format!(
                                    "function `{function_name}`: argument {position} is %{} whose \
                                     type this producer could not reconstruct — position NOT \
                                     type-checked; the edge was re-pointed on arity and identity \
                                     alone",
                                    arg.index(),
                                ));
                                continue;
                            };
                            match ty_link_verdict(arg_ty, param) {
                                TyLink::Bound => {}
                                TyLink::Differs => {
                                    edge_refusal = Some(format!(
                                        "function `{function_name}`: a call site passes argument \
                                         {position} at type {arg_ty:?}, but the Clean definition \
                                         declares parameter {position} at type {param:?} — the \
                                         edge stays declared (fail-closed); give both sides one \
                                         type to link it"
                                    ));
                                    break;
                                }
                                TyLink::Undecided(why) => unchecked.push(format!(
                                    "function `{function_name}`: argument {position} ({arg_ty:?} \
                                     vs {param:?}) NOT type-checked — {why}; the edge was \
                                     re-pointed on arity and identity alone"
                                )),
                            }
                        }
                    }

                    if let Some(refusal) = edge_refusal {
                        unchecked.truncate(unchecked_mark);
                        refusals.push(refusal);
                        continue;
                    }
                    *callee = target_id;
                    repointed += 1;
                }
                Inst::Const { ty, value: Constant::FnDef(id) } if *id == decl_id => {
                    let trust_ir::ty::Ty::Func(sig_id) = ty else {
                        refusals.push(format!(
                            "function `{function_name}`: a reified function-pointer edge carries \
                             non-function type {ty:?} — the edge stays declared (fail-closed)"
                        ));
                        continue;
                    };
                    let Some(edge_sig) = func_types.get(sig_id.as_usize()) else {
                        refusals.push(format!(
                            "function `{function_name}`: a reified function-pointer edge carries \
                             dangling FuncTyId({}) — the edge stays declared (fail-closed)",
                            sig_id.index(),
                        ));
                        continue;
                    };
                    if *sig_id != target_ty {
                        refusals.push(format!(
                            "function `{function_name}`: a reified function-pointer edge carries \
                             FuncTyId({}) with signature {edge_sig:?}, but the Clean definition \
                             declares FuncTyId({}) with signature {target_sig:?} — the edge stays \
                             declared (fail-closed)",
                            sig_id.index(),
                            target_ty.index(),
                        ));
                        continue;
                    }
                    *id = target_id;
                    repointed += 1;
                }
                _ => {}
            }
        }
    }
    RepointOutcome { repointed, refusals, unchecked }
}

/// Plan step 3.4 (design §4.2, D37 part 1): the `gate` row's verdict fields and
/// the authority its Function carries, for the disclosure (`sep` = `":"`,
/// `lead` = `,"`) and coverage (`": "`, `, "`) renderings. Additive: every
/// pre-existing key keeps its spelling and value. Disclosure, never authority:
/// nothing reads these strings to license anything.
fn carrier_license_fields(row: &EmittedRow, sep: &str, lead: &str) -> String {
    let (Some(environment), Some(kernel), Some(ledger)) =
        (&row.gate_environment_digest, row.gate_kernel_version, &row.gate_ledger_digest)
    else {
        return String::new();
    };
    format!(
        "{lead}gate_environment_digest{sep}{}\"{lead}gate_kernel_version{sep}{}\"\
         {lead}gate_ledger_digest{sep}{}\"{lead}codegen_license{sep}{}\"\
         {lead}codegen_license_scope{sep}stamped on the published Function and honored only \
         beside this compilation's session ledger entry; no lane admits it before plan step 3.6 \
         (F1's Compiler::compile lane); a codegen license, never a proof grade\"",
        json_escape_min(environment),
        json_escape_min(kernel),
        json_escape_min(ledger),
        trust_clean_ir_gate::CLEAN_CARRIER_GATE_AUTHORITY,
    )
}

fn install_disclosure(module: &mut Module, summary: &CleanOriginJoinSummary) {
    let mut disclosure = SpecModule::new(CLEAN_ORIGIN_DISCLOSURE_NAME);
    for row in &summary.emitted {
        let (tier_fields, body_gate) = match row.tier {
            CleanOriginTier::Structural => ("\"tier\":\"structural\"".to_string(), "ungated"),
            CleanOriginTier::KernelTv => (
                "\"tier\":\"kernel-tv\",\
                 \"judgment\":\"denotation-at-Nat-mod-2^w\",\
                 \"carrier_faithfulness\":\"not-established\""
                    .to_string(),
                "ungated",
            ),
            CleanOriginTier::Gate => (
                "\"tier\":\"gate\",\
                 \"judgment\":\"actual-TrustIR-Function-carrier-defeq\",\
                 \"carrier_faithfulness\":\"established\""
                    .to_string(),
                "carrier-faithful",
            ),
        };
        let gate_fields = match (&row.gate_subject_digest, row.gate_carrier, row.gate_method) {
            (Some(digest), Some(carrier), Some(method)) => format!(
                ",\"gate_subject_digest\":\"{}\",\"gate_carrier\":\"{carrier}\",\
                 \"gate_method\":\"{method}\",\"gate_scope\":\
                 \"same-crate Rust-to-Clean link only; not G5 cross-crate and not G7 codegen\"{}",
                json_escape_min(digest),
                carrier_license_fields(row, "\":\"", ",\"")
            ),
            _ => String::new(),
        };
        let tv_note = match &row.tv_note {
            Some(note) => format!(",\"tv_note\":\"{}\"", json_escape_min(note)),
            None => String::new(),
        };
        // Plan step 3.5 (D37 part 1): the `mir_gate` field says what the recorder did with the
        // MIR body on this lane; a row with no recorded lane (none today) states that it is not
        // stated rather than inherit the MIR lane's claim.
        let mir_gate = summary.mir_gate.get(&row.def_index).map_or(
            "not stated: no recorder lane was recorded for this row",
            |gate| gate.disclosure(),
        );
        disclosure.invariants.push(SpecInvariant::new(
            format!("fn:{}", row.func_id),
            // The verdict wording binds to the MIR body — the trust-ir
            // spelling itself is UNGATED below tier `gate`. Gate rows name the
            // exact independently reflected/digest-bound permission; every
            // other tier keeps `body_gate: ungated` so a tier-ignorant consumer
            // still refuses.
            format!(
                "{{\"schema\":\"trust.clean-origin-disclosure.v1\",\
                 \"def_path\":\"{}\",\"clean_name\":\"{}\",\"shape\":\"{}\",\
                 {tier_fields},\"body_gate\":\"{body_gate}\",\
                 \"mir_gate\":\"{}\"{gate_fields}{tv_note}}}",
                json_escape_min(&row.def_path),
                json_escape_min(&row.clean_name),
                row.shape,
                json_escape_min(mir_gate),
            ),
        ));
    }
    for (def_index, def_path, _clean, shape, reason) in &summary.skipped {
        disclosure.invariants.push(SpecInvariant::new(
            format!("skipped:{def_index}"),
            format!(
                "{{\"schema\":\"trust.clean-origin-disclosure.v1\",\"def_path\":\"{}\",\
                 \"shape\":\"{shape}\",\"reason\":\"{}\"}}",
                json_escape_min(def_path),
                json_escape_min(reason),
            ),
        ));
    }
    for (name, disposition, tv, reason) in &summary.general {
        let tv_field = if *tv {
            ",\"tv\":\"mint-certified (clean-compiler kernel gate; re-checked in-tree by \
             the clean_backend_tv mirror before the proof channels were stripped); at Nat \
             denotation level, carrier faithfulness NOT established\""
                .to_string()
        } else {
            String::new()
        };
        let reason_field = if reason.is_empty() {
            String::new()
        } else {
            format!(",\"reason\":\"{}\"", json_escape_min(reason))
        };
        disclosure.invariants.push(SpecInvariant::new(
            format!("general:{}", json_escape_min(name)),
            format!(
                "{{\"schema\":\"trust.clean-origin-disclosure.v1\",\"clean_name\":\"{}\",\
                 \"tier\":\"general\",\"disposition\":\"{disposition}\",\
                 \"body_gate\":\"ungated\",\"provenance\":\"clean-compiler general \
                 pipeline (kernel Expr -> L5CNF -> L5IR); NO sealed plan, NO side-C \
                 diamond, NOT callable from Rust — do not hand to codegen\"{tv_field}{reason_field}}}",
                json_escape_min(name),
            ),
        ));
    }
    // An island-free crate records nothing and installs nothing.
    if !disclosure.invariants.is_empty() {
        module.spec_modules.push(disclosure);
    }
}

/// Structural validation of one emitted function in isolation, over a
/// one-function mini-module carrying only its interned signature.
///
/// Deliberately NOT the whole-module validation tripwire (log-only by its own
/// ratified ruling): the population here is bounded and has none of the known
/// whole-module reject classes; a failure is signal, not noise.
fn validate_standalone(record: &CleanOriginIrRecord) -> Result<(), String> {
    render_validation(trust_ir_build::validate_module(&tv_mini_module(record, None)))
}

/// The kernel-tv re-check (design §4): the mini-module now carries the minted
/// obligation + CleanCic certificate, and `trust_ir_build::validate_module`
/// routes it to the `clean_backend_tv` re-checker — which re-derives the
/// emitted side's denotation from THIS module (the producer cannot choose the
/// LHS) and has the CIC kernel decide the equation on theorem insertion.
fn recheck_kernel_tv(record: &CleanOriginIrRecord, mint: &CleanTvMint) -> Result<(), String> {
    render_validation(trust_ir_build::validate_module(&tv_mini_module(record, Some(mint))))
}

fn render_validation(
    validation_errors: Vec<trust_ir_build::validate::ValidationError>,
) -> Result<(), String> {
    if validation_errors.is_empty() {
        return Ok(());
    }
    let mut rendered: Vec<String> =
        validation_errors.iter().take(3).map(|e| format!("{e:?}")).collect();
    if validation_errors.len() > 3 {
        rendered.push(format!("... and {} more", validation_errors.len() - 3));
    }
    Err(rendered.join("; "))
}

fn tv_mini_module(record: &CleanOriginIrRecord, mint: Option<&CleanTvMint>) -> Module {
    let mut mini = Module::new(format!("clean-origin-validate::{}", record.clean_name));
    mini.func_types.push(record.signature.clone());
    let mut function = record.function.clone();
    function.id = FuncId::new(0);
    function.ty = FuncTyId::new(0);
    mini.functions.push(function);
    if let Some(mint) = mint {
        mini.proof_obligations.push(mint.obligation.clone());
        mini.proof_certificates.push(mint.certificate.clone());
    }
    mini
}

/// Intern `ty` into `module.func_types` by equality.
fn intern_func_ty(module: &mut Module, ty: &FuncTy) -> FuncTyId {
    if let Some(position) = module.func_types.iter().position(|existing| existing == ty) {
        return FuncTyId::new(u32::try_from(position).expect("func_types exceeds u32"));
    }
    let id = FuncTyId::new(u32::try_from(module.func_types.len()).expect("func_types exceeds u32"));
    module.func_types.push(ty.clone());
    id
}

/// Trust (v1.2): the `types`-table twin of [`intern_func_ty`].
fn intern_type(module: &mut Module, ty: &trust_ir::ty::Ty) -> TyId {
    if let Some(position) = module.types.iter().position(|existing| existing == ty) {
        return TyId::new(u32::try_from(position).expect("types exceeds u32"));
    }
    let id = TyId::new(u32::try_from(module.types.len()).expect("types exceeds u32"));
    module.types.push(ty.clone());
    id
}

/// Minimal JSON string escaping for the disclosure payloads (mirrors the
/// discipline of `crate_module::json_escape`, private to the frozen file).
pub(crate) fn json_escape_min(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out
}

/// Render the `clean_origin` coverage section (design §3.4). Additive: every
/// pre-existing coverage key, totals entry, and row is byte-unchanged.
pub fn coverage_section(summary: &CleanOriginJoinSummary) -> String {
    use std::fmt::Write as _;
    let mut out = String::new();
    if !summary.recorded {
        let _ = write!(
            out,
            "  \"clean_origin\": {{\n    \"recorded\": false,\n    \"reason\": \"verification \
             off: this lane does not demand Clean-origin bodies; rows deliberately absent\"\n  }}"
        );
        return out;
    }
    let _ = writeln!(out, "  \"clean_origin\": {{");
    let _ = writeln!(out, "    \"recorded\": true,");
    let _ = writeln!(out, "    \"emitted\": [");
    for (i, row) in summary.emitted.iter().enumerate() {
        let comma = if i + 1 == summary.emitted.len() { "" } else { "," };
        let (tier_fields, body_gate) = match row.tier {
            CleanOriginTier::Structural => ("\"tier\": \"structural\"".to_string(), "ungated"),
            CleanOriginTier::KernelTv => (
                "\"tier\": \"kernel-tv\", \
                 \"judgment\": \"denotation-at-Nat-mod-2^w\", \
                 \"carrier_faithfulness\": \"not-established\""
                    .to_string(),
                "ungated",
            ),
            CleanOriginTier::Gate => (
                "\"tier\": \"gate\", \
                 \"judgment\": \"actual-TrustIR-Function-carrier-defeq\", \
                 \"carrier_faithfulness\": \"established\""
                    .to_string(),
                "carrier-faithful",
            ),
        };
        let gate_fields = match (&row.gate_subject_digest, row.gate_carrier, row.gate_method) {
            (Some(digest), Some(carrier), Some(method)) => format!(
                ", \"gate_subject_digest\": \"{}\", \"gate_carrier\": \"{carrier}\", \
                 \"gate_method\": \"{method}\", \"gate_scope\": \
                 \"same-crate Rust-to-Clean link only; not G5 cross-crate and not G7 codegen\"{}",
                json_escape_min(digest),
                carrier_license_fields(row, "\": \"", ", \"")
            ),
            _ => String::new(),
        };
        let tv_note = match &row.tv_note {
            Some(note) => format!(", \"tv_note\": \"{}\"", json_escape_min(note)),
            None => String::new(),
        };
        let _ = writeln!(
            out,
            "      {{\"def_index\": {}, \"def_path\": \"{}\", \"clean_name\": \"{}\", \
             \"shape\": \"{}\", {tier_fields}, \"body_gate\": \"{body_gate}\", \
             \"func_id\": {}{gate_fields}{tv_note}}}{comma}",
            row.def_index,
            json_escape_min(&row.def_path),
            json_escape_min(&row.clean_name),
            row.shape,
            row.func_id,
        );
    }
    let _ = writeln!(out, "    ],");
    let _ = writeln!(out, "    \"skipped\": [");
    for (i, (def_index, def_path, clean_name, shape, reason)) in summary.skipped.iter().enumerate()
    {
        let comma = if i + 1 == summary.skipped.len() { "" } else { "," };
        let _ = writeln!(
            out,
            "      {{\"def_index\": {def_index}, \"def_path\": \"{}\", \"clean_name\": \"{}\", \
             \"shape\": \"{shape}\", \"reason\": \"{}\"}}{comma}",
            json_escape_min(def_path),
            json_escape_min(clean_name),
            json_escape_min(reason),
        );
    }
    let _ = writeln!(out, "    ],");
    let _ = writeln!(out, "    \"linked\": [");
    for (i, row) in summary.linked.iter().enumerate() {
        let comma = if i + 1 == summary.linked.len() { "" } else { "," };
        let _ = writeln!(
            out,
            "      {{\"decl_key\": \"{}\", \"decl_func_id\": {}, \
             \"source_def_index\": {}, \"target_func_id\": {}, \"def_path\": \"{}\", \
             \"edges_repointed\": {}, \"refusals\": [{}], \
             \"type_unchecked\": [{}], \"retired_declaration\": {}}}{comma}",
            json_escape_min(&row.decl_key),
            row.decl_func_id,
            row.source_def_index,
            row.target_func_id,
            json_escape_min(&row.def_path),
            row.edges_repointed,
            row.refusals
                .iter()
                .map(|r| format!("\"{}\"", json_escape_min(r)))
                .collect::<Vec<_>>()
                .join(", "),
            row.type_unchecked
                .iter()
                .map(|r| format!("\"{}\"", json_escape_min(r)))
                .collect::<Vec<_>>()
                .join(", "),
            json_string_or_null(row.retired_declaration.as_deref()),
        );
    }
    let _ = writeln!(out, "    ],");
    let _ = writeln!(out, "    \"general\": [");
    for (i, (name, disposition, tv, reason)) in summary.general.iter().enumerate() {
        let comma = if i + 1 == summary.general.len() { "" } else { "," };
        let reason_field = if reason.is_empty() {
            String::new()
        } else {
            format!(", \"reason\": \"{}\"", json_escape_min(reason))
        };
        let _ = writeln!(
            out,
            "      {{\"clean_name\": \"{}\", \"tier\": \"general\", \
             \"disposition\": \"{disposition}\", \"tv_mint_certified\": {tv}{reason_field}}}{comma}",
            json_escape_min(name),
        );
    }
    let _ = writeln!(out, "    ],");
    let _ = writeln!(out, "    \"general_renamed\": [");
    for (i, (from, to)) in summary.general_renamed.iter().enumerate() {
        let comma = if i + 1 == summary.general_renamed.len() { "" } else { "," };
        let _ = writeln!(
            out,
            "      {{\"general_name\": \"{}\", \"recorded_as\": \"{}\"}}{comma}",
            json_escape_min(from),
            json_escape_min(to),
        );
    }
    let _ = writeln!(out, "    ]");
    let _ = write!(out, "  }}");
    out
}

#[cfg(test)]
#[path = "clean_origin_join/bulk_memory_type_remap_tests.rs"]
mod bulk_memory_type_remap_tests;

#[cfg(test)]
#[path = "clean_origin_join/unwind_and_site_refusal_tests.rs"]
mod unwind_and_site_refusal_tests;

#[cfg(test)]
mod tests {
    use trust_certify::clean_island::CleanIslandSession;
    use trust_ir::BinOp;
    use trust_ir::ty::Ty;

    use super::*;

    /// Both real Rust bodies have the same type, so swapping identities cannot
    /// be detected by signature validation alone.
    /// WS5.2: the fixture's stand-in for `tcx.symbol_name` of the minted Rust item `answer`.
    const ANSWER_SYMBOL: &str = "_RNvCs0_5probe6answer";

    fn rust_call_fixture() -> (Module, CleanOriginRustCallRecord, Vec<RustBodyIdentity>) {
        use trust_certify::clean_island::RustCallee;
        let declared = ["left", "right"].map(|name| RustCallee {
            clean_name: name.into(),
            params: vec![trust_types::Ty::u64()],
            result: trust_types::Ty::u64(),
        });
        let mut session = CleanIslandSession::new();
        session.declare_rust_callees(&declared).expect("registered fixture callees");
        let checked = session.check("def answer (x : UInt64) : UInt64 := left (right x)");
        assert!(!checked.is_rejected(), "fixture must kernel-check: {checked:?}");
        let roster = declared
            .iter()
            .map(|callee| trust_clean_origin::RustCalleeRef {
                clean_name: callee.clean_name.clone(),
                def_path: format!("probe::{}", callee.clean_name),
                params: callee.params.clone(),
                result: callee.result.clone(),
            })
            .collect::<Vec<_>>();
        let plan = trust_clean_origin::plan_clean_origin_body_with_rust_callees(
            session.environment().expect("untainted fixture"),
            "answer",
            &roster,
        )
        .expect("call plan");
        let mut builder = trust_ir_build::ModuleBuilder::new("owned-rust-callees");
        let ty = builder.add_func_type(vec![Ty::U64], vec![Ty::U64]);
        for name in ["left", "right"] {
            let mut function = builder.function(name, ty);
            let entry = function.create_block();
            let parameter = function.add_block_param(entry, Ty::U64);
            function.switch_to_block(entry);
            function.ret(vec![parameter]);
            function.build();
        }
        let mut module = builder.build().expect("ModuleBuilder::build: test fixture");
        let mut owners = Vec::new();
        let mut callees = Vec::new();
        for (index, function) in module.functions.iter_mut().enumerate() {
            function.producer = Some(Producer::TRust);
            function.calling_conv = trust_ir::CallingConv::Rust;
            let owner = RustBodyIdentity {
                def_index: 10 + index as u32,
                definition: crate::lineage::DefinitionIdentity::test_only(1, index as u64),
                func_id: function.id,
                abi: crate::calling_convention::FunctionAbi::RUST,
                kind: crate::BodyKind::Fn,
                // The full Rust path intentionally differs from extractor spelling.
                def_path: function.name.clone(),
            };
            let (plan_index, plan_callee) = plan
                .callees()
                .iter()
                .enumerate()
                .find(|(_, callee)| callee.clean_name == function.name)
                .expect("plan row");
            callees.push(CleanOriginRustCallee {
                plan_index,
                def_index: owner.def_index,
                definition: owner.definition,
                def_path: owner.def_path.clone(),
                signature: trust_clean_ir::rust_callee_func_ty(plan_callee).unwrap(),
                plan_def_path: plan_callee.def_path.clone(),
                clean_name: plan_callee.clean_name.clone(),
            });
            owners.push(owner);
        }
        let record = CleanOriginRustCallRecord {
            def_index: 42,
            def_path: "answer".into(),
            link_symbol: ANSWER_SYMBOL.into(),
            clean_name: "answer".into(),
            source: trust_clean_ir_gate::rust_calls::RetainedRustCallSource::retain(
                std::sync::Arc::new(session.environment().unwrap().clone()),
                std::sync::Arc::new(plan),
            ),
            callees,
            mir_gate: MirGateAtSeam::Reearned,
        };
        assert!(trust_ir_build::validate_module(&module).is_empty());
        (module, record, owners)
    }

    #[test]
    fn rust_calls_bind_real_owned_bodies_and_remain_structural() {
        let (mut module, mut record, owners) = rust_call_fixture();
        record.callees.reverse(); // Transport order does not determine plan order.
        let original = module.clone();
        let mut errors = Vec::new();
        let summary = append_clean_origin_with_rust_callees(
            &mut module,
            vec![CleanOriginIrOutcome::RustCalls(record)],
            &mut errors,
            &owners,
        );
        assert!(errors.is_empty(), "{errors:?}");
        assert_eq!(summary.emitted.len(), 1);
        assert!(summary.skipped.is_empty());
        let row = &summary.emitted[0];
        assert!(row.tier == CleanOriginTier::Structural);
        assert!(
            row.tv_note.as_deref().unwrap().contains("linked-module candidate model/trace accepted")
        );
        assert_eq!(summary.pending_rust_calls.len(), 1);
        let pending = &summary.pending_rust_calls[0];
        assert_eq!(pending.def_index, row.def_index);
        assert_eq!(pending.func_id.index(), row.func_id);
        pending.source.check_module_model(&module, pending.func_id, &pending.bindings)
            .expect("the original kernel snapshot survives actual owned-body binding");
        assert!(summary.gated.is_empty(), "retention grants no gate token");
        assert!(
            row.gate_subject_digest.is_none()
                && row.gate_carrier.is_none()
                && row.gate_method.is_none()
        );
        let function = &module.functions[row.func_id as usize];
        assert_eq!(function.producer, Some(Producer::Clean));
        // WS5.2: named by the minted Rust item's link-time symbol, Lean spelling displayed.
        assert_eq!(function.name, ANSWER_SYMBOL);
        assert_eq!(function.display_path.as_deref(), Some("answer"));
        assert!(
            function.attrs.is_empty() && function.proofs.is_empty() && function.summary.is_none()
        );
        let calls = function
            .blocks
            .iter()
            .flat_map(|block| &block.body)
            .filter_map(|node| {
                assert!(node.proofs.is_empty() && node.proof_context.is_none());
                if let Inst::Call { callee, .. } = &node.inst {
                    assert!(node.inst.has_side_effects(), "no NoPanic or readnone assumption");
                    Some(*callee)
                } else {
                    None
                }
            })
            .collect::<Vec<_>>();
        assert_eq!(calls, vec![owners[1].func_id, owners[0].func_id]);
        assert_eq!(&module.functions[..2], original.functions.as_slice());
        assert!(trust_ir_build::validate_module(&module).is_empty());
        assert!(coverage_section(&summary).contains("\"tier\": \"structural\""));
        let published = std::sync::Arc::new(module);
        let reason = crate::AssembledCrateModuleForCodegen::checked(
            published.clone(),
            vec![(
                row.def_index,
                crate::lineage::DefinitionIdentity::test_only(1, 42),
                FuncId::new(row.func_id),
            )],
        )
        .err()
        .expect("the actual appended call chain must not acquire a codegen handoff");
        assert!(
            reason.contains("Clean-origin") && reason.contains("not codegen-eligible"),
            "{reason}"
        );
        crate::AssembledCrateModuleForCodegen::checked(
            published,
            owners.iter().map(|owner| (owner.def_index, owner.definition, owner.func_id)).collect(),
        )
        .expect("the original Rust body identity population remains selectable");
    }

    #[test]
    fn rust_call_binding_rejects_identity_abi_type_and_population_mutations() {
        for mutation in 0..21 {
            let (mut module, mut record, mut owners) = rust_call_fixture();
            match mutation {
                0 => {
                    owners.remove(0);
                }
                1 => owners.push(owners[0].clone()),
                2 => {
                    record.callees[0].definition =
                        crate::lineage::DefinitionIdentity::test_only(9, 9)
                }
                3 => record.callees[0].def_path = "wrong::left".into(),
                4 => owners[0].kind = crate::BodyKind::StaticInit,
                5 => owners[0].kind = crate::BodyKind::ConstInit,
                6 => owners[0].abi = crate::calling_convention::FunctionAbi::C,
                7 => module.functions[0].calling_conv = trust_ir::CallingConv::C,
                8 => module.functions[0].producer = Some(Producer::Clean),
                9 => module.functions[0].producer = None,
                10 => module.functions[0].blocks.clear(),
                11 => module.func_types[0].returns = vec![Ty::U8],
                12 => record.callees[0].signature.is_vararg = true,
                13 => {
                    let mut duplicate = owners[0].clone();
                    duplicate.def_index += 100;
                    owners.push(duplicate);
                }
                14 => {
                    module.functions[1].id = module.functions[0].id;
                }
                15 => {
                    record.callees.pop();
                }
                16 => record.callees.push(record.callees[0].clone()),
                17 => record.callees[0].plan_index = usize::MAX,
                18 => record.callees[0].plan_def_path = "probe::wrong".into(),
                19 => record.callees[0].clean_name = "wrong".into(),
                20 => record.def_index = owners[0].def_index,
                _ => unreachable!(),
            }
            let before = module.clone();
            assert!(
                bind_rust_call_candidate(&module, &record, &owners, &[]).is_err(),
                "mutation {mutation}"
            );
            assert_eq!(module, before, "a refusal must not intern types or append bodies");
        }
    }

    /// Trust (WS5.2): the Rust-call overlap guard still refuses what it refused when it compared
    /// `name == def_path` — a defined row DISPLAYING the pending def path (its pre-WS5.2
    /// name) — although no row is named by the definition's link-time symbol. Mutation
    /// control: drop the display half of `defined_row_claims` and this binds.
    #[test]
    fn a_defined_row_displaying_the_pending_def_path_still_refuses_the_rust_call() {
        let (mut module, record, owners) = rust_call_fixture();
        assert!(module.functions.iter().all(|function| function.name != record.link_symbol));
        module.functions[1].display_path = Some(record.def_path.clone());
        let before = module.clone();
        let reason = bind_rust_call_candidate(&module, &record, &owners, &[])
            .err()
            .expect("the pre-WS5.2 overlap refusal");
        assert!(reason.contains("already claims the pending Clean definition"), "{reason}");
        assert_eq!(module, before);
    }

    #[test]
    fn rust_call_equal_signature_swapped_plan_indices_refuse() {
        let (module, mut record, owners) = rust_call_fixture();
        assert_eq!(record.callees[0].signature, record.callees[1].signature);
        let first = record.callees[0].plan_index;
        record.callees[0].plan_index = record.callees[1].plan_index;
        record.callees[1].plan_index = first;
        let reason = bind_rust_call_candidate(&module, &record, &owners, &[])
            .err()
            .expect("swapped plan rows");
        assert!(reason.contains("plan-row identity"), "{reason}");
    }

    #[test]
    fn rust_calls_validate_the_whole_actual_module() {
        let (mut module, record, owners) = rust_call_fixture();
        // The target identity/type remains valid; its physical body is invalid.
        // A placeholder-only mini-module would conceal this failure.
        module.functions[0].blocks[0].body.pop();
        let before = module.clone();
        let mut errors = Vec::new();
        let summary = append_clean_origin_with_rust_callees(
            &mut module,
            vec![CleanOriginIrOutcome::RustCalls(record)],
            &mut errors,
            &owners,
        );
        assert_eq!(errors.len(), 1, "{errors:?}");
        assert!(errors[0].contains("whole-module call validation refused"), "{errors:?}");
        assert!(!summary.recorded && summary.emitted.is_empty());
        assert_eq!(module, before);
    }

    /// A `local-unlowered` declaration of the Rust item `def_path`, NAMED by its link-time
    /// `symbol` with `def_path` as its display path — exactly as assembly mints it (WS5.2).
    fn pending_clean_declaration(
        module: &mut Module,
        def_path: &str,
        symbol: &str,
        def_index: u32,
    ) -> DeclarationLinkIdentity {
        let ty = intern_func_ty(
            module,
            &FuncTy { params: vec![], returns: vec![Ty::U64], is_vararg: true, abi: None },
        );
        let id = FuncId::new(module.functions.len() as u32);
        let mut declaration = Function::new(id, symbol, ty, trust_ir::BlockId::new(0));
        declaration.display_path = Some(def_path.to_string());
        declaration.calling_conv = trust_ir::CallingConv::Rust;
        module.functions.push(declaration);
        DeclarationLinkIdentity {
            func_id: id,
            key: format!("local-unlowered:{def_path}"),
            local_def_index: Some(def_index),
        }
    }

    fn add_rust_caller(module: &mut Module, declaration: FuncId) -> FuncId {
        let mut builder = trust_ir_build::ModuleBuilder::new("rust-caller");
        let ty = builder.add_func_type(vec![Ty::U64], vec![Ty::U64]);
        let mut function = builder.function("calls_pending_clean", ty);
        let entry = function.create_block();
        let value = function.add_block_param(entry, Ty::U64);
        function.switch_to_block(entry);
        let result = function.call(declaration, vec![value]);
        function.ret(vec![result]);
        function.build();
        let mut function =
            builder.build().expect("ModuleBuilder::build: test fixture").functions.remove(0);
        let id = FuncId::new(module.functions.len() as u32);
        function.id = id;
        function.ty = intern_func_ty(
            module,
            &FuncTy { params: vec![Ty::U64], returns: vec![Ty::U64], is_vararg: false, abi: None },
        );
        function.calling_conv = trust_ir::CallingConv::Rust;
        function.producer = Some(Producer::TRust);
        module.functions.push(function);
        id
    }

    #[test]
    fn pending_rust_call_batch_links_unsigned_declaration_before_full_validation() {
        let (mut module, record, owners) = rust_call_fixture();
        let declaration = pending_clean_declaration(&mut module, "answer", ANSWER_SYMBOL, 42);
        let caller = add_rust_caller(&mut module, declaration.func_id);
        assert!(!trust_ir_build::validate_module(&module).is_empty(), "unsigned input");
        let before = module.clone();
        let mut errors = Vec::new();
        let prepared = prepare_clean_origin_with_rust_callees(
            &module,
            vec![CleanOriginIrOutcome::RustCalls(record)],
            &mut errors,
            &owners,
            std::slice::from_ref(&declaration),
        );
        assert_eq!(module, before, "preparation never publishes a candidate");
        assert_eq!(prepared.summary().emitted.len(), 1);
        let summary =
            link_prepared_clean_origin(&mut module, prepared, &[declaration.clone()], &mut errors);
        assert!(errors.is_empty(), "{errors:?}");
        assert_eq!(summary.emitted.len(), 1);
        assert_eq!(summary.linked.len(), 1);
        assert_eq!(summary.linked[0].edges_repointed, 1);
        // WS5.2: the definition took its declaration's row — nothing retired, no orphan.
        assert_eq!(summary.linked[0].retired_declaration, None);
        let target = FuncId::new(summary.emitted[0].func_id);
        assert_eq!(target, declaration.func_id, "one link-time symbol, one row");
        assert_eq!(module.functions.len(), before.functions.len(), "no row was appended");
        assert!(!module.functions[target.index() as usize].is_declaration());
        assert!(function_references(&module.functions[caller.index() as usize], target));
        assert!(trust_ir_build::validate_module(&module).is_empty());
        assert!(summary.emitted[0].tier == CleanOriginTier::Structural);
        assert!(summary.emitted[0].gate_subject_digest.is_none());
    }

    #[test]
    fn pending_rust_call_batch_signs_other_outcomes_in_either_registry_order() {
        for call_first in [false, true] {
            let (mut module, record, owners) = rust_call_fixture();
            let mut declarations =
                vec![pending_clean_declaration(&mut module, "answer", ANSWER_SYMBOL, 42)];
            declarations.push(pending_clean_declaration(
                &mut module,
                "probe_def_43",
                "probe_def_43",
                43,
            ));
            add_rust_caller(&mut module, declarations[1].func_id);
            let mut outcomes = vec![
                CleanOriginIrOutcome::RustCalls(record),
                CleanOriginIrOutcome::Emitted(projection_record(43)),
            ];
            if !call_first {
                outcomes.reverse();
            }
            let rows_before = module.functions.len();
            let mut errors = Vec::new();
            let prepared = prepare_clean_origin_with_rust_callees(
                &module,
                outcomes,
                &mut errors,
                &owners,
                &declarations,
            );
            let summary =
                link_prepared_clean_origin(&mut module, prepared, &declarations, &mut errors);
            assert!(errors.is_empty(), "order {call_first}: {errors:?}");
            assert_eq!(summary.emitted.len(), 2);
            assert_eq!(summary.linked.len(), 2);
            assert_eq!(module.functions.len(), rows_before, "both definitions took their rows");
            for row in &summary.linked {
                assert!(row.refusals.is_empty() && row.retired_declaration.is_none());
                assert_eq!(row.decl_func_id, row.target_func_id, "one symbol, one row");
                assert!(!module.functions[row.target_func_id as usize].is_declaration());
                assert_eq!(row.source_def_index, if row.def_path == "answer" { 42 } else { 43 });
            }
            assert!(trust_ir_build::validate_module(&module).is_empty());
        }
    }

    #[test]
    fn pending_rust_call_transaction_rolls_back_identity_type_and_body_refusals() {
        for mutation in 0..7 {
            let (mut module, record, owners) = rust_call_fixture();
            let mut declarations =
                vec![pending_clean_declaration(&mut module, "answer", ANSWER_SYMBOL, 42)];
            let caller = add_rust_caller(&mut module, declarations[0].func_id);
            match mutation {
                0 => declarations.clear(),
                1 => declarations[0].local_def_index = Some(41),
                2 => declarations[0].key = "local-unlowered:another_answer".into(),
                3 => {
                    module.functions[declarations[0].func_id.index() as usize].calling_conv =
                        trust_ir::CallingConv::C
                }
                4 => {
                    let ty = intern_func_ty(
                        &mut module,
                        &FuncTy {
                            params: vec![Ty::U8],
                            returns: vec![Ty::U64],
                            is_vararg: false,
                            abi: None,
                        },
                    );
                    let caller = &mut module.functions[caller.index() as usize];
                    caller.ty = ty;
                    caller.blocks[0].params[0].1 = Ty::U8;
                }
                5 => {
                    module.functions[caller.index() as usize].blocks[0].body.pop();
                }
                6 => {}
                _ => unreachable!(),
            }
            let before = module.clone();
            let mut errors = Vec::new();
            let prepared = prepare_clean_origin_with_rust_callees(
                &module,
                vec![CleanOriginIrOutcome::RustCalls(record)],
                &mut errors,
                &owners,
                &declarations,
            );
            if mutation == 6 {
                errors.push("caller overlap guard refused".into());
            }
            let summary =
                link_prepared_clean_origin(&mut module, prepared, &declarations, &mut errors);
            assert!(!errors.is_empty(), "mutation {mutation}");
            if mutation == 3 {
                assert!(
                    errors.iter().any(|error| error.contains("transaction refused declaration")),
                    "{errors:?}"
                );
            }
            assert!(!summary.recorded && summary.emitted.is_empty() && summary.linked.is_empty());
            assert_eq!(module, before, "mutation {mutation} must roll back every table/body/link");
        }
    }

    /// The join is a linking authority, not a signature authority. Before WS5.2 a signed
    /// declaration the definition shadowed kept its own signature on a separate (retired)
    /// row; now the definition TAKES that row, so a signed declaration contradicting the
    /// definition's exact FuncTyId would be overwritten — hiding the disagreement. It is
    /// refused instead, edges or not, and the transaction rolls back.
    #[test]
    fn pending_rust_call_transaction_refuses_a_contradicting_signed_declaration() {
        let (mut module, record, owners) = rust_call_fixture();
        let declaration = pending_clean_declaration(&mut module, "answer", ANSWER_SYMBOL, 42);
        let signed = intern_func_ty(
            &mut module,
            &FuncTy { params: vec![Ty::U8], returns: vec![Ty::U8], is_vararg: false, abi: None },
        );
        module.functions[declaration.func_id.index() as usize].ty = signed;
        let before = module.clone();
        let mut errors = Vec::new();
        let prepared = prepare_clean_origin_with_rust_callees(
            &module,
            vec![CleanOriginIrOutcome::RustCalls(record)],
            &mut errors,
            &owners,
            std::slice::from_ref(&declaration),
        );
        let summary =
            link_prepared_clean_origin(&mut module, prepared, &[declaration], &mut errors);
        assert_eq!(errors.len(), 1, "{errors:?}");
        assert!(errors[0].contains("the same signature identity"), "{errors:?}");
        assert!(!summary.recorded);
        assert_eq!(module, before, "the signed declaration is left exactly as it was");
    }

    #[test]
    fn prepared_rust_call_transaction_rejects_a_changed_original_module() {
        let (mut module, record, owners) = rust_call_fixture();
        let mut errors = Vec::new();
        let prepared = prepare_clean_origin_with_rust_callees(
            &module,
            vec![CleanOriginIrOutcome::RustCalls(record)],
            &mut errors,
            &owners,
            &[],
        );
        module.functions[0].name.push_str("_changed");
        let before = module.clone();
        let summary = link_prepared_clean_origin(&mut module, prepared, &[], &mut errors);
        assert_eq!(errors.len(), 1);
        assert!(errors[0].contains("changed after preparation"));
        assert!(!summary.recorded && summary.emitted.is_empty());
        assert_eq!(module, before);
    }

    #[test]
    fn pending_rust_call_batch_does_not_bypass_required_gate_tv() {
        let (mut module, record, owners) = rust_call_fixture();
        let mut declaration = pending_clean_declaration(&mut module, "answer", ANSWER_SYMBOL, 42);
        declaration.local_def_index = Some(41);
        let before = module.clone();
        let mut errors = Vec::new();
        let prepared = prepare_clean_origin_with_rust_callees(
            &module,
            vec![
                CleanOriginIrOutcome::RustCalls(record),
                CleanOriginIrOutcome::Emitted(independently_minted_wrapping_record(
                    43,
                    "gated_add",
                )),
            ],
            &mut errors,
            &owners,
            std::slice::from_ref(&declaration),
        );
        assert!(
            errors.iter().any(|error| error.contains("kernel-TV companion is missing")),
            "{errors:?}"
        );
        assert!(prepared.summary().emitted.iter().all(|row| row.tier != CleanOriginTier::Gate));
        let summary =
            link_prepared_clean_origin(&mut module, prepared, &[declaration], &mut errors);
        assert!(!errors.is_empty());
        assert!(!summary.recorded && summary.emitted.is_empty() && summary.skipped.is_empty());
        assert!(summary.pending_rust_calls.is_empty(), "failed batch retains no source contexts");
        assert_eq!(module, before);
    }

    #[test]
    fn legacy_append_cannot_invent_rust_callee_authority() {
        let (mut module, record, _) = rust_call_fixture();
        let before = module.functions.clone();
        let mut errors = Vec::new();
        let summary = append_clean_origin(
            &mut module,
            vec![CleanOriginIrOutcome::RustCalls(record)],
            &mut errors,
        );
        assert!(errors.is_empty() && summary.emitted.is_empty());
        assert_eq!(summary.skipped.len(), 1);
        assert!(summary.skipped[0].4.contains("assembled owners"));
        assert_eq!(module.functions, before);
    }

    #[test]
    fn source_candidate_comparison_refusal_is_disclosed_without_minting_authority() {
        use trust_certify::clean_island::RustCallee;
        let (mut module, mut record, owners) = rust_call_fixture();
        let declared = ["left", "right"].map(|name| RustCallee {
            clean_name: name.into(),
            params: vec![trust_types::Ty::u64()],
            result: trust_types::Ty::u64(),
        });
        let mut later = CleanIslandSession::new();
        later.declare_rust_callees(&declared).unwrap();
        assert!(!later.check("def answer (x : UInt64) : UInt64 := right (left x)").is_rejected());
        // Keep the original emission plan but supply a different source
        // snapshot. Ordinary structural binding still succeeds; the actual
        // original-source comparison must disclose this disagreement.
        record.source = trust_clean_ir_gate::rust_calls::RetainedRustCallSource::retain(
            std::sync::Arc::new(later.environment().unwrap().clone()),
            std::sync::Arc::new(record.source.plan().clone()),
        );
        let original = module.clone();
        let mut errors = Vec::new();
        let summary = append_clean_origin_with_rust_callees(
            &mut module,
            vec![CleanOriginIrOutcome::RustCalls(record)],
            &mut errors,
            &owners,
        );
        assert!(errors.is_empty(), "{errors:?}");
        assert_eq!(summary.emitted.len(), 1);
        let row = &summary.emitted[0];
        assert!(row.tier == CleanOriginTier::Structural);
        assert!(
            row.tv_note.as_deref().unwrap().contains("linked-module candidate model/trace refused")
        );
        assert!(summary.gated.is_empty());
        assert!(
            row.gate_subject_digest.is_none()
                && row.gate_carrier.is_none()
                && row.gate_method.is_none()
        );
        assert_eq!(&module.functions[..original.functions.len()], original.functions.as_slice());
        let body = module.function_by_id(FuncId::new(row.func_id)).unwrap();
        assert!(body.attrs.is_empty() && body.proofs.is_empty() && body.summary.is_none());
        assert!(body.body_gate.is_none());
        assert!(trust_ir_build::validate_module(&module).is_empty());
        assert!(coverage_section(&summary).contains("candidate model/trace refused"));
    }

    #[test]
    fn pending_rust_calls_share_duplicate_identity_prepass() {
        for duplicate_pending in [false, true] {
            let (mut module, record, owners) = rust_call_fixture();
            let second = if duplicate_pending {
                CleanOriginIrOutcome::RustCalls(record.clone())
            } else {
                let mut existing = projection_record(record.def_index);
                existing.def_path = record.def_path.clone();
                CleanOriginIrOutcome::Emitted(existing)
            };
            let before = module.functions.clone();
            let mut errors = Vec::new();
            let summary = append_clean_origin_with_rust_callees(
                &mut module,
                vec![CleanOriginIrOutcome::RustCalls(record), second],
                &mut errors,
                &owners,
            );
            assert_eq!(errors.len(), 2, "both path and DefIndex collide");
            assert!(summary.emitted.is_empty() && summary.skipped.is_empty());
            assert_eq!(module.functions, before);
        }
    }

    #[test]
    fn targeted_plan_cannot_be_demoted_to_pending_rust_calls() {
        let (mut module, mut record, owners) = rust_call_fixture();
        let mut session = CleanIslandSession::new();
        assert!(!session.check("def add8 (a b : UInt8) : UInt8 := a + b").is_rejected());
        let plan = trust_clean_origin::plan_clean_origin_body(session.environment().unwrap(), "add8")
            .unwrap();
        record.source = trust_clean_ir_gate::rust_calls::RetainedRustCallSource::retain(
            std::sync::Arc::new(session.environment().unwrap().clone()),
            std::sync::Arc::new(plan),
        );
        record.clean_name = "add8".into();
        assert!(trust_clean_ir_gate::gate_targets(record.source.plan()));
        let before = module.functions.clone();
        let mut errors = Vec::new();
        let summary = append_clean_origin_with_rust_callees(
            &mut module,
            vec![CleanOriginIrOutcome::RustCalls(record)],
            &mut errors,
            &owners,
        );
        assert_eq!(errors.len(), 1);
        assert!(errors[0].contains("never skipped or demoted"));
        assert!(summary.emitted.is_empty() && summary.skipped.is_empty());
        assert_eq!(module.functions, before);
    }

    #[test]
    fn pending_rust_calls_preserve_general_bodies_on_success_and_refusal() {
        for admit in [false, true] {
            let (mut module, record, owners) = rust_call_fixture();
            let mut builder = trust_ir_build::ModuleBuilder::new("general-answer");
            let ty = builder.add_func_type(vec![Ty::U64], vec![Ty::U64]);
            let mut function = builder.function("answer", ty);
            let entry = function.create_block();
            let value = function.add_block_param(entry, Ty::U64);
            function.switch_to_block(entry);
            function.ret(vec![value]);
            function.build();
            let general = CleanOriginIrOutcome::General(GeneralCleanIr {
                rows: vec![GeneralRow {
                    clean_name: "answer".into(),
                    outcome: GeneralOutcome::Compiled { tv_mint_certified: false },
                }],
                module: Some(builder.build().expect("ModuleBuilder::build: test fixture")),
            });
            let mut errors = Vec::new();
            let summary = append_clean_origin_with_rust_callees(
                &mut module,
                vec![CleanOriginIrOutcome::RustCalls(record), general],
                &mut errors,
                if admit { &owners } else { &[] },
            );
            assert!(errors.is_empty(), "{errors:?}");
            assert_eq!(summary.emitted.len(), usize::from(admit));
            assert_eq!(summary.skipped.len(), usize::from(!admit));
            assert_eq!(summary.general_functions.len(), 1);
            assert_eq!(module.functions.len(), if admit { 4 } else { 3 });
            // WS5.2: the admitted Rust-call row is named by the minted Rust item's link-time
            // symbol, so the general lane's own `answer` no longer collides with it and keeps
            // its own name in BOTH cases — the retired `general::` rename is not needed.
            assert!(
                module
                    .functions
                    .iter()
                    .any(|function| !function.is_declaration() && function.name == "answer")
            );
            assert_eq!(
                module.functions.iter().any(|function| function.name == ANSWER_SYMBOL),
                admit
            );
            assert!(
                module.functions.iter().all(|function| !function.name.starts_with("general::"))
            );
        }
    }

    /// Trust: trust-ir d1f4a2f's nominal `Ty::Dialect` is refused by BOTH general remap
    /// lanes -- the signature/table lane (`remap_ty`, which runs first and used to fall
    /// through its `other =>` catch-all) and the body lane (`remap_general_ty`). A Dialect
    /// carries no table index to remap, so admit-by-no-op was the path of least
    /// resistance; the refusal is the point, it must reach a Dialect nested inside a
    /// carrier, and both messages must name the fix (v7/D3). The positive control keeps
    /// the refusal from being a blanket one.
    #[test]
    fn dialect_types_are_refused_in_both_general_remap_lanes() {
        use trust_ir::ty::DialectTy;
        let dialect = Ty::Dialect(Box::new(DialectTy::new("probe", "Nominal", 1)));

        // Body lane, bare and nested.
        let mut body_ty = dialect.clone();
        let err = remap_general_ty(&mut body_ty, &[], &[])
            .expect_err("body lane must refuse a Dialect type");
        assert!(err.contains("not admitted"), "{err}");
        assert!(err.contains("probe::Nominal v1"), "{err}");
        assert!(err.contains("legalize"), "a refusal must carry the fix: {err}");
        let mut nested_body = Ty::Ref(Box::new(dialect.clone()));
        let err = remap_general_ty(&mut nested_body, &[], &[])
            .expect_err("body lane must reach a Dialect nested in a reference");
        assert!(err.contains("not admitted"), "{err}");
        let mut scalar = Ty::U64;
        assert!(remap_general_ty(&mut scalar, &[], &[]).is_ok(), "positive control");

        // Signature/table lane, bare and nested, against an empty source module.
        let mut dst = Module::new("crate_under_test");
        let src_func_types: Vec<FuncTy> = Vec::new();
        let src_types: Vec<Ty> = Vec::new();
        let mut cx = GeneralTyRemap {
            src_func_types: &src_func_types,
            src_types: &src_types,
            func_memo: Vec::new(),
            func_in_progress: Vec::new(),
            ty_memo: Vec::new(),
            ty_in_progress: Vec::new(),
        };
        let err = remap_ty(&dialect, &mut cx, &mut dst)
            .expect_err("signature lane must refuse a Dialect type");
        assert!(err.contains("does not admit"), "{err}");
        assert!(err.contains("probe::Nominal v1"), "{err}");
        assert!(err.contains("legalize"), "a refusal must carry the fix: {err}");
        let nested = Ty::RefMut(Box::new(dialect));
        let err = remap_ty(&nested, &mut cx, &mut dst)
            .expect_err("signature lane must reach a Dialect nested in a reference");
        assert!(err.contains("does not admit"), "{err}");
        assert_eq!(remap_ty(&Ty::U64, &mut cx, &mut dst).unwrap(), Ty::U64, "positive control");
        assert!(dst.func_types.is_empty() && dst.types.is_empty(), "a refusal interns nothing");
    }

    /// Trust: trust-ir v43's nominal `Ty::Handle` is refused by BOTH general remap lanes,
    /// for the same admit-by-no-op reason as `Ty::Dialect` and one sharper one. A handle's
    /// only legal origins are its runtime's PINNED entry-point declarations; this join
    /// re-mints every `FuncId` and rewrites the edges, and carries no declarations. So a
    /// handle-typed body admitted here would arrive in `dst` with its origin either absent
    /// (which `validate_module` refuses) or, worse, resolved to whichever function holds
    /// the old index. The signature lane needs its own arm because it runs FIRST and its
    /// `other =>` catch-all is correct about remapping (there is no table index) and silent
    /// about admission. Both messages must name the fix (v7/D3), and the positive controls
    /// keep neither refusal from being a blanket one.
    #[test]
    fn opaque_runtime_handles_are_refused_in_both_general_remap_lanes() {
        let handle = Ty::handle("Nat", "trust_bignum::Nat");

        // Body lane, bare and nested.
        let mut body_ty = handle.clone();
        let err = remap_general_ty(&mut body_ty, &[], &[])
            .expect_err("body lane must refuse an opaque runtime handle");
        assert!(err.contains("not admitted"), "{err}");
        assert!(err.contains("trust_bignum::Nat"), "must name the runtime: {err}");
        assert!(err.contains("pinned"), "must name what the origin is: {err}");
        assert!(err.contains("Carry the pinned"), "a refusal must carry the fix: {err}");
        let mut nested_body = Ty::Ref(Box::new(handle.clone()));
        let err = remap_general_ty(&mut nested_body, &[], &[])
            .expect_err("body lane must reach a handle nested in a reference");
        assert!(err.contains("not admitted"), "{err}");
        let mut scalar = Ty::U64;
        assert!(remap_general_ty(&mut scalar, &[], &[]).is_ok(), "positive control");

        // Signature/table lane, bare and nested, against an empty source module.
        let mut dst = Module::new("crate_under_test");
        let src_func_types: Vec<FuncTy> = Vec::new();
        let src_types: Vec<Ty> = Vec::new();
        let mut cx = GeneralTyRemap {
            src_func_types: &src_func_types,
            src_types: &src_types,
            func_memo: Vec::new(),
            func_in_progress: Vec::new(),
            ty_memo: Vec::new(),
            ty_in_progress: Vec::new(),
        };
        let err = remap_ty(&handle, &mut cx, &mut dst)
            .expect_err("signature lane must refuse an opaque runtime handle");
        assert!(err.contains("does not admit"), "{err}");
        assert!(err.contains("trust_bignum::Nat"), "must name the runtime: {err}");
        assert!(err.contains("Carry the pinned"), "a refusal must carry the fix: {err}");
        let nested = Ty::RefMut(Box::new(handle));
        let err = remap_ty(&nested, &mut cx, &mut dst)
            .expect_err("signature lane must reach a handle nested in a reference");
        assert!(err.contains("does not admit"), "{err}");
        assert_eq!(remap_ty(&Ty::U64, &mut cx, &mut dst).unwrap(), Ty::U64, "positive control");
        assert!(dst.func_types.is_empty() && dst.types.is_empty(), "a refusal interns nothing");
    }

    /// Trust: trust-ir v67's `Ty::Tensor` is refused by name in BOTH general remap lanes:
    /// the signature/table lane (`remap_ty`), which runs first and whose `other =>`
    /// catch-all would otherwise intern it, and the body lane (`remap_general_ty`). The
    /// refusal reaches a tensor nested in a carrier, and the positive controls keep it
    /// from being a blanket refusal.
    #[test]
    fn tensor_types_are_refused_in_both_general_remap_lanes() {
        let tensor = Ty::Tensor(Box::new(Ty::I32), 2);

        // Body lane, bare and nested.
        let mut body_ty = tensor.clone();
        let err = remap_general_ty(&mut body_ty, &[], &[])
            .expect_err("body lane must refuse a tensor type");
        assert!(err.contains("Ty::Tensor(rank 2)"), "{err}");
        assert!(err.contains("not admitted"), "{err}");
        let mut nested_body = Ty::Tuple(vec![Ty::U64, tensor.clone()]);
        let err = remap_general_ty(&mut nested_body, &[], &[])
            .expect_err("body lane must reach a tensor nested in a tuple");
        assert!(err.contains("Ty::Tensor"), "{err}");
        let mut scalar = Ty::I32;
        assert!(remap_general_ty(&mut scalar, &[], &[]).is_ok(), "positive control");

        // Signature/table lane, bare and nested, against an empty source module.
        let mut dst = Module::new("crate_under_test");
        let src_func_types: Vec<FuncTy> = Vec::new();
        let src_types: Vec<Ty> = Vec::new();
        let mut cx = GeneralTyRemap {
            src_func_types: &src_func_types,
            src_types: &src_types,
            func_memo: Vec::new(),
            func_in_progress: Vec::new(),
            ty_memo: Vec::new(),
            ty_in_progress: Vec::new(),
        };
        let err = remap_ty(&tensor, &mut cx, &mut dst)
            .expect_err("signature lane must refuse a tensor type");
        assert!(err.contains("Ty::Tensor(rank 2)"), "{err}");
        assert!(err.contains("does not admit"), "{err}");
        let nested = Ty::Ref(Box::new(tensor));
        let err = remap_ty(&nested, &mut cx, &mut dst)
            .expect_err("signature lane must reach a tensor nested in a reference");
        assert!(err.contains("Ty::Tensor"), "{err}");
        assert_eq!(remap_ty(&Ty::I32, &mut cx, &mut dst).unwrap(), Ty::I32, "positive control");
        assert!(dst.func_types.is_empty() && dst.types.is_empty(), "a refusal interns nothing");
    }

    /// Trust: each of trust-ir v67-v69's six tensor instructions is refused by name in the
    /// fallible body pass, before any destination table is touched.
    #[test]
    fn tensor_instructions_are_refused_by_name_in_the_body_lane() {
        let tensor = Ty::Tensor(Box::new(Ty::I32), 1);
        let v = ValueId::new(0);
        let cases = [
            (
                "a TensorContract",
                Inst::TensorContract {
                    ty: tensor.clone(),
                    lhs: v,
                    rhs: v,
                    batch: Vec::new(),
                    contract: vec![(0, 0)],
                },
            ),
            ("a TensorMap", Inst::TensorMap { ty: tensor.clone(), args: vec![v], body: Vec::new() }),
            (
                "a TensorReduce",
                Inst::TensorReduce {
                    ty: tensor.clone(),
                    src: v,
                    op: trust_ir::TensorReduceOp::Add,
                    axes: vec![0],
                    order: trust_ir::TensorReduceOrder::RowMajor,
                },
            ),
            (
                "a TensorView",
                Inst::TensorView {
                    ty: tensor.clone(),
                    src: v,
                    params: Vec::new(),
                    exprs: Vec::new(),
                    shape: vec![0],
                    index: Vec::new(),
                    fill: None,
                },
            ),
            ("a TensorGather", Inst::TensorGather { ty: tensor.clone(), data: v, coords: vec![v] }),
            (
                "a TensorScatter",
                Inst::TensorScatter { ty: tensor.clone(), init: v, src: v, coords: vec![v] },
            ),
        ];
        for (name, mut inst) in cases {
            assert_eq!(general_inst_name(&inst), name);
            let err = remap_general_inst_tys(&mut inst, &[], &[])
                .expect_err("a tensor instruction must be refused");
            assert!(err.contains(name), "{name} must be refused by name: {err}");
            assert!(err.contains("tensor instruction"), "{err}");
        }
        let mut scalar = Inst::Copy { ty: Ty::I32, operand: v };
        assert!(remap_general_inst_tys(&mut scalar, &[], &[]).is_ok(), "positive control");
    }

    /// Trust: trust-ir v70's weight blobs are refused by name wherever the join can meet
    /// them: a `Constant::TensorBlob` at any depth of an `Inst::Const`, a switch case or a
    /// global initializer, and a non-empty `Module::blobs` table, which refuses the whole
    /// general module before any id is remapped. The scalar twins still pass.
    #[test]
    fn tensor_blob_constants_and_the_blob_table_are_refused_by_name() {
        let digest = trust_ir::blob::BlobDigest::of(&[1, 2, 3, 4]);
        let blob = Constant::TensorBlob { digest, dims: vec![1] };
        assert!(general_const_tensor_blob_refusal(&blob).is_some_and(|r| r.contains("TensorBlob")));
        let nested = Constant::Aggregate(vec![Constant::Int(0), blob.clone()]);
        assert!(general_const_tensor_blob_refusal(&nested).is_some(), "the walk must be deep");
        assert!(general_const_tensor_blob_refusal(&Constant::Int(0)).is_none(), "positive control");

        // The body lane checks the value before the type, so a blob under a scalar type
        // (a shape `validate_module` refuses) is refused here too.
        let mut constant = Inst::Const { ty: Ty::U64, value: blob.clone() };
        let err = remap_general_inst_tys(&mut constant, &[], &[])
            .expect_err("a blob constant must be refused");
        assert!(err.contains("Constant::TensorBlob"), "{err}");
        let mut switch = Inst::Switch {
            value: ValueId::new(0),
            default: trust_ir::BlockId::new(0),
            default_args: Vec::new(),
            cases: vec![trust_ir::SwitchCase {
                value: blob.clone(),
                target: trust_ir::BlockId::new(0),
                args: Vec::new(),
            }],
            exhaustive_enum_unreachable: false,
        };
        let err = remap_general_inst_tys(&mut switch, &[], &[])
            .expect_err("a blob switch case must be refused");
        assert!(err.contains("Constant::TensorBlob"), "{err}");
        let mut scalar = Inst::Const { ty: Ty::U64, value: Constant::Int(7) };
        assert!(remap_general_inst_tys(&mut scalar, &[], &[]).is_ok(), "positive control");

        // A non-empty blob table refuses the whole general module, by name.
        let mut src = general_two_fn_module();
        src.intern_blob(vec![0, 0, 0, 0]);
        let mut module = Module::new("crate_under_test");
        let mut errors = Vec::new();
        let summary =
            append_clean_origin(&mut module, vec![general_outcome(Some(src))], &mut errors);
        assert!(module.functions.is_empty() && module.blobs.is_empty());
        assert!(
            summary
                .general
                .iter()
                .any(|(_, d, _, r)| *d == "merge-refused" && r.contains("weight-blob table")),
            "{:?}",
            summary.general
        );

        // A blob in a global initializer refuses the module too, by the global's name.
        let mut src = general_two_fn_module();
        src.globals.push(trust_ir::Global {
            name: "weights".to_string(),
            ty: Ty::U64,
            mutable: false,
            initializer: Some(blob),
            linkage: trust_ir::Linkage::default(),
            tls: None,
            align: None,
            section: None,
            visibility: trust_ir::Visibility::default(),
            retained: false,
        });
        let mut module = Module::new("crate_under_test");
        let mut errors = Vec::new();
        let summary =
            append_clean_origin(&mut module, vec![general_outcome(Some(src))], &mut errors);
        assert!(module.functions.is_empty() && module.globals.is_empty());
        assert!(
            summary.general.iter().any(|(_, d, _, r)| *d == "merge-refused"
                && r.contains("general global `weights`")
                && r.contains("Constant::TensorBlob")),
            "{:?}",
            summary.general
        );
    }

    /// A minimal VALID emitted function shaped like trust-clean-ir's output:
    /// one block, identity return of the sole `u64` parameter.
    fn projection_record(nth: u32) -> CleanOriginIrRecord {
        let mut mb = trust_ir_build::ModuleBuilder::new("probe");
        let ft = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
        let mut fb = mb.function(format!("probe_def_{nth}"), ft);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::U64);
        fb.switch_to_block(entry);
        fb.ret(vec![x]);
        fb.build();
        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        let mut function = module.functions.into_iter().next().expect("one function built");
        // `ModuleBuilder::function` inherits `Function::new`'s foreign-C
        // default. Real Clean-origin records are emitted by trust-clean-ir and
        // carry the compiler-minted Rust ABI, so keep this reusable fixture
        // faithful to that producer boundary.
        function.calling_conv = trust_ir::CallingConv::Rust;
        CleanOriginIrRecord {
            def_index: nth,
            def_path: format!("probe_def_{nth}"),
            clean_name: format!("probeDef{nth}"),
            shape: "projection",
            gate_target: false,
            signature: FuncTy {
                params: vec![Ty::U64],
                returns: vec![Ty::U64],
                is_vararg: false,
                abi: None,
            },
            function,
            gate: None,
            gate_environment: None,
            tv: None,
            tv_note: None,
            mir_gate: MirGateAtSeam::Reearned,
        }
    }

    fn independently_minted_wrapping_record(def_index: u32, def_path: &str) -> CleanOriginIrRecord {
        let mut session = CleanIslandSession::new();
        let outcome = session.check("def add8 (a b : UInt8) : UInt8 := a + b");
        assert!(!outcome.is_rejected(), "fixture must kernel-check: {outcome:?}");
        let env = session.environment().expect("untainted fixture");
        let plan =
            trust_clean_origin::plan_clean_origin_body(env, "add8").expect("fixture must plan");
        let signature = trust_clean_ir::trust_ir_func_ty(plan.signature())
            .expect("fixture signature must lower");
        let mut function =
            trust_clean_ir::emit_clean_origin_function(&plan, FuncId::new(0), FuncTyId::new(0))
                .expect("fixture body must emit");
        // WS5.2: the collector binds the minted Rust item's symbol before minting.
        crate::link_symbol::bind_clean_origin_link_symbol(
            &mut function,
            &format!("_RNvCs0_5probe{}{def_path}", def_path.len()),
        )
        .expect("fixture binds its link symbol");
        let gate = trust_clean_ir_gate::admit_wrapping_binop(
            env, &plan, def_index, def_path, &signature, &function,
        )
        .expect("fixture must mint a real private gate token");
        let gate_environment = trust_clean_ir_gate::GateEnvironment::of(env, plan.declaration())
            .expect("fixture closure must digest");
        CleanOriginIrRecord {
            def_index,
            def_path: def_path.to_string(),
            clean_name: "add8".to_string(),
            shape: "wrapping-binop",
            gate_target: true,
            signature,
            function,
            gate: Some(gate),
            gate_environment: Some(gate_environment),
            // These seam controls intentionally stop at authentication or
            // exact-set rejection, before the independent TV companion.
            tv: None,
            tv_note: None,
            mir_gate: MirGateAtSeam::Reearned,
        }
    }

    #[test]
    fn append_mints_dense_ids_and_interns_signatures_once() {
        let mut module = Module::new("crate_under_test");
        let existing_ty = module
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
                "rust_fn",
                existing_ty,
                trust_ir::BlockId::new(0),
            ))
            .expect("Module::try_add_function: test fixture");

        let mut errors = Vec::new();
        let summary = append_clean_origin(
            &mut module,
            vec![
                CleanOriginIrOutcome::Emitted(projection_record(7)),
                CleanOriginIrOutcome::Emitted(projection_record(9)),
            ],
            &mut errors,
        );
        assert!(errors.is_empty(), "claim-free append must not error: {errors:?}");
        assert_eq!(summary.emitted.len(), 2);
        assert!(summary.skipped.is_empty());
        assert_eq!(module.functions.len(), 3);
        for (i, f) in module.functions.iter().enumerate() {
            assert_eq!(f.id.index() as usize, i, "dense id invariant broken at {i}");
        }
        assert_eq!(module.func_types.len(), 2, "equal signatures must intern once");
        assert_eq!(module.functions[1].ty, module.functions[2].ty);
        for f in &module.functions[1..] {
            assert_eq!(f.producer, Some(Producer::Clean));
            assert!(f.proofs.is_empty(), "appended rows are claim-free");
            assert!(f.summary.is_none(), "appended rows carry no summary");
        }
        assert!(module.proof_obligations.is_empty());
        assert!(module.proof_certificates.is_empty());
        let disclosure = module
            .spec_modules
            .iter()
            .find(|s| s.name == CLEAN_ORIGIN_DISCLOSURE_NAME)
            .expect("disclosure installed");
        assert_eq!(disclosure.enforcement, trust_ir::SpecEnforcementMode::DesignOnly);
        assert!(disclosure.proofs.is_empty());
        assert_eq!(disclosure.invariants.len(), 2);
        assert!(disclosure.invariants[0].formula.contains("\"tier\":\"structural\""));
        assert!(disclosure.invariants[0].formula.contains("\"body_gate\":\"ungated\""));
    }

    /// Plan step 3.5 (D37 part 1, "state the F1 rows' authority in the disclosure"): the
    /// disclosure's `mir_gate` says what the recorder did with each row's MIR body. On the MIR
    /// lane the text is the one every row carried before 3.5, byte for byte; on F1, where no MIR
    /// body is demanded, it must not claim one was gated at the seam. FAILS before 3.5: every row
    /// claimed the MIR body's verdict was earned at the finalize seam, F1 rows included.
    #[test]
    fn the_disclosure_states_whether_the_mir_gate_was_earned_at_the_seam() {
        let mut module = Module::new("crate_under_test");
        let mut f1_record = projection_record(9);
        f1_record.mir_gate = MirGateAtSeam::NotOnF1;
        let mut errors = Vec::new();
        let summary = append_clean_origin(
            &mut module,
            vec![
                CleanOriginIrOutcome::Emitted(projection_record(7)),
                CleanOriginIrOutcome::Emitted(f1_record),
            ],
            &mut errors,
        );
        assert!(errors.is_empty(), "{errors:?}");
        assert_eq!(summary.mir_gate.get(&7), Some(&MirGateAtSeam::Reearned));
        assert_eq!(summary.mir_gate.get(&9), Some(&MirGateAtSeam::NotOnF1));
        let disclosure = module
            .spec_modules
            .iter()
            .find(|s| s.name == CLEAN_ORIGIN_DISCLOSURE_NAME)
            .expect("disclosure installed");
        let formula = |def_path: &str| {
            disclosure
                .invariants
                .iter()
                .map(|i| i.formula.as_str())
                .find(|f| f.contains(&format!("\"def_path\":\"{def_path}\"")))
                .unwrap_or_else(|| panic!("no row for {def_path}"))
        };
        let mir_lane = formula("probe_def_7");
        assert!(
            mir_lane.contains(
                "\"mir_gate\":\"kernel Faithful earned for the emitted MIR body at the finalize \
                 seam\""
            ),
            "{mir_lane}"
        );
        let f1 = formula("probe_def_9");
        assert!(f1.contains("\"mir_gate\":\"not earned on F1 (plan step 3.5)"), "{f1}");
        assert!(!f1.contains("earned for the emitted MIR body"), "{f1}");
        // Disclosure only: the tier and the stamp are the row's, whatever the lane.
        for row in [mir_lane, f1] {
            assert!(row.contains("\"tier\":\"structural\""), "{row}");
            assert!(row.contains("\"body_gate\":\"ungated\""), "{row}");
        }
    }

    #[test]
    fn invalid_emitted_function_is_demoted_to_a_skip_never_published() {
        let mut module = Module::new("crate_under_test");
        let mut record = projection_record(3);
        record.function.blocks.clear();
        // A bodyless External Rust function is a valid declaration. Make this
        // negative fixture an explicitly body-required Internal definition so
        // its invalidity is structural and does not depend on a false C ABI.
        record.function.linkage = trust_ir::Linkage::Internal;
        let mut errors = Vec::new();
        let summary = append_clean_origin(
            &mut module,
            vec![CleanOriginIrOutcome::Emitted(record)],
            &mut errors,
        );
        assert!(errors.is_empty(), "a validation demotion is a skip, not an abort");
        assert!(summary.emitted.is_empty());
        assert_eq!(summary.skipped.len(), 1);
        assert!(summary.skipped[0].4.contains("per-function validation refused"));
        assert!(module.functions.is_empty(), "an unvalidated row is never published");
    }

    #[test]
    fn targeted_wrapping_binop_without_private_gate_is_fatal_never_demoted() {
        let mut module = Module::new("crate_under_test");
        let mut record = projection_record(4);
        record.shape = "wrapping-binop";
        record.gate_target = true;
        let mut errors = Vec::new();
        let summary = append_clean_origin(
            &mut module,
            vec![CleanOriginIrOutcome::Emitted(record)],
            &mut errors,
        );
        assert_eq!(errors.len(), 1);
        assert!(errors[0].contains("carrier-gate evidence missing"));
        assert!(errors[0].contains("not demoted"));
        assert!(summary.emitted.is_empty());
        assert!(summary.skipped.is_empty(), "fatal target must not become a skip row");
        assert!(module.functions.is_empty(), "fatal target must not be published");
    }

    #[test]
    fn append_reauthenticates_body_and_def_path_before_any_possible_demotion() {
        let mut stale_body = independently_minted_wrapping_record(21, "m::add8");
        for node in &mut stale_body.function.blocks[0].body {
            if let Inst::BinOp { op, .. } = &mut node.inst {
                *op = BinOp::Sub;
            }
        }
        let mut module = Module::new("crate_under_test");
        let mut errors = Vec::new();
        let summary = append_clean_origin(
            &mut module,
            vec![CleanOriginIrOutcome::Emitted(stale_body)],
            &mut errors,
        );
        assert_eq!(errors.len(), 1, "stale body must stop at token authentication");
        assert!(errors[0].contains("token-digest"), "{errors:?}");
        assert!(summary.emitted.is_empty());
        assert!(summary.skipped.is_empty());
        assert!(module.functions.is_empty());

        let mut stale_path = independently_minted_wrapping_record(22, "m::add8");
        stale_path.def_path = "other::add8".to_string();
        let mut module = Module::new("crate_under_test");
        let mut errors = Vec::new();
        let summary = append_clean_origin(
            &mut module,
            vec![CleanOriginIrOutcome::Emitted(stale_path)],
            &mut errors,
        );
        assert_eq!(errors.len(), 1, "retargeted path must stop at token authentication");
        assert!(errors[0].contains("token-digest"), "{errors:?}");
        assert!(summary.emitted.is_empty());
        assert!(summary.skipped.is_empty());
        assert!(module.functions.is_empty());
    }

    /// Plan step 3.4 (design §4.2, D37 part 1): the token binds the kernel
    /// environment its verdict was decided in, and the append compares it with
    /// the environment the record names. A token minted over another closure,
    /// a targeted record that names no environment, and an environment on a
    /// non-target record are each fatal and unpublished, like every other
    /// targeted disagreement. Each FAILED before the environment belt (the
    /// first two published the row, the third published it too).
    #[test]
    fn a_gate_token_is_never_appended_against_another_environment() {
        // The same declaration over a different dependency closure: `add8` calls a helper.
        let mut other = CleanIslandSession::new();
        for source in [
            "def helperAdd8 (a b : UInt8) : UInt8 := a + b",
            "def add8 (a b : UInt8) : UInt8 := helperAdd8 a b",
        ] {
            let outcome = other.check(source);
            assert!(!outcome.is_rejected(), "fixture must kernel-check: {outcome:?}");
        }
        let foreign = trust_clean_ir_gate::GateEnvironment::of(
            other.environment().expect("untainted fixture"),
            &trust_certify::clean_island::island_source_name("add8").expect("a plain name"),
        )
        .expect("fixture closure must digest");

        let mut moved = independently_minted_wrapping_record(51, "m::add8");
        assert_ne!(moved.gate_environment.as_ref(), Some(&foreign), "fixture closures differ");
        moved.gate_environment = Some(foreign);
        let mut module = Module::new("crate_under_test");
        let mut errors = Vec::new();
        let summary = append_clean_origin(
            &mut module,
            vec![CleanOriginIrOutcome::Emitted(moved)],
            &mut errors,
        );
        assert_eq!(errors.len(), 1, "{errors:?}");
        assert!(errors[0].contains("token-environment"), "{errors:?}");
        assert!(errors[0].contains("not demoted"), "{errors:?}");
        assert!(summary.emitted.is_empty() && summary.gated.is_empty());
        assert!(module.functions.is_empty(), "a foreign-environment token publishes nothing");

        let mut missing = independently_minted_wrapping_record(52, "m::add8");
        missing.gate_environment = None;
        let mut module = Module::new("crate_under_test");
        let mut errors = Vec::new();
        let summary = append_clean_origin(
            &mut module,
            vec![CleanOriginIrOutcome::Emitted(missing)],
            &mut errors,
        );
        assert_eq!(errors.len(), 1, "{errors:?}");
        assert!(errors[0].contains("carrier-gate environment missing"), "{errors:?}");
        assert!(summary.emitted.is_empty() && summary.gated.is_empty());
        assert!(module.functions.is_empty());

        let mut surplus = projection_record(53);
        surplus.gate_environment = independently_minted_wrapping_record(54, "m::add8")
            .gate_environment;
        let mut module = Module::new("crate_under_test");
        let mut errors = Vec::new();
        let summary = append_clean_origin(
            &mut module,
            vec![CleanOriginIrOutcome::Emitted(surplus)],
            &mut errors,
        );
        assert_eq!(errors.len(), 1, "{errors:?}");
        assert!(
            errors[0].contains("carrier-gate environment attached to non-target"),
            "{errors:?}"
        );
        assert!(summary.emitted.is_empty());
        assert!(module.functions.is_empty());

        // Control: the record as minted stops later (at the absent kernel-TV companion), so
        // the belt above is not a blanket refusal of targeted rows.
        let exact = independently_minted_wrapping_record(55, "m::add8");
        let mut module = Module::new("crate_under_test");
        let mut errors = Vec::new();
        let _ = append_clean_origin(
            &mut module,
            vec![CleanOriginIrOutcome::Emitted(exact)],
            &mut errors,
        );
        assert_eq!(errors.len(), 1, "{errors:?}");
        assert!(errors[0].contains("kernel-TV companion is missing"), "{errors:?}");
    }

    #[test]
    fn independently_minted_duplicate_source_subjects_are_atomically_refused() {
        let first = independently_minted_wrapping_record(31, "m::add8");
        let second = independently_minted_wrapping_record(31, "m::add8");
        let mut module = Module::new("crate_under_test");
        let mut errors = Vec::new();
        let summary = append_clean_origin(
            &mut module,
            vec![CleanOriginIrOutcome::Emitted(first), CleanOriginIrOutcome::Emitted(second)],
            &mut errors,
        );
        assert!(
            errors.iter().any(|error| error.contains("duplicate emitted canonical def_path")),
            "{errors:?}"
        );
        assert!(
            errors.iter().any(|error| error.contains("duplicate emitted source def_index")),
            "{errors:?}"
        );
        assert!(summary.emitted.is_empty());
        assert!(summary.skipped.is_empty(), "duplicates are fatal, never skip rows");
        assert!(module.functions.is_empty(), "neither replayed subject may publish");
    }

    #[test]
    fn skip_rows_are_carried_and_disclosed() {
        let mut module = Module::new("crate_under_test");
        let mut errors = Vec::new();
        let summary = append_clean_origin(
            &mut module,
            vec![CleanOriginIrOutcome::Skipped(CleanOriginIrSkip {
                def_index: 11,
                def_path: "m::nat_rec".into(),
                clean_name: "natRec".into(),
                shape: "structural-nat-rec",
                gate_target: false,
                reason: "recursion computes at unbounded Nat; supply a NatRuntime".into(),
            })],
            &mut errors,
        );
        assert!(errors.is_empty());
        assert_eq!(summary.skipped.len(), 1);
        assert!(module.functions.is_empty());
        let disclosure = module
            .spec_modules
            .iter()
            .find(|s| s.name == CLEAN_ORIGIN_DISCLOSURE_NAME)
            .expect("skips are disclosed in-band too");
        assert!(disclosure.invariants[0].name.starts_with("skipped:"));
    }

    #[test]
    fn targeted_wrapping_binop_skip_is_fatal_at_public_append_belt() {
        let mut module = Module::new("crate_under_test");
        let mut errors = Vec::new();
        let summary = append_clean_origin(
            &mut module,
            vec![CleanOriginIrOutcome::Skipped(CleanOriginIrSkip {
                def_index: 44,
                def_path: "m::add8".into(),
                clean_name: "add8".into(),
                shape: "wrapping-binop",
                gate_target: true,
                reason: "synthetic precursor refusal".into(),
            })],
            &mut errors,
        );
        assert_eq!(errors.len(), 1);
        assert!(errors[0].contains("arrived at append as a skip"));
        assert!(errors[0].contains("never skipped"));
        assert!(summary.emitted.is_empty());
        assert!(summary.skipped.is_empty());
        assert!(module.functions.is_empty());
        assert!(
            module.spec_modules.iter().all(|spec| spec.name != CLEAN_ORIGIN_DISCLOSURE_NAME),
            "fatal target skip must not produce a disclosure row"
        );
    }

    #[test]
    fn island_free_crate_installs_no_disclosure() {
        let mut module = Module::new("ordinary_crate");
        let mut errors = Vec::new();
        let summary = append_clean_origin(&mut module, Vec::new(), &mut errors);
        assert!(errors.is_empty());
        assert!(summary.recorded);
        assert!(module.spec_modules.is_empty(), "no rows, no disclosure noise");
    }

    #[test]
    fn coverage_section_discloses_the_not_recorded_lane() {
        let section = coverage_section(&CleanOriginJoinSummary::not_recorded());
        assert!(section.contains("\"recorded\": false"));
        assert!(section.contains("verification off"));
        let mut module = Module::new("m");
        let mut errors = Vec::new();
        let summary = append_clean_origin(
            &mut module,
            vec![CleanOriginIrOutcome::Emitted(projection_record(1))],
            &mut errors,
        );
        let section = coverage_section(&summary);
        assert!(section.contains("\"recorded\": true"));
        assert!(section.contains("\"tier\": \"structural\""));
        assert!(section.contains("\"func_id\": 0"));
        assert!(section.contains("\"linked\": ["));
    }

    /// A caller module whose one Rust function calls a `local-unlowered`
    /// declaration for the Clean def, exactly as assemble pass 2 mints it.
    /// WS5.2: the fixture's stand-ins for `tcx.symbol_name` of the minted Rust item — one for
    /// the module-wrapped `m::clean_def`, one for the crate-root `clean_def`.
    const CLEAN_DEF_SYMBOL: &str = "_RNvNtCs0_5crate1m9clean_def";
    const CRATE_ROOT_SYMBOL: &str = "_RNvCs0_5crate9clean_def";

    fn caller_with_declared_edge() -> (Module, Vec<DeclarationLinkIdentity>) {
        caller_with_declared_edge_at(Ty::U64)
    }

    fn caller_with_declared_edge_at(carrier: Ty) -> (Module, Vec<DeclarationLinkIdentity>) {
        let mut mb = trust_ir_build::ModuleBuilder::new("caller_crate");
        // The Clean record is built in a separate module at FuncTyId(0).
        // Assembly interns into this module, whose first type is unrelated.
        let _unrelated_ft = mb.add_func_type(vec![Ty::Bool], vec![Ty::Bool]);
        let caller_ft = mb.add_func_type(vec![carrier.clone()], vec![carrier.clone()]);
        let decl_ft = caller_ft;
        // Function 0: the Rust caller; its call targets FuncId 1 (the decl).
        let mut fb = mb.function("calls_clean", caller_ft);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, carrier);
        fb.switch_to_block(entry);
        let result = fb.call(FuncId::new(1), vec![x]);
        fb.ret(vec![result]);
        fb.build();
        // Function 1: the bodyless local-unlowered declaration, NAMED by the Rust item's
        // link-time symbol with its def path as display path (WS5.2, as assembly mints it).
        let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
        module.functions[0].calling_conv = trust_ir::CallingConv::Rust;
        let mut decl =
            Function::new(FuncId::new(1), CLEAN_DEF_SYMBOL, decl_ft, trust_ir::BlockId::new(0));
        decl.display_path = Some("m::clean_def".to_string());
        decl.blocks.clear();
        // Clean-origin items are compiler-minted Rust functions. This mirrors
        // the callee ledger's registry-backed ABI classification; leaving the
        // constructor default here would make the test fixture itself claim C.
        decl.calling_conv = trust_ir::CallingConv::Rust;
        module.functions.push(decl);
        let decl_keys = vec![DeclarationLinkIdentity {
            func_id: FuncId::new(1),
            key: "local-unlowered:m::clean_def".to_string(),
            local_def_index: Some(42),
        }];
        (module, decl_keys)
    }

    /// A Rust body that takes the address of the local-unlowered declaration.
    /// `pointer_sig` is the DECLARATION's own signature, and therefore the type
    /// the reified `Constant::FnDef` carries: a function-item constant's type
    /// IS the named function's declared signature, and `validate_module`
    /// enforces that exactly — `FuncTyId` identity, on every constant, used or
    /// unused. `reuse_decl_type` reuses `func_types[0]` — the entry the
    /// `(U64) -> U64` Clean record resolves to — and additionally CALLS the
    /// pointer, exercising the full FnDef/CallIndirect identity rule; the
    /// refusal fixtures put the declaration on a SEPARATE table entry, which is
    /// the disagreement the link check must refuse.
    fn caller_with_declared_fndef(
        pointer_sig: FuncTy,
        reuse_decl_type: bool,
    ) -> (Module, Vec<DeclarationLinkIdentity>) {
        let mut mb = trust_ir_build::ModuleBuilder::new("caller_crate");
        let clean_ft = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
        let caller_ft = clean_ft;
        let FuncTy { params, returns, is_vararg, abi } = pointer_sig;
        assert!(!is_vararg, "the ModuleBuilder fixture admits fixed signatures only");
        assert!(abi.is_none(), "the ModuleBuilder fixture records no signature ABI");
        let pointer_ft = if reuse_decl_type {
            assert_eq!(params, vec![Ty::U64]);
            assert_eq!(returns, vec![Ty::U64]);
            clean_ft
        } else {
            // func_types[1]: a SEPARATE table entry, structurally equal or not.
            mb.add_func_type(params, returns)
        };
        let mut fb = mb.function("takes_clean_address", caller_ft);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::U64);
        fb.switch_to_block(entry);
        let address = fb.fn_addr(pointer_ft, FuncId::new(1));
        if reuse_decl_type {
            let result =
                fb.call_indirect_cc(address, pointer_ft, vec![x], trust_ir::CallingConv::Rust);
            fb.ret(vec![result]);
        } else {
            fb.ret(vec![x]);
        }
        fb.build();

        let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
        module.functions[0].calling_conv = trust_ir::CallingConv::Rust;
        let mut decl =
            Function::new(FuncId::new(1), CLEAN_DEF_SYMBOL, pointer_ft, trust_ir::BlockId::new(0));
        decl.display_path = Some("m::clean_def".to_string());
        decl.blocks.clear();
        decl.calling_conv = trust_ir::CallingConv::Rust;
        module.functions.push(decl);
        let declarations = vec![DeclarationLinkIdentity {
            func_id: FuncId::new(1),
            key: "local-unlowered:m::clean_def".to_string(),
            local_def_index: Some(42),
        }];
        (module, declarations)
    }

    /// The Clean definition of `m::clean_def`, bound as the collector binds it: NAMED by the
    /// Rust item's link-time symbol, its Lean spelling `cleanDef` as display path.
    fn clean_def_record_for_link() -> CleanOriginIrRecord {
        let mut record = projection_record(42);
        record.def_path = "m::clean_def".to_string();
        record.function.name = CLEAN_DEF_SYMBOL.to_string();
        record.function.display_path = Some("cleanDef".to_string());
        record
    }

    fn pin_test_target(module: &mut Module) {
        module.target_info = Some(trust_ir::TargetInfo {
            triple: "x86_64-unknown-linux-gnu".to_string(),
            pointer_size: 8,
            endianness: trust_ir::Endianness::Little,
            abi: Some("sysv64".to_string()),
            struct_passing: Default::default(),
        });
    }

    /// WS5.2: the production transaction — preparation with the declaration ledger (the
    /// definition takes its declaration's row), then the link (the edges are CHECKED). A
    /// refusal anywhere rolls the whole batch back.
    fn append_and_link(
        module: &mut Module,
        declarations: &[DeclarationLinkIdentity],
        outcomes: Vec<CleanOriginIrOutcome>,
        errors: &mut Vec<String>,
    ) -> CleanOriginJoinSummary {
        let prepared =
            prepare_clean_origin_with_rust_callees(module, outcomes, errors, &[], declarations);
        link_prepared_clean_origin(module, prepared, declarations, errors)
    }

    fn assert_rolled_back(module: &Module, before: &Module, summary: &CleanOriginJoinSummary) {
        assert!(!summary.recorded && summary.emitted.is_empty() && summary.linked.is_empty());
        assert_eq!(module, before, "a refused batch publishes nothing");
    }

    #[test]
    fn link_places_the_definition_in_its_declaration_row_and_certifies_edges() {
        let (mut module, decl_keys) = caller_with_declared_edge();
        let mut errors = Vec::new();
        let record = clean_def_record_for_link();
        assert_ne!(record.function.ty, module.functions[1].ty, "source and assembled IDs differ");
        let rows_before = module.functions.len();
        let summary = append_and_link(
            &mut module,
            &decl_keys,
            vec![CleanOriginIrOutcome::Emitted(record)],
            &mut errors,
        );
        assert!(errors.is_empty(), "{errors:?}");
        // One link-time symbol, one row: the definition occupies the declaration's id.
        assert_eq!(summary.emitted[0].func_id, 1);
        assert_eq!(module.functions.len(), rows_before, "no orphan row, nothing appended");
        assert_eq!(summary.linked.len(), 1);
        let row = &summary.linked[0];
        assert_eq!(row.decl_func_id, 1);
        assert_eq!(row.target_func_id, 1);
        assert_eq!(row.source_def_index, 42);
        assert_eq!(row.edges_repointed, 1, "refusals: {:?}", row.refusals);
        assert!(row.refusals.is_empty());
        assert_eq!(row.retired_declaration, None);
        assert_eq!(direct_call_target(&module), FuncId::new(1));
        let definition = &module.functions[1];
        assert!(!definition.is_declaration());
        assert_eq!(definition.producer, Some(Producer::Clean));
        assert_eq!(definition.name, CLEAN_DEF_SYMBOL);
        assert_eq!(definition.display_path.as_deref(), Some("cleanDef"));
        assert_eq!(definition.calling_conv, trust_ir::CallingConv::Rust);
        assert!(module.functions.iter().all(|f| !f.name.contains("<shadowed-by-")));
        let validation = trust_ir_build::validate_module(&module);
        assert!(validation.is_empty(), "the linked final module must validate: {validation:?}");
        // Disclosure carries the link row.
        let disclosure = module
            .spec_modules
            .iter()
            .find(|s| s.name == CLEAN_ORIGIN_DISCLOSURE_NAME)
            .expect("disclosure");
        let linked = disclosure
            .invariants
            .iter()
            .find(|inv| inv.name.starts_with("linked:"))
            .expect("linked evidence row");
        assert!(linked.formula.contains("\"decl_func_id\":1"), "{}", linked.formula);
        assert!(linked.formula.contains("\"target_func_id\":1"), "{}", linked.formula);
        assert!(linked.formula.contains("\"source_def_index\":42"), "{}", linked.formula);
        assert!(linked.formula.contains("\"retired_declaration\":null"), "{}", linked.formula);
    }

    /// MUTATION CONTROL for the placement: the legacy entry (no declaration ledger) appends
    /// the definition BESIDE the declaration, and because both are named by one link-time
    /// symbol the producer boundary refuses the module — which is exactly why the definition
    /// must take the declaration's row instead of an orphan being renamed out of the way.
    #[test]
    fn without_the_ledger_one_symbol_would_name_two_rows_and_is_refused() {
        let (mut module, _decl_keys) = caller_with_declared_edge();
        let mut errors = Vec::new();
        let summary = append_clean_origin(
            &mut module,
            vec![CleanOriginIrOutcome::Emitted(clean_def_record_for_link())],
            &mut errors,
        );
        assert!(errors.is_empty(), "{errors:?}");
        assert_eq!(summary.emitted[0].func_id, 2, "appended beside the declaration");
        let refused = crate::crate_module::final_module_validation_errors(&module);
        assert!(
            refused.iter().any(|e| e.contains("DuplicateFunction") && e.contains(CLEAN_DEF_SYMBOL)),
            "two rows under one symbol must be refused: {refused:?}"
        );
    }

    fn direct_call_target(module: &Module) -> FuncId {
        module.functions[0]
            .blocks
            .iter()
            .flat_map(|block| &block.body)
            .find_map(|node| match &node.inst {
                Inst::Call { callee, .. } => Some(*callee),
                _ => None,
            })
            .expect("caller retains its direct call")
    }

    #[test]
    fn link_refuses_same_arity_but_different_signed_carrier() {
        let (mut module, declarations) = caller_with_declared_edge_at(Ty::U32);
        assert!(trust_ir_build::validate_module(&module).is_empty());
        let before = module.clone();
        let mut errors = Vec::new();
        let summary = append_and_link(
            &mut module,
            &declarations,
            vec![CleanOriginIrOutcome::Emitted(clean_def_record_for_link())],
            &mut errors,
        );
        assert_eq!(errors.len(), 1, "{errors:?}");
        assert!(errors[0].contains("the same signature identity"), "{errors:?}");
        assert_rolled_back(&module, &before, &summary);
        assert_eq!(direct_call_target(&module), FuncId::new(1));
        assert!(trust_ir_build::validate_module(&module).is_empty());
    }

    #[test]
    fn link_refuses_equal_signature_with_distinct_signed_id() {
        let (mut module, declarations) = caller_with_declared_edge();
        let original_ty = module.functions[1].ty;
        let distinct_ty = FuncTyId::new(u32::try_from(module.func_types.len()).unwrap());
        module.func_types.push(module.func_types[original_ty.as_usize()].clone());
        module.functions[1].ty = distinct_ty;
        assert_ne!(original_ty, distinct_ty);
        assert_eq!(
            module.func_types[original_ty.as_usize()],
            module.func_types[distinct_ty.as_usize()]
        );
        assert!(trust_ir_build::validate_module(&module).is_empty());
        let before = module.clone();
        let mut errors = Vec::new();
        let summary = append_and_link(
            &mut module,
            &declarations,
            vec![CleanOriginIrOutcome::Emitted(clean_def_record_for_link())],
            &mut errors,
        );
        assert_eq!(errors.len(), 1, "{errors:?}");
        assert!(errors[0].contains("the same signature identity"), "{errors:?}");
        assert_rolled_back(&module, &before, &summary);
        assert_eq!(direct_call_target(&module), FuncId::new(1));
        assert!(trust_ir_build::validate_module(&module).is_empty());
    }

    /// WS5.2 NEGATIVE TWINS for the placement itself: two declaration rows claiming one source
    /// identity (the assembly's `LinkSymbolCollision` refusal should have removed their minting
    /// bodies), or a declaration row NAMED by a different symbol than the definition's, refuse
    /// the batch by name — a definition never picks one of two rows, and never takes a row that
    /// is not the declaration of its own symbol.
    #[test]
    fn placement_refuses_two_slots_and_a_differently_named_slot() {
        // Two rows, one def_index.
        let (mut module, mut declarations) = caller_with_declared_edge();
        let mut twin = module.functions[1].clone();
        twin.id = FuncId::new(2);
        module.functions.push(twin);
        declarations.push(DeclarationLinkIdentity {
            func_id: FuncId::new(2),
            key: "local-unlowered:m::clean_def|nres:1".to_string(),
            local_def_index: Some(42),
        });
        let before = module.clone();
        let mut errors = Vec::new();
        let summary = append_and_link(
            &mut module,
            &declarations,
            vec![CleanOriginIrOutcome::Emitted(clean_def_record_for_link())],
            &mut errors,
        );
        assert!(
            errors.iter().any(|e| e.contains("2 declaration rows claim source def_index 42")),
            "{errors:?}"
        );
        assert_rolled_back(&module, &before, &summary);

        // One row, the wrong symbol.
        let (mut module, declarations) = caller_with_declared_edge();
        module.functions[1].name = "_RNvNtCs0_5crate1m5other".to_string();
        let before = module.clone();
        let mut errors = Vec::new();
        let summary = append_and_link(
            &mut module,
            &declarations,
            vec![CleanOriginIrOutcome::Emitted(clean_def_record_for_link())],
            &mut errors,
        );
        assert!(
            errors.iter().any(|e| e.contains("is a declaration named `_RNvNtCs0_5crate1m5other`")
                && e.contains(CLEAN_DEF_SYMBOL)),
            "{errors:?}"
        );
        assert_rolled_back(&module, &before, &summary);
    }

    /// The crate-root shape from `docs/design/2026-09-11-tree-carrier-level-then-kexpr.md` §9:
    /// the declaration's `def_path` and the emitted definition's Clean name are ONE string.
    fn crate_root_caller_with_declared_edge() -> (Module, Vec<DeclarationLinkIdentity>) {
        let (mut module, mut declarations) = caller_with_declared_edge();
        module.functions[1].name = CRATE_ROOT_SYMBOL.to_string();
        module.functions[1].display_path = Some("clean_def".to_string());
        declarations[0].key = "local-unlowered:clean_def".to_string();
        (module, declarations)
    }

    fn crate_root_clean_def_record_for_link() -> CleanOriginIrRecord {
        let mut record = clean_def_record_for_link();
        record.def_path = "clean_def".to_string();
        record.function.name = CRATE_ROOT_SYMBOL.to_string();
        record.function.display_path = Some("clean_def".to_string());
        record
    }

    /// The crate-root island (measured 2026-09-11: `ctrl_min`'s declaration and definition
    /// shared one name) used to be repaired by renaming the orphan declaration
    /// `clean_def::<shadowed-by-clean-origin:FuncId(N)>` — a name that is no symbol at all,
    /// which trust-ir's `SyntheticSymbolName` refuses (WS4.17). Since WS5.2 the definition
    /// takes the declaration's row: no orphan, no synthetic name, and the module validates.
    #[test]
    fn crate_root_definition_takes_its_declaration_row_and_mints_no_synthetic_name() {
        let (mut module, decl_keys) = crate_root_caller_with_declared_edge();
        let mut errors = Vec::new();
        let summary = append_and_link(
            &mut module,
            &decl_keys,
            vec![CleanOriginIrOutcome::Emitted(crate_root_clean_def_record_for_link())],
            &mut errors,
        );
        assert!(errors.is_empty(), "{errors:?}");
        let row = &summary.linked[0];
        assert_eq!(row.edges_repointed, 1, "refusals: {:?}", row.refusals);
        assert!(row.refusals.is_empty());
        assert_eq!(row.retired_declaration, None);
        assert!(
            module.functions.iter().all(|f| !f.name.contains("<shadowed-by-")),
            "no synthetic symbol is minted"
        );
        let named: Vec<&Function> =
            module.functions.iter().filter(|f| f.name == CRATE_ROOT_SYMBOL).collect();
        assert_eq!(named.len(), 1, "one link-time symbol names one row");
        assert_eq!(named[0].id, FuncId::new(1));
        assert!(!named[0].is_declaration());
        let after = crate::crate_module::final_module_validation_errors(&module);
        assert!(after.is_empty(), "the linked crate-root module must validate: {after:?}");
        // Disclosed in-band and in the coverage section: nothing was retired.
        let disclosure = module
            .spec_modules
            .iter()
            .find(|s| s.name == CLEAN_ORIGIN_DISCLOSURE_NAME)
            .expect("disclosure");
        let linked = disclosure
            .invariants
            .iter()
            .find(|inv| inv.name.starts_with("linked:"))
            .expect("linked evidence row");
        assert!(linked.formula.contains("\"retired_declaration\":null"), "{}", linked.formula);
        let section = coverage_section(&summary);
        assert!(section.contains("\"retired_declaration\": null"), "{section}");
    }

    /// Trust (v41 `RustAbiVararg`): the declaration a Clean `def` that never lowered through
    /// THIR actually gets — the producer's UNKNOWN-signature encoding (`params: []` +
    /// `is_vararg: true`, `returns` from the call site) — is the exact module that failed
    /// finalization with `RustAbiVararg`. The row now BECOMES the Clean definition, carrying
    /// the definition's own typed signature, so no vararg row survives.
    #[test]
    fn an_unsigned_declaration_row_becomes_the_definition_with_its_signature() {
        let (mut module, decl_keys) = caller_with_declared_edge();
        let unknown = module
            .add_func_type(FuncTy {
                params: Vec::new(),
                returns: vec![Ty::U64],
                is_vararg: true,
                abi: None,
            })
            .expect("Module::add_func_type: test fixture");
        module.functions[1].ty = unknown;
        assert!(
            crate::crate_module::final_module_validation_errors(&module)
                .iter()
                .any(|error| error.contains("[RustAbiVararg]")),
            "fixture must reproduce the finalization failure this fix repairs"
        );

        let mut errors = Vec::new();
        let summary = append_and_link(
            &mut module,
            &decl_keys,
            vec![CleanOriginIrOutcome::Emitted(clean_def_record_for_link())],
            &mut errors,
        );
        assert!(errors.is_empty(), "{errors:?}");
        let row = &summary.linked[0];
        assert_eq!(row.edges_repointed, 1, "refusals: {:?}", row.refusals);
        assert!(row.refusals.is_empty());
        let definition = &module.functions[1];
        assert!(!definition.is_declaration(), "the row is the definition now");
        assert!(!module.func_types[definition.ty.index() as usize].is_vararg);
        assert_eq!(
            module.func_types[definition.ty.index() as usize],
            FuncTy { params: vec![Ty::U64], returns: vec![Ty::U64], is_vararg: false, abi: None }
        );
        let after = crate::crate_module::final_module_validation_errors(&module);
        assert!(after.is_empty(), "the linked module must validate: {after:?}");
    }

    /// A declaration some other pass ALREADY signed — here with exactly the definition's
    /// FuncTyId — keeps that signature: the row's type is unchanged by the placement. (One
    /// that contradicts it is refused: `link_refuses_equal_signature_with_distinct_signed_id`,
    /// `pending_rust_call_transaction_refuses_a_contradicting_signed_declaration`.)
    #[test]
    fn link_keeps_the_signature_an_already_signed_declaration_row_carried() {
        let (mut module, decl_keys) = caller_with_declared_edge();
        let signed = module.functions[1].ty;
        assert!(!module.func_types[signed.index() as usize].is_vararg, "fixture starts signed");
        let mut errors = Vec::new();
        append_and_link(
            &mut module,
            &decl_keys,
            vec![CleanOriginIrOutcome::Emitted(clean_def_record_for_link())],
            &mut errors,
        );
        assert!(errors.is_empty(), "{errors:?}");
        assert_eq!(module.functions[1].ty, signed, "an already-signed row keeps its type");
    }

    #[test]
    fn the_placed_definition_is_named_by_the_symbol_and_displays_the_lean_name() {
        // The module-wrapped shape (`m::clean_def` vs `cleanDef`): the ROW carries the Rust
        // item's link-time symbol as its name and the Clean spelling as its display path.
        let (mut module, decl_keys) = caller_with_declared_edge();
        let mut errors = Vec::new();
        let summary = append_and_link(
            &mut module,
            &decl_keys,
            vec![CleanOriginIrOutcome::Emitted(clean_def_record_for_link())],
            &mut errors,
        );
        assert!(errors.is_empty(), "{errors:?}");
        assert_eq!(summary.linked[0].retired_declaration, None);
        assert_eq!(module.functions[1].name, CLEAN_DEF_SYMBOL);
        assert_eq!(module.functions[1].display_path.as_deref(), Some("cleanDef"));
        assert!(crate::crate_module::final_module_validation_errors(&module).is_empty());
    }

    /// Arity mismatch. Before WS5.2 the edge stayed on the (still named) declaration and the
    /// module was published; now the declaration and the definition are ONE row, so no edge
    /// can stay declared and the whole batch is refused, naming the disagreeing edge.
    #[test]
    fn an_arity_refused_edge_refuses_the_batch_because_no_declaration_can_stay() {
        let (mut module, decl_keys) = crate_root_caller_with_declared_edge();
        let unknown = module
            .add_func_type(FuncTy {
                params: Vec::new(),
                returns: vec![Ty::U64],
                is_vararg: true,
                abi: None,
            })
            .expect("Module::add_func_type: test fixture");
        module.functions[1].ty = unknown;
        let mut record = crate_root_clean_def_record_for_link();
        record.signature = FuncTy {
            params: vec![Ty::U64, Ty::U64],
            returns: vec![Ty::U64],
            is_vararg: false,
            abi: None,
        };
        let mut mb = trust_ir_build::ModuleBuilder::new("probe3");
        let ft = mb.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
        let mut fb = mb.function(CRATE_ROOT_SYMBOL, ft);
        let entry = fb.create_block();
        let a = fb.add_block_param(entry, Ty::U64);
        let _b = fb.add_block_param(entry, Ty::U64);
        fb.switch_to_block(entry);
        fb.ret(vec![a]);
        fb.build();
        record.function = mb
            .build()
            .expect("ModuleBuilder::build: test fixture")
            .functions
            .into_iter()
            .next()
            .unwrap();
        record.function.display_path = Some("clean_def".to_string());
        record.function.calling_conv = trust_ir::CallingConv::Rust;
        let before = module.clone();
        let mut errors = Vec::new();
        let summary = append_and_link(
            &mut module,
            &decl_keys,
            vec![CleanOriginIrOutcome::Emitted(record)],
            &mut errors,
        );
        assert_eq!(errors.len(), 1, "{errors:?}");
        assert!(errors[0].contains("clean-origin link refused for `clean_def`"), "{errors:?}");
        assert!(errors[0].contains("passes 1 argument(s)"), "{errors:?}");
        assert_rolled_back(&module, &before, &summary);
    }

    /// Display paths are not injective. A declaration for source A must never be taken by a
    /// Clean body for distinct source B merely because B is the only row with A's display path.
    #[test]
    fn link_refuses_same_path_from_different_source_identity_without_rewriting() {
        let (mut module, mut declarations) = caller_with_declared_edge();
        declarations[0].local_def_index = Some(41); // A
        let before = module.clone();
        let mut errors = Vec::new();
        let summary = append_and_link(
            &mut module,
            &declarations,
            // B has the same display path but a distinct exact source identity.
            vec![CleanOriginIrOutcome::Emitted(clean_def_record_for_link())],
            &mut errors,
        );
        assert_eq!(errors.len(), 1, "identity mismatch must be fatal: {errors:?}");
        assert!(errors[0].contains("source identity mismatch"), "{errors:?}");
        assert!(errors[0].contains("expected def_index 41"), "{errors:?}");
        assert!(errors[0].contains("[42]"), "{errors:?}");
        assert_rolled_back(&module, &before, &summary);
        assert_eq!(direct_call_target(&module), FuncId::new(1), "A's edge is untouched");
    }

    /// `caller_with_declared_edge_at`, with the declaration left in the producer's
    /// UNKNOWN-signature encoding (`params: []` + `is_vararg: true`) — what a Clean
    /// `def` that never lowered through THIR actually gets, and the state that BYPASSES
    /// the signed-identity guard at the top of `link_clean_origin_edges`. This is the
    /// 82.6%-of-rows path on which arity used to be the entire type check.
    fn unsigned_caller_with_declared_edge(
        carrier: Ty,
        recovered_ret: Vec<Ty>,
    ) -> (Module, Vec<DeclarationLinkIdentity>) {
        let (mut module, decl_keys) = caller_with_declared_edge_at(carrier);
        let unsigned = module
            .add_func_type(FuncTy {
                params: Vec::new(),
                returns: recovered_ret,
                is_vararg: true,
                abi: None,
            })
            .expect("Module::add_func_type: test fixture");
        module.functions[1].ty = unsigned;
        (module, decl_keys)
    }

    /// A Clean definition whose signature is exactly `(param) -> (ret)`, with a body
    /// that returns its own argument so per-function validation still passes.
    fn clean_def_record_with_sig(param: Ty, ret: Ty) -> CleanOriginIrRecord {
        let mut record = clean_def_record_for_link();
        record.signature = FuncTy {
            params: vec![param.clone()],
            returns: vec![ret.clone()],
            is_vararg: false,
            abi: None,
        };
        let mut mb = trust_ir_build::ModuleBuilder::new("probe_typed");
        let ft = mb.add_func_type(vec![param.clone()], vec![ret.clone()]);
        let mut fb = mb.function(CLEAN_DEF_SYMBOL, ft);
        let entry = fb.create_block();
        let a = fb.add_block_param(entry, param);
        fb.switch_to_block(entry);
        // The carriers agree in the positive fixture; where they differ the body must
        // still type-check on its OWN signature, so return a fresh constant instead.
        if record.signature.params[0] == record.signature.returns[0] {
            fb.ret(vec![a]);
        } else {
            let z = fb.uconst(ret.clone(), 0);
            fb.ret(vec![z]);
        }
        fb.build();
        record.function = mb
            .build()
            .expect("ModuleBuilder::build: test fixture")
            .functions
            .into_iter()
            .next()
            .unwrap();
        record.function.display_path = Some("cleanDef".to_string());
        record.function.calling_conv = trust_ir::CallingConv::Rust;
        record
    }

    /// Append + link one record; returns the summary and the refusals (fatal since WS5.2).
    fn link_unsigned(
        module: &mut Module,
        decl_keys: &[DeclarationLinkIdentity],
        record: CleanOriginIrRecord,
    ) -> (CleanOriginJoinSummary, Vec<String>) {
        let mut errors = Vec::new();
        let summary = append_and_link(
            module,
            decl_keys,
            vec![CleanOriginIrOutcome::Emitted(record)],
            &mut errors,
        );
        (summary, errors)
    }

    /// POSITIVE CONTROL — the anti-false-refusal net. An UNSIGNED declaration whose
    /// call site and Clean definition agree on every carrier must still link, with
    /// nothing refused and nothing left undecided. If this ever reds, the type guard
    /// has started breaking legal two-language programs — which at this seam is a
    /// FATAL finalization error, not a tolerated red.
    #[test]
    fn link_repoints_an_unsigned_edge_whose_types_agree() {
        let (mut module, decl_keys) = unsigned_caller_with_declared_edge(Ty::U64, vec![Ty::U64]);
        let (summary, errors) =
            link_unsigned(&mut module, &decl_keys, clean_def_record_with_sig(Ty::U64, Ty::U64));
        assert!(errors.is_empty(), "{errors:?}");
        let row = &summary.linked[0];
        assert_eq!(row.edges_repointed, 1, "{row:?}");
        assert!(row.refusals.is_empty(), "{:?}", row.refusals);
        assert!(
            row.type_unchecked.is_empty(),
            "a fully table-free scalar edge must be DECIDED, not disclosed: {:?}",
            row.type_unchecked
        );
    }

    /// NEGATIVE CONTROL — the hole this guard closes. The declaration is unsigned, so
    /// the signed-identity guard is bypassed and the arity matches (1 arg, 1 result):
    /// a `u64` handed to a parameter the Clean definition declares at a different
    /// carrier. It is refused, naming the disagreeing position, and nothing publishes.
    #[test]
    fn link_refuses_an_unsigned_edge_whose_argument_type_differs() {
        let (mut module, decl_keys) = unsigned_caller_with_declared_edge(Ty::U64, vec![Ty::U64]);
        let before = module.clone();
        // The caller passes u64; the Clean definition declares u32.
        let (summary, errors) =
            link_unsigned(&mut module, &decl_keys, clean_def_record_with_sig(Ty::U32, Ty::U64));
        assert_eq!(errors.len(), 1, "{errors:?}");
        assert!(
            errors[0].contains("passes argument 0"),
            "the refusal must name the disagreeing position: {}",
            errors[0]
        );
        assert_rolled_back(&module, &before, &summary);
    }

    /// NEGATIVE CONTROL — the result half, which needs no value map because the
    /// unknown-signature encoding DROPS `params` and KEEPS `returns`. The declaration
    /// recovered `u64` from its Rust call sites; the Clean definition returns `u32`.
    #[test]
    fn link_refuses_an_unsigned_edge_whose_result_type_differs() {
        let (mut module, decl_keys) = unsigned_caller_with_declared_edge(Ty::U64, vec![Ty::U64]);
        let before = module.clone();
        let (summary, errors) =
            link_unsigned(&mut module, &decl_keys, clean_def_record_with_sig(Ty::U64, Ty::U32));
        assert_eq!(errors.len(), 1, "{errors:?}");
        assert!(
            errors[0].contains("result 0"),
            "the refusal must name the disagreeing result: {}",
            errors[0]
        );
        assert_rolled_back(&module, &before, &summary);
    }

    /// The `Undecided` arm is DISCLOSED, never refused. A declaration that recovered no
    /// Rust-side result type (`returns: []` — "nothing survived", not "returns nothing")
    /// still links. Refusing here would turn a program this seam merely could not check
    /// into a fatal finalization error.
    #[test]
    fn link_discloses_rather_than_refuses_a_result_it_cannot_decide() {
        let (mut module, decl_keys) = unsigned_caller_with_declared_edge(Ty::U64, Vec::new());
        let (summary, errors) =
            link_unsigned(&mut module, &decl_keys, clean_def_record_with_sig(Ty::U64, Ty::U64));
        assert!(errors.is_empty(), "{errors:?}");
        let row = &summary.linked[0];
        assert_eq!(row.edges_repointed, 1, "the edge must still link: {row:?}");
        assert!(row.refusals.is_empty(), "{:?}", row.refusals);
    }

    #[test]
    fn link_refuses_an_arity_mismatched_edge_and_publishes_nothing() {
        let (mut module, decl_keys) = caller_with_declared_edge();
        let unknown = module
            .add_func_type(FuncTy {
                params: Vec::new(),
                returns: vec![Ty::U64],
                is_vararg: true,
                abi: None,
            })
            .expect("Module::add_func_type: test fixture");
        module.functions[1].ty = unknown;
        let mut record = clean_def_record_for_link();
        // Sabotage the signature: the Clean def now takes 2 params, while the
        // caller passes 1 — the per-edge guard must refuse.
        record.signature = FuncTy {
            params: vec![Ty::U64, Ty::U64],
            returns: vec![Ty::U64],
            is_vararg: false,
            abi: None,
        };
        let mut mb = trust_ir_build::ModuleBuilder::new("probe2");
        let ft = mb.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
        let mut fb = mb.function(CLEAN_DEF_SYMBOL, ft);
        let entry = fb.create_block();
        let a = fb.add_block_param(entry, Ty::U64);
        let _b = fb.add_block_param(entry, Ty::U64);
        fb.switch_to_block(entry);
        fb.ret(vec![a]);
        fb.build();
        record.function = mb
            .build()
            .expect("ModuleBuilder::build: test fixture")
            .functions
            .into_iter()
            .next()
            .unwrap();
        record.function.display_path = Some("cleanDef".to_string());
        record.function.calling_conv = trust_ir::CallingConv::Rust;
        let before = module.clone();
        let mut errors = Vec::new();
        let summary = append_and_link(
            &mut module,
            &decl_keys,
            vec![CleanOriginIrOutcome::Emitted(record)],
            &mut errors,
        );
        assert_eq!(errors.len(), 1, "{errors:?}");
        assert!(errors[0].contains("passes 1 argument(s)"), "{errors:?}");
        assert_rolled_back(&module, &before, &summary);
        assert_eq!(direct_call_target(&module), FuncId::new(1), "the declaration is untouched");
    }

    #[test]
    fn link_checks_fndef_against_its_exact_signature_id() {
        let exact =
            FuncTy { params: vec![Ty::U64], returns: vec![Ty::U64], is_vararg: false, abi: None };
        let (mut module, declarations) = caller_with_declared_fndef(exact, true);
        let mut errors = Vec::new();
        let summary = append_and_link(
            &mut module,
            &declarations,
            vec![CleanOriginIrOutcome::Emitted(clean_def_record_for_link())],
            &mut errors,
        );
        assert!(errors.is_empty(), "{errors:?}");
        let row = &summary.linked[0];
        assert_eq!(row.source_def_index, 42);
        assert_eq!(row.edges_repointed, 1, "refusals: {:?}", row.refusals);
        assert!(row.refusals.is_empty());
        let pointer_target = module.functions[0]
            .blocks
            .iter()
            .flat_map(|block| &block.body)
            .find_map(|node| match &node.inst {
                Inst::Const { value: Constant::FnDef(target), .. } => Some(*target),
                _ => None,
            })
            .expect("fixture carries a reified function pointer");
        assert_eq!(pointer_target, FuncId::new(1), "the pointer names the definition's row");
        let (indirect_sig, indirect_calling_conv) = module.functions[0]
            .blocks
            .iter()
            .flat_map(|block| &block.body)
            .find_map(|node| match &node.inst {
                Inst::CallIndirect { sig, calling_conv, .. } => Some((*sig, *calling_conv)),
                _ => None,
            })
            .expect("fixture executes the reified pointer through CallIndirect");
        let target = &module.functions[1];
        assert!(!target.is_declaration());
        assert_eq!(indirect_sig, target.ty, "the indirect edge pins the target FuncTyId");
        assert_eq!(indirect_calling_conv, trust_ir::CallingConv::Rust);
        assert_eq!(indirect_calling_conv, target.calling_conv);
        let validation = trust_ir_build::validate_module(&module);
        assert!(validation.is_empty(), "the linked final module must validate: {validation:?}");
    }

    #[test]
    fn link_refuses_cross_calling_convention_before_any_edge() {
        let (mut module, declarations) = caller_with_declared_edge();
        module.functions[1].calling_conv = trust_ir::CallingConv::C;
        pin_test_target(&mut module);
        let before = module.clone();
        let mut errors = Vec::new();
        let summary = append_and_link(
            &mut module,
            &declarations,
            vec![CleanOriginIrOutcome::Emitted(clean_def_record_for_link())],
            &mut errors,
        );
        assert_eq!(errors.len(), 1, "{errors:?}");
        assert!(errors[0].contains("calling convention ccc"), "{errors:?}");
        assert!(errors[0].contains("uses rustcc"), "{errors:?}");
        assert_rolled_back(&module, &before, &summary);
        assert_eq!(direct_call_target(&module), FuncId::new(1));
        assert_eq!(module.functions[1].calling_conv, trust_ir::CallingConv::C);
        let validation = trust_ir_build::validate_module(&module);
        assert!(validation.is_empty(), "the refused module stays valid: {validation:?}");
    }

    #[test]
    fn link_refuses_cross_calling_convention_before_a_fndef_edge() {
        let exact =
            FuncTy { params: vec![Ty::U64], returns: vec![Ty::U64], is_vararg: false, abi: None };
        let (mut module, declarations) = caller_with_declared_fndef(exact, true);
        module.functions[1].calling_conv = trust_ir::CallingConv::C;
        let indirect_calling_conv = module.functions[0]
            .blocks
            .iter_mut()
            .flat_map(|block| &mut block.body)
            .find_map(|node| match &mut node.inst {
                Inst::CallIndirect { calling_conv, .. } => Some(calling_conv),
                _ => None,
            })
            .expect("fixture executes its reified function pointer");
        *indirect_calling_conv = trust_ir::CallingConv::C;
        pin_test_target(&mut module);
        let initial_validation = trust_ir_build::validate_module(&module);
        assert!(
            initial_validation.is_empty(),
            "the C declaration and indirect edge agree before relinking: {initial_validation:?}"
        );
        let before = module.clone();
        let mut errors = Vec::new();
        let summary = append_and_link(
            &mut module,
            &declarations,
            vec![CleanOriginIrOutcome::Emitted(clean_def_record_for_link())],
            &mut errors,
        );
        assert_eq!(errors.len(), 1, "{errors:?}");
        assert!(errors[0].contains("calling convention ccc"), "{errors:?}");
        assert_rolled_back(&module, &before, &summary);
    }

    #[test]
    fn link_refuses_fndef_with_equal_but_distinct_signature_id() {
        let structurally_equal =
            FuncTy { params: vec![Ty::U64], returns: vec![Ty::U64], is_vararg: false, abi: None };
        let (mut module, declarations) = caller_with_declared_fndef(structurally_equal, false);
        // Two structurally equal `FuncTy` rows are two distinct identities, and the
        // declaration is on the second one — a SIGNED declaration whose FuncTyId is not the
        // definition's, refused by the signed-identity guard before any edge is examined.
        let initial_validation = trust_ir_build::validate_module(&module);
        assert!(
            initial_validation.is_empty(),
            "the distinct-but-equal fixture starts valid: {initial_validation:?}"
        );
        let before = module.clone();
        let mut errors = Vec::new();
        let summary = append_and_link(
            &mut module,
            &declarations,
            vec![CleanOriginIrOutcome::Emitted(clean_def_record_for_link())],
            &mut errors,
        );
        assert_eq!(errors.len(), 1, "{errors:?}");
        assert!(errors[0].contains("FuncTyId(1)"), "{errors:?}");
        assert!(errors[0].contains("FuncTyId(0)"), "{errors:?}");
        assert_rolled_back(&module, &before, &summary);
    }

    #[test]
    fn link_refuses_fndef_signature_mismatch_without_publishing() {
        let mismatched = FuncTy {
            params: vec![Ty::U64, Ty::U64],
            returns: vec![Ty::U64],
            is_vararg: false,
            abi: None,
        };
        let (mut module, declarations) = caller_with_declared_fndef(mismatched, false);
        // The fixture is WELL-TYPED before linking: the reified pointer and the
        // declaration it names carry the same `FuncTyId`. The mismatch under
        // test is between that edge and the Clean definition.
        let initial_validation = trust_ir_build::validate_module(&module);
        assert!(
            initial_validation.is_empty(),
            "the mismatched-FnDef fixture starts valid: {initial_validation:?}"
        );
        let before = module.clone();
        let mut errors = Vec::new();
        let summary = append_and_link(
            &mut module,
            &declarations,
            vec![CleanOriginIrOutcome::Emitted(clean_def_record_for_link())],
            &mut errors,
        );
        assert_eq!(errors.len(), 1, "{errors:?}");
        assert!(errors[0].contains("the same signature identity"), "{errors:?}");
        assert_rolled_back(&module, &before, &summary);
    }

    /// The per-edge FnDef guard itself, reached with an UNSIGNED declaration (so the
    /// signed-identity guard does not fire first): a reified pointer typed `(u64, u64) ->
    /// u64` against a `(u64) -> u64` definition is refused by name.
    #[test]
    fn link_refuses_an_unsigned_fndef_edge_whose_signature_id_differs() {
        let mismatched = FuncTy {
            params: vec![Ty::U64, Ty::U64],
            returns: vec![Ty::U64],
            is_vararg: false,
            abi: None,
        };
        let (mut module, declarations) = caller_with_declared_fndef(mismatched, false);
        let unknown = module
            .add_func_type(FuncTy {
                params: Vec::new(),
                returns: vec![Ty::U64],
                is_vararg: true,
                abi: None,
            })
            .expect("Module::add_func_type: test fixture");
        module.functions[1].ty = unknown;
        let before = module.clone();
        let mut errors = Vec::new();
        let summary = append_and_link(
            &mut module,
            &declarations,
            vec![CleanOriginIrOutcome::Emitted(clean_def_record_for_link())],
            &mut errors,
        );
        assert_eq!(errors.len(), 1, "{errors:?}");
        assert!(errors[0].contains("reified function-pointer edge carries FuncTyId"), "{errors:?}");
        assert_rolled_back(&module, &before, &summary);
    }

    #[test]
    fn shadowed_def_path_is_refused_at_append() {
        let mut module = Module::new("crate_under_test");
        // A DEFINED (body-bearing) THIR function already claims the name.
        let mut mb = trust_ir_build::ModuleBuilder::new("shadow");
        let ft = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
        let mut fb = mb.function("probe_def_5", ft);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::U64);
        fb.switch_to_block(entry);
        fb.ret(vec![x]);
        fb.build();
        let shadow = mb.build().expect("ModuleBuilder::build: test fixture");
        module.func_types = shadow.func_types;
        module.functions = shadow.functions;

        let mut errors = Vec::new();
        let summary = append_clean_origin(
            &mut module,
            vec![CleanOriginIrOutcome::Emitted(projection_record(5))],
            &mut errors,
        );
        assert!(errors.is_empty());
        assert!(summary.emitted.is_empty());
        assert_eq!(summary.skipped.len(), 1);
        assert!(summary.skipped[0].4.contains("a defined function already claims the name"));
        assert_eq!(module.functions.len(), 1, "the shadowing row is never published");
    }

    /// Trust (WS5.2): the append's overlap guard refuses a defined row that DISPLAYS the
    /// record's def path — the exact string the pre-WS5.2 guard compared as a name — even when
    /// the row is named by a different link-time symbol. Mutation control: drop the display half
    /// of `defined_row_claims` and the record is published.
    #[test]
    fn a_defined_row_displaying_the_def_path_is_refused_at_append_as_before_ws5_2() {
        let mut module = Module::new("crate_under_test");
        let mut mb = trust_ir_build::ModuleBuilder::new("shadow");
        let ft = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
        let mut fb = mb.function("_RNvCs0_5crate11probe_def_5", ft);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::U64);
        fb.switch_to_block(entry);
        fb.ret(vec![x]);
        fb.build();
        let shadow = mb.build().expect("ModuleBuilder::build: test fixture");
        module.func_types = shadow.func_types;
        module.functions = shadow.functions;
        module.functions[0].display_path = Some("probe_def_5".to_string());
        let record = projection_record(5);
        assert_ne!(module.functions[0].name, record.function.name);
        assert_eq!(module.functions[0].display_path.as_deref(), Some(record.def_path.as_str()));

        let mut errors = Vec::new();
        let summary = append_clean_origin(
            &mut module,
            vec![CleanOriginIrOutcome::Emitted(record)],
            &mut errors,
        );
        assert!(errors.is_empty(), "{errors:?}");
        assert!(summary.emitted.is_empty());
        assert_eq!(summary.skipped.len(), 1);
        assert!(summary.skipped[0].4.contains("a defined function already claims the name"));
        assert_eq!(module.functions.len(), 1, "the shadowing row is never published");
    }

    /// A minimal VALID general-lane module shaped like the collector's output:
    /// `gen_callee` (identity on u64) and `gen_caller` (calls it), claim-free.
    fn general_two_fn_module() -> Module {
        let mut mb = trust_ir_build::ModuleBuilder::new("clean-general::probe");
        let ft = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
        let mut fb = mb.function("gen_callee", ft);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::U64);
        fb.switch_to_block(entry);
        fb.ret(vec![x]);
        fb.build();
        let mut fb = mb.function("gen_caller", ft);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::U64);
        fb.switch_to_block(entry);
        let y = fb.call(FuncId::new(0), vec![x]);
        fb.ret(vec![y]);
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    }

    fn general_outcome(module: Option<Module>) -> CleanOriginIrOutcome {
        CleanOriginIrOutcome::General(GeneralCleanIr {
            rows: vec![
                GeneralRow {
                    clean_name: "genCallee".to_string(),
                    outcome: GeneralOutcome::Compiled { tv_mint_certified: true },
                },
                GeneralRow {
                    clean_name: "genCaller".to_string(),
                    outcome: GeneralOutcome::Compiled { tv_mint_certified: false },
                },
                GeneralRow {
                    clean_name: "genTheorem".to_string(),
                    outcome: GeneralOutcome::NotComputational,
                },
            ],
            module,
        })
    }

    #[test]
    fn general_module_merges_offset_ids_and_repoints_internal_calls() {
        let mut module = Module::new("crate_under_test");
        let rust_ty = module
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
                "rust_fn",
                rust_ty,
                trust_ir::BlockId::new(0),
            ))
            .expect("Module::try_add_function: test fixture");

        let mut errors = Vec::new();
        let summary = append_clean_origin(
            &mut module,
            vec![general_outcome(Some(general_two_fn_module()))],
            &mut errors,
        );
        assert!(errors.is_empty(), "general merge must not error: {errors:?}");
        assert_eq!(module.functions.len(), 3);
        for (i, f) in module.functions.iter().enumerate() {
            assert_eq!(f.id.index() as usize, i, "dense id invariant broken at {i}");
        }
        for f in &module.functions[1..] {
            assert_eq!(f.producer, Some(Producer::Clean));
            assert!(f.proofs.is_empty(), "general rows are claim-free");
            assert!(f.summary.is_none());
            assert!(f.source_provenance.is_none(), "provenance stripped (v1)");
        }
        // The internal call edge must follow the offset: gen_caller -> gen_callee.
        let caller =
            module.functions.iter().find(|f| f.name == "gen_caller").expect("caller merged");
        let callee_id =
            module.functions.iter().find(|f| f.name == "gen_callee").expect("callee merged").id;
        let repointed =
            caller.blocks.iter().flat_map(|b| &b.body).any(
                |node| matches!(&node.inst, Inst::Call { callee, .. } if *callee == callee_id),
            );
        assert!(repointed, "internal call must be repointed by the FuncId offset");
        // Rows disclose, defined names recorded, disclosure carries the tier.
        assert_eq!(summary.general.len(), 3);
        assert!(
            summary
                .general
                .iter()
                .any(|(n, d, tv, _)| n.as_str() == "genCallee" && *d == "compiled" && *tv)
        );
        assert!(
            summary
                .general
                .iter()
                .any(|(n, d, _, _)| n.as_str() == "genTheorem" && *d == "not-computational")
        );
        assert_eq!(
            summary.general_functions,
            vec!["gen_callee".to_string(), "gen_caller".to_string()]
        );
        let disclosure = module
            .spec_modules
            .iter()
            .find(|s| s.name == CLEAN_ORIGIN_DISCLOSURE_NAME)
            .expect("disclosure installed");
        let general_row = disclosure
            .invariants
            .iter()
            .find(|inv| inv.name == "general:genCallee")
            .expect("general disclosure row");
        assert!(general_row.formula.contains("\"tier\":\"general\""));
        assert!(general_row.formula.contains("\"body_gate\":\"ungated\""));
        assert!(general_row.formula.contains("mint-certified"));
        let coverage = coverage_section(&summary);
        assert!(coverage.contains("\"tier\": \"general\""));
    }

    /// WS5.2: a general DEFINITION whose symbol another row holds now refuses the WHOLE general
    /// module, exactly like a declaration collision. It used to be recorded under a
    /// `general::<name>` namespace — a name that is no link-time symbol (WS4.17 refuses such
    /// synthetic names). Every other row is named by its Rust link-time symbol since WS5.2, so a
    /// collision is a genuine symbol clash, and no row is renamed to hide it.
    #[test]
    fn general_definition_symbol_collision_refuses_the_whole_batch_never_renamed() {
        let mut module = Module::new("crate_under_test");
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
                "gen_callee", // held by another lane's row
                ty,
                trust_ir::BlockId::new(0),
            ))
            .expect("Module::try_add_function: test fixture");
        let mut errors = Vec::new();
        let summary = append_clean_origin(
            &mut module,
            vec![general_outcome(Some(general_two_fn_module()))],
            &mut errors,
        );
        assert!(errors.is_empty());
        assert_eq!(module.functions.len(), 1, "nothing merged on a definition collision");
        assert!(module.functions.iter().all(|f| !f.name.starts_with("general::")));
        let refused: Vec<_> =
            summary.general.iter().filter(|(_, d, _, _)| *d == "merge-refused").collect();
        assert_eq!(refused.len(), 2, "BOTH compiled rows refuse together");
        assert!(refused[0].3.contains("general function `gen_callee`"), "{refused:?}");
        assert!(summary.general_functions.is_empty());
        assert!(summary.general_renamed.is_empty(), "the rename is retired");
        let cov = coverage_section(&summary);
        assert!(cov.contains("\"general_renamed\": ["), "the schema key stays: {cov}");
        assert!(!cov.contains("recorded_as"), "{cov}");
    }

    #[test]
    fn general_declaration_name_collision_still_refuses_the_whole_batch() {
        let mut module = Module::new("crate_under_test");
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
                "gen_extern",
                ty,
                trust_ir::BlockId::new(0),
            ))
            .expect("Module::try_add_function: test fixture");
        // A general module whose extra row is a DECLARATION named like an existing row.
        let mut src = general_two_fn_module();
        let decl_ty = src
            .add_func_type(FuncTy {
                params: Vec::new(),
                returns: Vec::new(),
                is_vararg: false,
                abi: None,
            })
            .expect("Module::add_func_type: test fixture");
        src.try_add_function(Function::new(
            FuncId::new(2),
            "gen_extern",
            decl_ty,
            trust_ir::BlockId::new(0),
        ))
        .expect("Module::try_add_function: test fixture");
        let mut errors = Vec::new();
        let summary =
            append_clean_origin(&mut module, vec![general_outcome(Some(src))], &mut errors);
        assert!(errors.is_empty());
        assert_eq!(module.functions.len(), 1, "nothing merged on a declaration collision");
        let refused: Vec<_> =
            summary.general.iter().filter(|(_, d, _, _)| *d == "merge-refused").collect();
        assert_eq!(refused.len(), 2, "BOTH compiled rows refuse together");
        assert!(refused[0].3.contains("declaration"));
        assert!(summary.general_functions.is_empty());
        assert!(summary.general_renamed.is_empty());
    }

    #[test]
    fn general_proof_channels_and_table_content_each_refuse() {
        // Belt 1: populated proof channels (the collector must strip).
        let mut src = general_two_fn_module();
        src.functions[0].summary = Some(trust_ir::FunctionSummary::new());
        let mut module = Module::new("crate_under_test");
        let mut errors = Vec::new();
        let summary =
            append_clean_origin(&mut module, vec![general_outcome(Some(src))], &mut errors);
        assert!(module.functions.is_empty());
        assert!(
            summary
                .general
                .iter()
                .any(|(_, d, _, r)| *d == "merge-refused" && r.contains("proof channels"))
        );

        // Belt 2: a table this merge does not remap (v1).
        let mut src = general_two_fn_module();
        src.spec_modules.push(SpecModule::new("stray"));
        let mut module = Module::new("crate_under_test");
        let mut errors = Vec::new();
        let summary =
            append_clean_origin(&mut module, vec![general_outcome(Some(src))], &mut errors);
        assert!(module.functions.is_empty());
        assert!(
            summary
                .general
                .iter()
                .any(|(_, d, _, r)| *d == "merge-refused" && r.contains("does not yet remap"))
        );

        // Belt 3: target identity must agree exactly.
        let mut src = general_two_fn_module();
        src.target_info = Some(trust_ir::TargetInfo {
            triple: "aarch64-apple-darwin".to_string(),
            pointer_size: 8,
            endianness: trust_ir::Endianness::Little,
            abi: None,
            struct_passing: trust_ir::StructPassingPolicy::Unclassified,
        });
        let mut module = Module::new("crate_under_test"); // target_info: None
        let mut errors = Vec::new();
        let summary =
            append_clean_origin(&mut module, vec![general_outcome(Some(src))], &mut errors);
        assert!(module.functions.is_empty());
        assert!(
            summary
                .general
                .iter()
                .any(|(_, d, _, r)| *d == "merge-refused" && r.contains("target_info mismatch"))
        );
    }

    #[test]
    fn general_batch_refusal_without_module_discloses_every_compiled_row() {
        let mut module = Module::new("crate_under_test");
        let mut errors = Vec::new();
        let summary = append_clean_origin(&mut module, vec![general_outcome(None)], &mut errors);
        assert!(errors.is_empty());
        assert!(module.functions.is_empty());
        assert_eq!(summary.general.len(), 3);
        let refused: Vec<_> =
            summary.general.iter().filter(|(_, d, _, _)| *d == "merge-refused").collect();
        assert_eq!(refused.len(), 2);
        assert!(refused[0].3.contains("withheld by the collector"));
    }
}
