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
//!   tier `kernel-tv`; a re-check failure DEMOTES to `structural` with a loud
//!   `tv-refused` note (its own class — never conflated with a fragment skip),
//!   and never fails the compile (this lane produces no binary).
//! * Tier honesty (docs/TCB.md row binds): `kernel-tv` records a kernel-decided
//!   defeq of two MINTED Nat-mod-2^w denotations — trusted, unmechanized
//!   checker-spec maps with correlated authorship — and carrier faithfulness is
//!   NOT established (G3). Every kernel-tv row keeps `body_gate: ungated`, so a
//!   tier-ignorant consumer still refuses. Unknown tier values must be treated
//!   as ungated by consumers (fail-closed default).
//!
//! # Call-edge linking (IR-5)
//!
//! Assemble pass 2 minted a fail-closed bodyless `local-unlowered` declaration
//! for every Rust→Clean call edge. [`link_clean_origin_edges`] re-points those
//! edges onto the appended definitions — post-append, per the design's chosen
//! shape — under three guards, each disclosed:
//!
//! * matching is by the ledger's exact `def_path` spelling (the collection
//!   normalizes with `with_no_trimmed_paths`), ambiguity refuses;
//! * every edge is arity-guarded (`results.len()` / `args.len()` against the
//!   target signature) — an `|nres:`-split site that binds a different result
//!   count stays declared, disclosed per edge;
//! * every touched function must pass the EXECUTABLE remap-shape certificate
//!   (`remap_certificate::certify_remap_shape` — discriminants, results,
//!   blocks, params, spans all unchanged; only callee ids may move), making
//!   "pass 3 writes callee ids and nothing else" a checked property rather
//!   than the argument pass 2 rides on. A certificate failure restores the
//!   function untouched and discloses.

use trust_ir::ty::FuncTy;
use trust_ir::value::{FuncId, FuncTyId};
use trust_ir::{Constant, Function, Inst, Module, Producer};
use trust_ir::{SpecInvariant, SpecModule};

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

/// The faithfulness tier of a recorded row (design §4). Ordered weakest-first;
/// none of these licenses codegen — that is tier `gate`, which does not exist
/// yet and is the entry condition for value production.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum CleanOriginTier {
    /// Emitted from the sealed plan, per-function validation passed, no
    /// symbolic gate on the body.
    Structural,
    /// Additionally: the CIC kernel decided `CleanTV.<fn>.denotes` — defeq of
    /// two minted denotations at Nat mod 2^w. NOT carrier faithfulness (G3);
    /// still `body_gate: ungated`.
    KernelTv,
}

impl CleanOriginTier {
    pub fn tag(self) -> &'static str {
        match self {
            CleanOriginTier::Structural => "structural",
            CleanOriginTier::KernelTv => "kernel-tv",
        }
    }
}

/// One Clean-origin def whose trust-ir spelling was emitted under a freshly
/// re-earned kernel verdict (for the emitted MIR body — see the tier wording).
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
    /// The signature as `trust-clean-ir` derives it from the carrier
    /// signature. Interned into `module.func_types` at append.
    pub signature: FuncTy,
    /// The emitted function. `id`/`ty` are placeholders until append.
    pub function: Function,
    /// The kernel-tv payload, when the mint's fragment covered the shape.
    pub tv: Option<CleanTvMint>,
    /// Why kernel-tv was not attempted (fragment skip, with v7/D3 options).
    pub tv_note: Option<String>,
}

/// One Clean-origin def the producer could not spell — a capability gap, never
/// a verdict. `reason` carries fix options (v7/D3).
pub struct CleanOriginIrSkip {
    pub def_index: u32,
    pub def_path: String,
    pub clean_name: String,
    pub shape: &'static str,
    pub reason: String,
}

/// Outcome per Clean-origin def, in registry order.
pub enum CleanOriginIrOutcome {
    Emitted(CleanOriginIrRecord),
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
    /// `tv_note` for structural rows (fragment skip with options), or the loud
    /// `tv-refused:` note when the kernel re-check demoted the row.
    pub tv_note: Option<String>,
}

/// One re-pointed (or refused) declaration edge set, for disclosure/coverage.
pub struct LinkedRow {
    pub decl_func_id: u32,
    pub decl_key: String,
    pub target_func_id: u32,
    pub def_path: String,
    pub edges_repointed: u32,
    /// Per-edge refusals (arity guard) and per-function certificate refusals,
    /// each disclosed rather than silently linked or silently skipped.
    pub refusals: Vec<String>,
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
        }
    }
}

/// Append the collected Clean-origin functions to the assembled module and
/// install the in-band disclosure.
pub fn append_clean_origin(
    module: &mut Module,
    outcomes: Vec<CleanOriginIrOutcome>,
    errors: &mut Vec<String>,
) -> CleanOriginJoinSummary {
    let mut summary = CleanOriginJoinSummary {
        recorded: true,
        emitted: Vec::new(),
        skipped: Vec::new(),
        linked: Vec::new(),
        general: Vec::new(),
        general_functions: Vec::new(),
    };
    if module.spec_modules.iter().any(|spec| spec.name == CLEAN_ORIGIN_DISCLOSURE_NAME) {
        errors.push(format!(
            "reserved clean-origin disclosure name collision: {CLEAN_ORIGIN_DISCLOSURE_NAME}"
        ));
        return summary;
    }

    for outcome in outcomes {
        match outcome {
            CleanOriginIrOutcome::Emitted(record) => {
                // A DEFINED (body-bearing) function already claiming this
                // def_path would mean a THIR body and a Clean body claim one
                // def — a bijection break, refused (demoted to a skip).
                if module
                    .functions
                    .iter()
                    .any(|f| !f.is_declaration() && f.name == record.def_path)
                {
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
                        let (tier, tv_note) = match &record.tv {
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
                        };
                        let ty = intern_func_ty(module, &record.signature);
                        let id = FuncId::new(
                            u32::try_from(module.functions.len())
                                .expect("function count exceeds u32"),
                        );
                        let mut function = record.function;
                        function.id = id;
                        function.ty = ty;
                        function.producer = Some(Producer::Clean);
                        module.functions.push(function);
                        summary.emitted.push(EmittedRow {
                            def_index: record.def_index,
                            def_path: record.def_path,
                            clean_name: record.clean_name,
                            shape: record.shape,
                            func_id: id.index(),
                            tier,
                            tv_note,
                        });
                    }
                    Err(reason) => {
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
            CleanOriginIrOutcome::Skipped(skip) => {
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
            GeneralOutcome::Skipped { reason } => summary.general.push((
                row.clean_name.clone(),
                "skipped",
                false,
                reason.clone(),
            )),
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
    let refuse = |summary: &mut CleanOriginJoinSummary,
                  compiled: &[(String, bool)],
                  reason: String| {
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
    if !src.structs.is_empty()
        || !src.enums.is_empty()
        || !src.records.is_empty()
        || !src.closure_types.is_empty()
        || !src.types.is_empty()
        || !src.spec_modules.is_empty()
        || !src.predicates.is_empty()
        || !src.universes.is_empty()
    {
        refuse(
            summary,
            &compiled_names,
            "general module carries type/spec/predicate tables this merge does not yet remap (v1 refuses rather than corrupting ids) — report which construct produced them"
                .to_string(),
        );
        return;
    }
    // Name-identity guard: a general function name colliding with ANY existing
    // function name refuses the whole module (partial merges break internal
    // calls; renaming would detach the disclosure identity).
    {
        let existing: std::collections::BTreeSet<&str> =
            dst.functions.iter().map(|f| f.name.as_str()).collect();
        if let Some(clash) = src.functions.iter().find(|f| existing.contains(f.name.as_str())) {
            refuse(
                summary,
                &compiled_names,
                format!(
                    "general function name `{}` collides with an existing module row — refusing the whole general module",
                    clash.name
                ),
            );
            return;
        }
    }

    // Id remaps: FuncId by offset, FuncTyId by equality-interning, GlobalId by
    // append offset. Spans/scopes are STRIPPED (v1): their file ids index the
    // general module's own file table, which this merge does not carry.
    let func_offset = u32::try_from(dst.functions.len()).expect("function count exceeds u32");
    // Function-type interning with RECURSIVE Ty::Func remapping (v1.1): a
    // higher-order signature (clean-compiler's apply/closure runtime spells
    // callables as Ty::Func(src-relative id)) is remapped id-by-id into the
    // destination table. Table-referencing variants other than Func
    // (Struct/Enum/Record/Closure/Array/Set/Sequence/Refine) cannot appear
    // here — the empty-tables belt above already refused any module that
    // could give their ids a referent — but the walk still names one on
    // sight rather than trusting that argument twice.
    let mut functy_map: Vec<FuncTyId> = Vec::with_capacity(src.func_types.len());
    {
        let mut memo: Vec<Option<FuncTyId>> = vec![None; src.func_types.len()];
        let mut in_progress: Vec<bool> = vec![false; src.func_types.len()];
        let mut failure: Option<String> = None;
        for index in 0..src.func_types.len() {
            match remap_func_ty_id(index, &src.func_types, dst, &mut memo, &mut in_progress) {
                Ok(id) => functy_map.push(id),
                Err(reason) => {
                    failure = Some(reason);
                    break;
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
    if let Some(carrier) = src.functions.iter().find(|f| {
        !f.is_declaration() && format!("{:?}", f.blocks).contains("Func(")
    }) {
        refuse(
            summary,
            &compiled_names,
            format!(
                "general function `{}` carries a function-typed value inside its body —                  v1.1 remaps Ty::Func in signatures only; higher-order value flow is                  refused rather than silently retyped. Options: keep the declaration                  first-order, or wait for the body-walk remap increment.",
                carrier.name
            ),
        );
        return;
    }
    let global_offset = u32::try_from(dst.globals.len()).expect("global count exceeds u32");
    for global in src.globals.drain(..) {
        dst.globals.push(global);
    }
    let defined: Vec<String> = src
        .functions
        .iter()
        .filter(|f| !f.is_declaration())
        .map(|f| f.name.clone())
        .collect();
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
                    Inst::Call { callee, .. } => {
                        *callee = FuncId::new(func_offset + callee.index());
                    }
                    Inst::CallIndirect { sig, .. } => {
                        *sig = functy_map[sig.index() as usize];
                    }
                    Inst::Const { value: Constant::FnDef(id), .. } => {
                        *id = FuncId::new(func_offset + id.index());
                    }
                    Inst::GlobalAddr { global } => {
                        *global =
                            trust_ir::value::GlobalId::new(global_offset + global.index());
                    }
                    _ => {}
                }
            }
        }
        dst.functions.push(function);
    }
    summary.general_functions = defined;
    for (name, tv) in compiled_names {
        summary.general.push((name, "compiled", tv, String::new()));
    }
}

/// Remap one src-relative `FuncTyId` into `dst`'s table, remapping every
/// embedded `Ty::Func` id recursively (memoized; a self-referential signature
/// refuses — it could only arise from a corrupted table and has no finite
/// spelling).
fn remap_func_ty_id(
    index: usize,
    src_func_types: &[FuncTy],
    dst: &mut Module,
    memo: &mut Vec<Option<FuncTyId>>,
    in_progress: &mut Vec<bool>,
) -> Result<FuncTyId, String> {
    if let Some(id) = memo[index] {
        return Ok(id);
    }
    if in_progress[index] {
        return Err(format!(
            "general func_types[{index}] is self-referential through Ty::Func — refusing              (no finite signature spells this; report which construct produced it)"
        ));
    }
    in_progress[index] = true;
    let src_ty = src_func_types[index].clone();
    let mut remapped = FuncTy {
        params: Vec::with_capacity(src_ty.params.len()),
        returns: Vec::with_capacity(src_ty.returns.len()),
        is_vararg: src_ty.is_vararg,
    };
    for ty in &src_ty.params {
        remapped.params.push(remap_ty(ty, src_func_types, dst, memo, in_progress)?);
    }
    for ty in &src_ty.returns {
        remapped.returns.push(remap_ty(ty, src_func_types, dst, memo, in_progress)?);
    }
    in_progress[index] = false;
    let id = intern_func_ty(dst, &remapped);
    memo[index] = Some(id);
    Ok(id)
}

/// Rewrite every src-relative id embedded in a type. Only `Ty::Func` can
/// carry one here (the empty-tables belt refused every other table), and the
/// recursive containers are walked in full — including `Tuple` and `Vector`,
/// which the v1 refusal check missed.
fn remap_ty(
    ty: &trust_ir::ty::Ty,
    src_func_types: &[FuncTy],
    dst: &mut Module,
    memo: &mut Vec<Option<FuncTyId>>,
    in_progress: &mut Vec<bool>,
) -> Result<trust_ir::ty::Ty, String> {
    use trust_ir::ty::Ty;
    Ok(match ty {
        Ty::Func(id) => {
            let index = id.index() as usize;
            if index >= src_func_types.len() {
                return Err(format!(
                    "general signature references func_types[{index}] which the module                      does not define — refusing a dangling id"
                ));
            }
            Ty::Func(remap_func_ty_id(index, src_func_types, dst, memo, in_progress)?)
        }
        Ty::Vector(inner, lanes) => Ty::Vector(
            Box::new(remap_ty(inner, src_func_types, dst, memo, in_progress)?),
            *lanes,
        ),
        Ty::Tuple(elems) => Ty::Tuple(
            elems
                .iter()
                .map(|e| remap_ty(e, src_func_types, dst, memo, in_progress))
                .collect::<Result<Vec<_>, _>>()?,
        ),
        Ty::Ref(inner) => {
            Ty::Ref(Box::new(remap_ty(inner, src_func_types, dst, memo, in_progress)?))
        }
        Ty::RefMut(inner) => {
            Ty::RefMut(Box::new(remap_ty(inner, src_func_types, dst, memo, in_progress)?))
        }
        Ty::PtrConst(inner) => {
            Ty::PtrConst(Box::new(remap_ty(inner, src_func_types, dst, memo, in_progress)?))
        }
        Ty::PtrMut(inner) => {
            Ty::PtrMut(Box::new(remap_ty(inner, src_func_types, dst, memo, in_progress)?))
        }
        Ty::Rc(inner) => {
            Ty::Rc(Box::new(remap_ty(inner, src_func_types, dst, memo, in_progress)?))
        }
        Ty::Struct(_) | Ty::Enum(_) | Ty::Record(_) | Ty::Closure(_) | Ty::Array(..)
        | Ty::Set(..) | Ty::Sequence(_) | Ty::Refine(..) => {
            return Err(format!(
                "general signature carries a table-referencing type ({ty:?}) whose table                  the merge requires empty — refusing (the belt above should have caught                  the table; report this pairing)"
            ));
        }
        other => other.clone(),
    })
}

/// IR-5: re-point the caller's `local-unlowered` declaration edges onto the
/// appended Clean-origin definitions. Runs after [`append_clean_origin`];
/// records outcomes into `summary.linked` and extends the installed
/// disclosure. Fail-closed at every step: no match = stays declared; ambiguous
/// match = refused + disclosed; guard/certificate failure = edge or function
/// untouched + disclosed.
pub fn link_clean_origin_edges(
    module: &mut Module,
    decl_keys: &[(FuncId, String)],
    summary: &mut CleanOriginJoinSummary,
    errors: &mut Vec<String>,
) {
    if summary.emitted.is_empty() {
        return;
    }
    // The match map: declaration FuncId -> appended definition FuncId, keyed
    // by the ledger's `local-unlowered:{def_path}` dedup key (the key may
    // carry `|ret:`/`|nres:` split suffixes — the base def_path decides the
    // match; per-edge guards decide each site).
    let mut matches: Vec<(FuncId, String, u32, String)> = Vec::new();
    for (decl_id, key) in decl_keys {
        let Some(rest) = key.strip_prefix("local-unlowered:") else { continue };
        let base = rest.split('|').next().unwrap_or(rest);
        let candidates: Vec<&EmittedRow> =
            summary.emitted.iter().filter(|row| row.def_path == base).collect();
        match candidates.as_slice() {
            [] => {}
            [row] => {
                matches.push((*decl_id, key.clone(), row.func_id, row.def_path.clone()));
            }
            many => {
                errors.push(format!(
                    "clean-origin link refused: declaration key `{key}` matches {} appended \
                     definitions — a def_path collision among Clean-origin rows",
                    many.len()
                ));
                return;
            }
        }
    }
    if matches.is_empty() {
        return;
    }

    for (decl_id, decl_key, target_index, def_path) in matches {
        let target_id = FuncId::new(target_index);
        let target_sig = {
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
            sig.clone()
        };
        let mut row = LinkedRow {
            decl_func_id: decl_id.index(),
            decl_key,
            target_func_id: target_index,
            def_path,
            edges_repointed: 0,
            refusals: Vec::new(),
        };
        for index in 0..module.functions.len() {
            if module.functions[index].producer == Some(Producer::Clean) {
                continue; // Clean rows carry no Rust edges; and never rewrite them.
            }
            if module.functions[index].is_declaration() {
                continue;
            }
            let before = module.functions[index].clone();
            let (repointed, refusals) =
                repoint_edges(&mut module.functions[index], decl_id, target_id, &target_sig);
            if repointed == 0 && refusals.is_empty() {
                continue;
            }
            // The EXECUTABLE certificate: only callee ids may have moved.
            if let Err(reason) =
                crate::remap_certificate::certify_remap_shape(&before, &module.functions[index])
            {
                let name = before.name.clone();
                module.functions[index] = before;
                row.refusals.push(format!(
                    "function `{name}`: remap-shape certificate refused the rewrite \
                     ({reason}); function restored untouched"
                ));
                continue;
            }
            row.edges_repointed += repointed;
            row.refusals.extend(refusals);
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
                     \"target_func_id\":{},\"def_path\":\"{}\",\"edges_repointed\":{},\
                     \"refusals\":[{}]}}",
                    json_escape_min(&row.decl_key),
                    row.target_func_id,
                    json_escape_min(&row.def_path),
                    row.edges_repointed,
                    row.refusals
                        .iter()
                        .map(|r| format!("\"{}\"", json_escape_min(r)))
                        .collect::<Vec<_>>()
                        .join(","),
                ),
            ));
        }
    }
}

/// Rewrite the callee ids inside one function: `Inst::Call { callee }` and
/// `Constant::FnDef(id)` equal to `decl_id` become `target_id`, each call edge
/// guarded on arity against the target signature. Returns (repointed count,
/// per-edge refusals).
fn repoint_edges(
    function: &mut Function,
    decl_id: FuncId,
    target_id: FuncId,
    target_sig: &FuncTy,
) -> (u32, Vec<String>) {
    let mut repointed = 0u32;
    let mut refusals = Vec::new();
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
                    *callee = target_id;
                    repointed += 1;
                }
                Inst::Const { value: Constant::FnDef(id), .. } if *id == decl_id => {
                    *id = target_id;
                    repointed += 1;
                }
                _ => {}
            }
        }
    }
    (repointed, refusals)
}

fn install_disclosure(module: &mut Module, summary: &CleanOriginJoinSummary) {
    let mut disclosure = SpecModule::new(CLEAN_ORIGIN_DISCLOSURE_NAME);
    for row in &summary.emitted {
        let tier_fields = match row.tier {
            CleanOriginTier::Structural => "\"tier\":\"structural\"".to_string(),
            CleanOriginTier::KernelTv => "\"tier\":\"kernel-tv\",\
                 \"judgment\":\"denotation-at-Nat-mod-2^w\",\
                 \"carrier_faithfulness\":\"not-established\""
                .to_string(),
        };
        let tv_note = match &row.tv_note {
            Some(note) => format!(",\"tv_note\":\"{}\"", json_escape_min(note)),
            None => String::new(),
        };
        disclosure.invariants.push(SpecInvariant::new(
            format!("fn:{}", row.func_id),
            // The verdict wording binds to the MIR body — the trust-ir
            // spelling itself is UNGATED below tier `gate`, and a consumer
            // must read it that way (design §4). `body_gate: ungated` stays on
            // EVERY tier so a tier-ignorant consumer still refuses.
            format!(
                "{{\"schema\":\"trust.clean-origin-disclosure.v1\",\
                 \"def_path\":\"{}\",\"clean_name\":\"{}\",\"shape\":\"{}\",\
                 {tier_fields},\"body_gate\":\"ungated\",\
                 \"mir_gate\":\"kernel Faithful earned for the emitted MIR \
                 body at the finalize seam; the trust-ir spelling is emitted \
                 from the sealed plan and is NOT gated at the carrier — do not \
                 hand it to codegen\"{tv_note}}}",
                json_escape_min(&row.def_path),
                json_escape_min(&row.clean_name),
                row.shape,
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
        let tier_fields = match row.tier {
            CleanOriginTier::Structural => "\"tier\": \"structural\"".to_string(),
            CleanOriginTier::KernelTv => "\"tier\": \"kernel-tv\", \
                 \"judgment\": \"denotation-at-Nat-mod-2^w\", \
                 \"carrier_faithfulness\": \"not-established\""
                .to_string(),
        };
        let tv_note = match &row.tv_note {
            Some(note) => format!(", \"tv_note\": \"{}\"", json_escape_min(note)),
            None => String::new(),
        };
        let _ = writeln!(
            out,
            "      {{\"def_index\": {}, \"def_path\": \"{}\", \"clean_name\": \"{}\", \
             \"shape\": \"{}\", {tier_fields}, \"func_id\": {}{tv_note}}}{comma}",
            row.def_index,
            json_escape_min(&row.def_path),
            json_escape_min(&row.clean_name),
            row.shape,
            row.func_id,
        );
    }
    let _ = writeln!(out, "    ],");
    let _ = writeln!(out, "    \"skipped\": [");
    for (i, (def_index, def_path, clean_name, shape, reason)) in
        summary.skipped.iter().enumerate()
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
            "      {{\"decl_key\": \"{}\", \"target_func_id\": {}, \"def_path\": \"{}\", \
             \"edges_repointed\": {}, \"refusals\": [{}]}}{comma}",
            json_escape_min(&row.decl_key),
            row.target_func_id,
            json_escape_min(&row.def_path),
            row.edges_repointed,
            row.refusals
                .iter()
                .map(|r| format!("\"{}\"", json_escape_min(r)))
                .collect::<Vec<_>>()
                .join(", "),
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
    let _ = writeln!(out, "    ]");
    let _ = write!(out, "  }}");
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_ir::ty::Ty;

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
        let module = mb.build();
        let function = module.functions.into_iter().next().expect("one function built");
        CleanOriginIrRecord {
            def_index: nth,
            def_path: format!("probe_def_{nth}"),
            clean_name: format!("probeDef{nth}"),
            shape: "projection",
            signature: FuncTy { params: vec![Ty::U64], returns: vec![Ty::U64], is_vararg: false },
            function,
            tv: None,
            tv_note: None,
        }
    }

    #[test]
    fn append_mints_dense_ids_and_interns_signatures_once() {
        let mut module = Module::new("crate_under_test");
        let existing_ty = module.add_func_type(FuncTy {
            params: Vec::new(),
            returns: Vec::new(),
            is_vararg: false,
        });
        module.add_function(Function::new(
            FuncId::new(0),
            "rust_fn",
            existing_ty,
            trust_ir::BlockId::new(0),
        ));

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

    #[test]
    fn invalid_emitted_function_is_demoted_to_a_skip_never_published() {
        let mut module = Module::new("crate_under_test");
        let mut record = projection_record(3);
        record.function.blocks.clear();
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
    fn caller_with_declared_edge() -> (Module, Vec<(FuncId, String)>) {
        let mut mb = trust_ir_build::ModuleBuilder::new("caller_crate");
        let caller_ft = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
        let decl_ft = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
        // Function 0: the Rust caller; its call targets FuncId 1 (the decl).
        let mut fb = mb.function("calls_clean", caller_ft);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::U64);
        fb.switch_to_block(entry);
        let result = fb.call(FuncId::new(1), vec![x]);
        fb.ret(vec![result]);
        fb.build();
        // Function 1: the bodyless local-unlowered declaration.
        let mut module = mb.build();
        let mut decl =
            Function::new(FuncId::new(1), "m::clean_def", decl_ft, trust_ir::BlockId::new(0));
        decl.blocks.clear();
        module.functions.push(decl);
        let decl_keys = vec![(FuncId::new(1), "local-unlowered:m::clean_def".to_string())];
        (module, decl_keys)
    }

    fn clean_def_record_for_link() -> CleanOriginIrRecord {
        let mut record = projection_record(42);
        record.def_path = "m::clean_def".to_string();
        record.function.name = "cleanDef".to_string();
        record
    }

    #[test]
    fn link_repoints_a_guard_passing_edge_and_certifies_shape() {
        let (mut module, decl_keys) = caller_with_declared_edge();
        let mut errors = Vec::new();
        let mut summary = append_clean_origin(
            &mut module,
            vec![CleanOriginIrOutcome::Emitted(clean_def_record_for_link())],
            &mut errors,
        );
        assert!(errors.is_empty(), "{errors:?}");
        let appended_id = summary.emitted[0].func_id;
        link_clean_origin_edges(&mut module, &decl_keys, &mut summary, &mut errors);
        assert!(errors.is_empty(), "{errors:?}");
        assert_eq!(summary.linked.len(), 1);
        let row = &summary.linked[0];
        assert_eq!(row.edges_repointed, 1, "refusals: {:?}", row.refusals);
        assert!(row.refusals.is_empty());
        // The caller's call now targets the appended definition.
        let caller = &module.functions[0];
        let mut found = false;
        for block in &caller.blocks {
            for node in &block.body {
                if let Inst::Call { callee, .. } = &node.inst {
                    assert_eq!(callee.index(), appended_id);
                    found = true;
                }
            }
        }
        assert!(found, "the call edge exists and was re-pointed");
        // The orphaned declaration row stays (dense ids), now edge-free.
        assert!(module.functions.iter().any(|f| f.is_declaration()));
        // Disclosure carries the link row.
        let disclosure = module
            .spec_modules
            .iter()
            .find(|s| s.name == CLEAN_ORIGIN_DISCLOSURE_NAME)
            .expect("disclosure");
        assert!(disclosure.invariants.iter().any(|inv| inv.name.starts_with("linked:")));
    }

    #[test]
    fn link_refuses_an_arity_mismatched_edge_and_leaves_it_declared() {
        let (mut module, decl_keys) = caller_with_declared_edge();
        let mut record = clean_def_record_for_link();
        // Sabotage the signature: the Clean def now takes 2 params, while the
        // caller passes 1 — the per-edge guard must refuse and disclose.
        record.signature =
            FuncTy { params: vec![Ty::U64, Ty::U64], returns: vec![Ty::U64], is_vararg: false };
        // Keep the function body consistent with the new signature so
        // per-function validation still passes.
        let mut mb = trust_ir_build::ModuleBuilder::new("probe2");
        let ft = mb.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
        let mut fb = mb.function("cleanDef", ft);
        let entry = fb.create_block();
        let a = fb.add_block_param(entry, Ty::U64);
        let _b = fb.add_block_param(entry, Ty::U64);
        fb.switch_to_block(entry);
        fb.ret(vec![a]);
        fb.build();
        record.function = mb.build().functions.into_iter().next().unwrap();
        let mut errors = Vec::new();
        let mut summary = append_clean_origin(
            &mut module,
            vec![CleanOriginIrOutcome::Emitted(record)],
            &mut errors,
        );
        assert!(errors.is_empty(), "{errors:?}");
        link_clean_origin_edges(&mut module, &decl_keys, &mut summary, &mut errors);
        assert!(errors.is_empty(), "{errors:?}");
        let row = &summary.linked[0];
        assert_eq!(row.edges_repointed, 0);
        assert_eq!(row.refusals.len(), 1);
        assert!(row.refusals[0].contains("passes 1 argument(s)"));
        // The refused edge still targets the declaration.
        let caller = &module.functions[0];
        let mut still_declared = false;
        for block in &caller.blocks {
            for node in &block.body {
                if let Inst::Call { callee, .. } = &node.inst {
                    assert_eq!(callee.index(), 1, "the refused edge stays declared");
                    still_declared = true;
                }
            }
        }
        assert!(still_declared);
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
        let shadow = mb.build();
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
        mb.build()
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
        let rust_ty = module.add_func_type(FuncTy {
            params: Vec::new(),
            returns: Vec::new(),
            is_vararg: false,
        });
        module.add_function(Function::new(
            FuncId::new(0),
            "rust_fn",
            rust_ty,
            trust_ir::BlockId::new(0),
        ));

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
        let caller = module
            .functions
            .iter()
            .find(|f| f.name == "gen_caller")
            .expect("caller merged");
        let callee_id = module
            .functions
            .iter()
            .find(|f| f.name == "gen_callee")
            .expect("callee merged")
            .id;
        let repointed = caller.blocks.iter().flat_map(|b| &b.body).any(|node| {
            matches!(&node.inst, Inst::Call { callee, .. } if *callee == callee_id)
        });
        assert!(repointed, "internal call must be repointed by the FuncId offset");
        // Rows disclose, defined names recorded, disclosure carries the tier.
        assert_eq!(summary.general.len(), 3);
        assert!(summary.general.iter().any(|(n, d, tv, _)| n.as_str() == "genCallee"
            && *d == "compiled"
            && *tv));
        assert!(summary
            .general
            .iter()
            .any(|(n, d, _, _)| n.as_str() == "genTheorem" && *d == "not-computational"));
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

    #[test]
    fn general_name_collision_refuses_the_whole_batch() {
        let mut module = Module::new("crate_under_test");
        let ty = module.add_func_type(FuncTy {
            params: Vec::new(),
            returns: Vec::new(),
            is_vararg: false,
        });
        module.add_function(Function::new(
            FuncId::new(0),
            "gen_callee", // collides with the general module's first function
            ty,
            trust_ir::BlockId::new(0),
        ));
        let mut errors = Vec::new();
        let summary = append_clean_origin(
            &mut module,
            vec![general_outcome(Some(general_two_fn_module()))],
            &mut errors,
        );
        assert!(errors.is_empty());
        assert_eq!(module.functions.len(), 1, "nothing merged on collision");
        let refused: Vec<_> = summary
            .general
            .iter()
            .filter(|(_, d, _, _)| *d == "merge-refused")
            .collect();
        assert_eq!(refused.len(), 2, "BOTH compiled rows refuse together");
        assert!(refused[0].3.contains("collides"));
        assert!(summary.general_functions.is_empty());
    }

    #[test]
    fn general_proof_channels_and_table_content_each_refuse() {
        // Belt 1: populated proof channels (the collector must strip).
        let mut src = general_two_fn_module();
        src.functions[0].summary =
            Some(trust_ir::FunctionSummary::new());
        let mut module = Module::new("crate_under_test");
        let mut errors = Vec::new();
        let summary =
            append_clean_origin(&mut module, vec![general_outcome(Some(src))], &mut errors);
        assert!(module.functions.is_empty());
        assert!(summary
            .general
            .iter()
            .any(|(_, d, _, r)| *d == "merge-refused" && r.contains("proof channels")));

        // Belt 2: a table this merge does not remap (v1).
        let mut src = general_two_fn_module();
        src.spec_modules.push(SpecModule::new("stray"));
        let mut module = Module::new("crate_under_test");
        let mut errors = Vec::new();
        let summary =
            append_clean_origin(&mut module, vec![general_outcome(Some(src))], &mut errors);
        assert!(module.functions.is_empty());
        assert!(summary
            .general
            .iter()
            .any(|(_, d, _, r)| *d == "merge-refused" && r.contains("does not yet remap")));

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
        assert!(summary
            .general
            .iter()
            .any(|(_, d, _, r)| *d == "merge-refused" && r.contains("target_info mismatch")));
    }

    #[test]
    fn general_batch_refusal_without_module_discloses_every_compiled_row() {
        let mut module = Module::new("crate_under_test");
        let mut errors = Vec::new();
        let summary = append_clean_origin(&mut module, vec![general_outcome(None)], &mut errors);
        assert!(errors.is_empty());
        assert!(module.functions.is_empty());
        assert_eq!(summary.general.len(), 3);
        let refused: Vec<_> = summary
            .general
            .iter()
            .filter(|(_, d, _, _)| *d == "merge-refused")
            .collect();
        assert_eq!(refused.len(), 2);
        assert!(refused[0].3.contains("withheld by the collector"));
    }
}
