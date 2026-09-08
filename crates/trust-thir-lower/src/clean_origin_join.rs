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
//!   `gate` rung exists only for WrappingBinOp Add/Sub/Mul at exact
//!   UInt8/16/32/64: an independent reflector inspected the actual Function,
//!   the Clean kernel decided carrier-level defeq, and this seam authenticated
//!   a private digest-bound token before publishing it.
//!
//! # Call-edge linking (IR-5)
//!
//! Assemble pass 2 minted a fail-closed bodyless `local-unlowered` declaration
//! for every admitted Rust→Clean call edge. [`link_clean_origin_edges`] re-points
//! those edges onto the appended definitions — post-append, per the design's
//! chosen shape — under five guards, each disclosed:
//!
//! * matching requires the ledger's exact same-crate source `DefIndex`; the
//!   normalized `def_path` is checked only as corroborating display identity,
//!   and a same-path/different-identity candidate is fatal rather than linkable;
//! * the bodyless declaration and appended definition must name the same
//!   calling convention; a convention change stays declared and is disclosed
//!   before any direct or reified edge is considered;
//! * every edge is arity-guarded (`results.len()` / `args.len()` against the
//!   target signature) — an `|nres:`-split site that binds a different result
//!   count stays declared, disclosed per edge;
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

use std::collections::BTreeSet;

use trust_clean_ir_gate::TrustIrFaithful;
use trust_ir::ty::FuncTy;
use trust_ir::value::{FuncId, FuncTyId, TyId};
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
    /// Private permission for the exact WrappingBinOp Function/signature.
    /// Must be `Some` exactly for shape `wrapping-binop`; missing, surplus, or
    /// stale evidence is a fatal semantic-finalization error, never a demotion.
    pub gate: Option<TrustIrFaithful>,
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
    /// SHA-256 subject identity authenticated after the Function received its
    /// final published id, type id, and Clean producer stamp.
    pub gate_subject_digest: Option<String>,
    /// Exact Clean carrier named by the authenticated gate.
    pub gate_carrier: Option<&'static str>,
    /// Kernel method named by the authenticated gate.
    pub gate_method: Option<&'static str>,
    /// `tv_note` for structural rows (fragment skip with options), or the loud
    /// `tv-refused:` note when the kernel re-check demoted the row.
    pub tv_note: Option<String>,
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
    /// Declaration-level calling-convention refusals, per-edge refusals (call arity or
    /// function-pointer signature), and per-function certificate refusals, each disclosed
    /// rather than silently linked or skipped.
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
    /// General-lane definitions recorded under the `general::` namespace because their own
    /// name was held by another lane's row: (name in the general module, recorded name).
    pub general_renamed: Vec<(String, String)>,
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
        general_renamed: Vec::new(),
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
        if let CleanOriginIrOutcome::Emitted(record) = outcome {
            if !seen_def_paths.insert(record.def_path.clone()) {
                duplicate_def_paths.insert(record.def_path.clone());
            }
            if !seen_def_indices.insert(record.def_index) {
                duplicate_def_indices.insert(record.def_index);
            }
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

    for outcome in outcomes {
        match outcome {
            CleanOriginIrOutcome::Emitted(record) => {
                if duplicate_def_paths.contains(&record.def_path)
                    || duplicate_def_indices.contains(&record.def_index)
                {
                    continue;
                }
                let targeted = record.shape == "wrapping-binop";
                // The gate token is an exact-set contract, not optional
                // metadata. Authenticate while the Function still carries the
                // placeholder ids used at mint time; append mutates those ids.
                // Missing/surplus/stale evidence is a semantic-finalization
                // failure via `errors`, never a skip or tier demotion.
                match (targeted, record.gate.as_ref()) {
                    (true, Some(gate)) => {
                        if let Err(refusal) = gate.authenticate(
                            &record.clean_name,
                            record.def_index,
                            &record.def_path,
                            &record.signature,
                            &record.function,
                        ) {
                            errors.push(format!(
                                "fatal clean-origin carrier-gate disagreement for targeted \
                                     wrapping-binop `{}`: {}. The row was not published and was \
                                     not demoted.",
                                record.clean_name,
                                refusal.note()
                            ));
                            continue;
                        }
                    }
                    (true, None) => {
                        errors.push(format!(
                            "fatal clean-origin carrier-gate evidence missing for targeted \
                                 wrapping-binop `{}`; the row was not published and was not \
                                 demoted",
                            record.clean_name
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
                    (false, None) => {}
                }
                // A DEFINED (body-bearing) function already claiming this
                // def_path would mean a THIR body and a Clean body claim one
                // def — a bijection break, refused (demoted to a skip).
                if module.functions.iter().any(|f| !f.is_declaration() && f.name == record.def_path)
                {
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
                        let id = FuncId::new(
                            u32::try_from(module.functions.len())
                                .expect("function count exceeds u32"),
                        );
                        let mut function = record.function.clone();
                        function.id = id;
                        function.ty = ty;
                        function.producer = Some(Producer::Clean);
                        let (gate_subject_digest, gate_carrier, gate_method) = if targeted {
                            let gate = record
                                .gate
                                .as_ref()
                                .expect("target gate presence was checked above");
                            let published = match gate.authenticate_published(
                                &record.clean_name,
                                record.def_index,
                                &record.def_path,
                                &record.signature,
                                &record.function,
                                &function,
                            ) {
                                Ok(published) => published,
                                Err(refusal) => {
                                    errors.push(format!(
                                        "fatal clean-origin final-subject authentication \
                                         disagreement for targeted wrapping-binop `{}`: {}. \
                                         The row was not published and was not demoted.",
                                        record.clean_name,
                                        refusal.note()
                                    ));
                                    continue;
                                }
                            };
                            (
                                Some(published.subject_digest().to_string()),
                                Some(published.carrier_tag()),
                                Some(published.method_tag()),
                            )
                        } else {
                            (None, None, None)
                        };
                        if insert_ty {
                            module.func_types.push(record.signature.clone());
                        }
                        module.functions.push(function);
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
            CleanOriginIrOutcome::Skipped(skip) => {
                if skip.shape == "wrapping-binop" {
                    errors.push(format!(
                        "fatal clean-origin targeted wrapping-binop `{}` arrived at append as a \
                         skip ({}) — targeted precursor/gate disagreements are never skipped, \
                         rerouted, or demoted",
                        skip.clean_name, skip.reason
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
    {
        refuse(
            summary,
            &compiled_names,
            "general module carries type/spec/predicate tables this merge does not yet remap (v1 refuses rather than corrupting ids) — report which construct produced them"
                .to_string(),
        );
        return;
    }
    // Name-identity guard. A general DECLARATION whose name an existing row already
    // holds still refuses the whole module (partial merges break internal calls, and a
    // declaration has no body of its own to record). A general DEFINITION whose name is
    // held by another lane's row — measured on the Clean corpus (2026-08-30): every
    // Nat-recursion def, whose value-producing MIR-lane row already sits in the module
    // under the plain Clean name, so the general batch that carried its DIRECT trust-ir
    // spelling was refused wholesale and the Lean side stopped at 86.4% — is recorded
    // under the `general::` namespace instead. Nothing is detached: the disclosure row
    // is keyed by `clean_name`, its `reason` names the recorded row, and tier `general`
    // rows are by design never linked from Rust (IR-5 repoints planner rows only), so
    // the module name of a general row is resolved by no one. Internal calls are
    // `FuncId` edges, untouched by the rename.
    let mut renamed: Vec<(String, String)> = Vec::new();
    {
        let existing: std::collections::BTreeSet<String> =
            dst.functions.iter().map(|f| f.name.clone()).collect();
        if let Some(clash) =
            src.functions.iter().find(|f| f.is_declaration() && existing.contains(&f.name))
        {
            refuse(
                summary,
                &compiled_names,
                format!(
                    "general declaration `{}` collides with an existing module row — refusing the whole general module",
                    clash.name
                ),
            );
            return;
        }
        for function in src.functions.iter_mut() {
            if !function.is_declaration() && existing.contains(&function.name) {
                let recorded = format!("general::{}", function.name);
                if existing.contains(&recorded) {
                    refuse(
                        summary,
                        &compiled_names,
                        format!(
                            "general function `{}` and its `general::` spelling both collide with existing module rows — refusing the whole general module",
                            function.name
                        ),
                    );
                    return;
                }
                renamed.push((function.name.clone(), recorded.clone()));
                function.name = recorded;
            }
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
    let global_offset = u32::try_from(dst.globals.len()).expect("global count exceeds u32");
    for global in src.globals.drain(..) {
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
    summary.general_renamed = renamed.clone();
    for (name, tv) in compiled_names {
        let reason = match renamed.iter().find(|(from, _)| *from == name) {
            Some((_, to)) => format!(
                "recorded as `{to}`: the name `{name}` is held by another lane's row of the same def; tier general rows are never linked, so the module name is resolved by no one"
            ),
            None => String::new(),
        };
        summary.general.push((name, "compiled", tv, reason));
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
        | Ty::Never => Ok(()),
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
        Inst::BinOp { ty, .. }
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
        | Inst::Const { ty, .. }
        | Inst::Undef { ty }
        | Inst::Copy { ty, .. }
        | Inst::Select { ty, .. }
        | Inst::SeqMapAddK { ty, .. }
        | Inst::SeqMapNot { ty, .. }
        | Inst::SeqMap { ty, .. }
        | Inst::LoadSlot { ty, .. } => remap_general_ty(ty, functy_map, types_map),
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
        Inst::Fence { .. }
        | Inst::Br { .. }
        | Inst::CondBr { .. }
        | Inst::Switch { .. }
        | Inst::Call { .. }
        | Inst::CallIndirect { .. }
        | Inst::Invoke { .. }
        | Inst::Return { .. }
        | Inst::NullPtr
        | Inst::GlobalAddr { .. }
        | Inst::Assume { .. }
        | Inst::Assert { .. }
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
        // A dialect op's payload is opaque to this walk; nothing the ExternCalls pipeline
        // emits, so refuse rather than guess at what its embedded types index.
        Inst::DialectOp(_) => {
            Err("general body carries a DialectOp — its embedded types are outside the v1.1 remap"
                .to_string())
        }
    }
}
/// Trust (v1.1): rewrite the `FuncId`s a CONSTANT can carry (`FnDef`, `Closure { func }`)
/// by the append offset, recursing through the aggregate constants. Infallible — offsets
/// cannot dangle — so it lives in the drain loop.
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
        Constant::Int(_)
        | Constant::U128(_)
        | Constant::Bytes { .. }
        | Constant::Float(_)
        | Constant::Bool(_)
        | Constant::SymbolAddr { .. }
        | Constant::PhantomData => {}
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
        other => other.clone(),
    })
}
pub fn link_clean_origin_edges(
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

    // Linking mutates only functions. Keep an immutable snapshot of the type
    // table so every reified function-pointer edge can be checked against the
    // target's exact FuncTyId before its FuncId changes.
    let func_types = module.func_types.clone();
    for (decl_id, decl_key, source_def_index, target_index, def_path) in matches {
        let target_id = FuncId::new(target_index);
        let declaration_calling_conv = {
            let declaration_rows: Vec<&Function> =
                module.functions.iter().filter(|f| f.id == decl_id).collect();
            match declaration_rows.as_slice() {
                [] => {
                    errors.push(format!(
                        "clean-origin link: declaration FuncId({}) for `{decl_key}` vanished \
                         before linking — report this",
                        decl_id.index()
                    ));
                    return;
                }
                [declaration] if declaration.is_declaration() => declaration.calling_conv,
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
        let mut row = LinkedRow {
            decl_func_id: decl_id.index(),
            decl_key,
            source_def_index,
            target_func_id: target_index,
            def_path,
            edges_repointed: 0,
            refusals: Vec::new(),
        };
        if declaration_calling_conv != target_calling_conv {
            row.refusals.push(format!(
                "declaration `{}` uses calling convention {}, but the Clean definition uses {} \
                 — every edge stays declared (fail-closed)",
                row.decl_key, declaration_calling_conv, target_calling_conv
            ));
            summary.linked.push(row);
            continue;
        }
        for index in 0..module.functions.len() {
            if module.functions[index].producer == Some(Producer::Clean) {
                continue; // Clean rows carry no Rust edges; and never rewrite them.
            }
            if module.functions[index].is_declaration() {
                continue;
            }
            let before = module.functions[index].clone();
            let (repointed, refusals) = repoint_edges(
                &mut module.functions[index],
                &func_types,
                decl_id,
                target_id,
                target_ty,
                &target_sig,
            );
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
                     \"decl_func_id\":{},\"source_def_index\":{},\"target_func_id\":{},\
                     \"def_path\":\"{}\",\"edges_repointed\":{},\
                     \"refusals\":[{}]}}",
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
                ),
            ));
        }
    }
}

/// Rewrite the callee ids inside one function: `Inst::Call { callee }` and
/// `Constant::FnDef(id)` equal to `decl_id` become `target_id`. Direct calls are
/// guarded on arity; reified function pointers must carry the target's exact
/// `FuncTyId`. Structural equality is insufficient because the validator pins
/// a statically resolved `CallIndirect` edge to the target function's declared
/// signature identity. Returns (repointed count, per-edge refusals).
fn repoint_edges(
    function: &mut Function,
    func_types: &[FuncTy],
    decl_id: FuncId,
    target_id: FuncId,
    target_ty: FuncTyId,
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
    (repointed, refusals)
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
                 \"same-crate Rust-to-Clean link only; not G5 cross-crate and not G7 codegen\"",
                json_escape_min(digest)
            ),
            _ => String::new(),
        };
        let tv_note = match &row.tv_note {
            Some(note) => format!(",\"tv_note\":\"{}\"", json_escape_min(note)),
            None => String::new(),
        };
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
                 \"mir_gate\":\"kernel Faithful earned for the emitted MIR \
                 body at the finalize seam\"{gate_fields}{tv_note}}}",
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
                 \"same-crate Rust-to-Clean link only; not G5 cross-crate and not G7 codegen\"",
                json_escape_min(digest)
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
             \"edges_repointed\": {}, \"refusals\": [{}]}}{comma}",
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
mod tests {
    use super::*;
    use trust_certify::clean_island::CleanIslandSession;
    use trust_ir::BinOp;
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
            signature: FuncTy { params: vec![Ty::U64], returns: vec![Ty::U64], is_vararg: false },
            function,
            gate: None,
            tv: None,
            tv_note: None,
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
        let function =
            trust_clean_ir::emit_clean_origin_function(&plan, FuncId::new(0), FuncTyId::new(0))
                .expect("fixture body must emit");
        let gate = trust_clean_ir_gate::admit_wrapping_binop(
            env, &plan, def_index, def_path, &signature, &function,
        )
        .expect("fixture must mint a real private gate token");
        CleanOriginIrRecord {
            def_index,
            def_path: def_path.to_string(),
            clean_name: "add8".to_string(),
            shape: "wrapping-binop",
            signature,
            function,
            gate: Some(gate),
            // These seam controls intentionally stop at authentication or
            // exact-set rejection, before the independent TV companion.
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
    fn caller_with_declared_edge() -> (Module, Vec<DeclarationLinkIdentity>) {
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
        module.functions[0].calling_conv = trust_ir::CallingConv::Rust;
        let mut decl =
            Function::new(FuncId::new(1), "m::clean_def", decl_ft, trust_ir::BlockId::new(0));
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
    /// `reuse_decl_type` chooses whether the pointer carries the declaration's
    /// exact FuncTyId or a separate table entry. The exact case calls the
    /// pointer, exercising the validator's full FnDef/CallIndirect identity
    /// rule; refusal fixtures leave their deliberately invalid pointer unused.
    fn caller_with_declared_fndef(
        pointer_sig: FuncTy,
        reuse_decl_type: bool,
    ) -> (Module, Vec<DeclarationLinkIdentity>) {
        let mut mb = trust_ir_build::ModuleBuilder::new("caller_crate");
        let decl_ft = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
        let caller_ft = decl_ft;
        let FuncTy { params, returns, is_vararg } = pointer_sig;
        assert!(!is_vararg, "the ModuleBuilder fixture admits fixed signatures only");
        let pointer_ft = if reuse_decl_type {
            assert_eq!(params, vec![Ty::U64]);
            assert_eq!(returns, vec![Ty::U64]);
            decl_ft
        } else {
            mb.add_func_type(params, returns)
        };
        let mut fb = mb.function("takes_clean_address", caller_ft);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::U64);
        fb.switch_to_block(entry);
        let address = fb.fn_addr(pointer_ft, FuncId::new(1));
        if reuse_decl_type {
            let result = fb.call_indirect_cc(
                address,
                pointer_ft,
                vec![x],
                trust_ir::CallingConv::Rust,
            );
            fb.ret(vec![result]);
        } else {
            fb.ret(vec![x]);
        }
        fb.build();

        let mut module = mb.build();
        module.functions[0].calling_conv = trust_ir::CallingConv::Rust;
        let mut decl =
            Function::new(FuncId::new(1), "m::clean_def", decl_ft, trust_ir::BlockId::new(0));
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

    fn clean_def_record_for_link() -> CleanOriginIrRecord {
        let mut record = projection_record(42);
        record.def_path = "m::clean_def".to_string();
        record.function.name = "cleanDef".to_string();
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
        assert_eq!(row.decl_func_id, 1);
        assert_eq!(row.source_def_index, 42);
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
        let declaration = module.functions.iter().find(|f| f.is_declaration()).expect("decl");
        assert_eq!(declaration.calling_conv, trust_ir::CallingConv::Rust);
        let target =
            module.functions.iter().find(|f| f.id.index() == appended_id).expect("appended target");
        assert_eq!(target.calling_conv, trust_ir::CallingConv::Rust);
        assert_eq!(
            declaration.calling_conv, target.calling_conv,
            "the direct edge preserves the declaration's calling convention"
        );
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
        assert!(linked.formula.contains("\"source_def_index\":42"), "{}", linked.formula);
    }

    /// Display paths are not injective. A declaration for source A must never re-point to a
    /// Clean body for distinct source B merely because B is the only row with A's display path.
    #[test]
    fn link_refuses_same_path_from_different_source_identity_without_rewriting() {
        let (mut module, mut declarations) = caller_with_declared_edge();
        declarations[0].local_def_index = Some(41); // A
        let mut errors = Vec::new();
        let mut summary = append_clean_origin(
            &mut module,
            // B has the same display path but a distinct exact source identity.
            vec![CleanOriginIrOutcome::Emitted(clean_def_record_for_link())],
            &mut errors,
        );
        assert!(errors.is_empty(), "append setup must succeed: {errors:?}");
        let appended_id = summary.emitted[0].func_id;

        link_clean_origin_edges(&mut module, &declarations, &mut summary, &mut errors);

        assert_eq!(errors.len(), 1, "identity mismatch must be fatal: {errors:?}");
        assert!(errors[0].contains("source identity mismatch"), "{errors:?}");
        assert!(errors[0].contains("expected def_index 41"), "{errors:?}");
        assert!(errors[0].contains("[42]"), "{errors:?}");
        assert!(summary.linked.is_empty(), "a refused identity must disclose no link row");
        let caller = &module.functions[0];
        let call_target = caller
            .blocks
            .iter()
            .flat_map(|block| &block.body)
            .find_map(|node| match &node.inst {
                Inst::Call { callee, .. } => Some(*callee),
                _ => None,
            })
            .expect("caller retains its call edge");
        assert_eq!(call_target, FuncId::new(1), "the edge must remain on A's declaration");
        assert_ne!(call_target.index(), appended_id, "the edge must not be retargeted to B");
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
        record.function.calling_conv = trust_ir::CallingConv::Rust;
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
    fn link_repoints_fndef_only_when_its_exact_signature_id_matches() {
        let exact = FuncTy { params: vec![Ty::U64], returns: vec![Ty::U64], is_vararg: false };
        let (mut module, declarations) = caller_with_declared_fndef(exact, true);
        let mut errors = Vec::new();
        let mut summary = append_clean_origin(
            &mut module,
            vec![CleanOriginIrOutcome::Emitted(clean_def_record_for_link())],
            &mut errors,
        );
        assert!(errors.is_empty(), "{errors:?}");
        let appended_id = summary.emitted[0].func_id;

        link_clean_origin_edges(&mut module, &declarations, &mut summary, &mut errors);

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
        assert_eq!(pointer_target.index(), appended_id);
        let (indirect_sig, indirect_calling_conv) = module.functions[0]
            .blocks
            .iter()
            .flat_map(|block| &block.body)
            .find_map(|node| match &node.inst {
                Inst::CallIndirect { sig, calling_conv, .. } => Some((*sig, *calling_conv)),
                _ => None,
            })
            .expect("fixture executes the reified pointer through CallIndirect");
        let target = module
            .functions
            .iter()
            .find(|function| function.id.index() == appended_id)
            .expect("appended Clean target");
        assert_eq!(indirect_sig, target.ty, "the indirect edge pins the target FuncTyId");
        assert_eq!(indirect_calling_conv, trust_ir::CallingConv::Rust);
        assert_eq!(
            indirect_calling_conv, target.calling_conv,
            "the indirect edge preserves the declaration's calling convention"
        );
        let validation = trust_ir_build::validate_module(&module);
        assert!(validation.is_empty(), "the linked final module must validate: {validation:?}");
    }

    #[test]
    fn link_refuses_cross_calling_convention_before_rewriting_a_direct_edge() {
        let (mut module, declarations) = caller_with_declared_edge();
        module.functions[1].calling_conv = trust_ir::CallingConv::C;
        pin_test_target(&mut module);
        let mut errors = Vec::new();
        let mut summary = append_clean_origin(
            &mut module,
            vec![CleanOriginIrOutcome::Emitted(clean_def_record_for_link())],
            &mut errors,
        );
        assert!(errors.is_empty(), "{errors:?}");
        let appended_id = summary.emitted[0].func_id;

        link_clean_origin_edges(&mut module, &declarations, &mut summary, &mut errors);

        assert!(
            errors.is_empty(),
            "a calling-convention disagreement is a disclosed link refusal: {errors:?}"
        );
        let row = &summary.linked[0];
        assert_eq!(row.edges_repointed, 0);
        assert_eq!(row.refusals.len(), 1, "{row:?}");
        assert!(row.refusals[0].contains("calling convention ccc"), "{row:?}");
        assert!(row.refusals[0].contains("uses rustcc"), "{row:?}");
        let call_target = module.functions[0]
            .blocks
            .iter()
            .flat_map(|block| &block.body)
            .find_map(|node| match &node.inst {
                Inst::Call { callee, .. } => Some(*callee),
                _ => None,
            })
            .expect("fixture retains its direct call");
        assert_eq!(
            call_target,
            FuncId::new(1),
            "the cross-convention edge stays declared"
        );
        assert_ne!(call_target.index(), appended_id);
        assert_eq!(module.functions[1].calling_conv, trust_ir::CallingConv::C);
        let target = module
            .functions
            .iter()
            .find(|function| function.id.index() == appended_id)
            .expect("appended Clean target");
        assert_eq!(target.calling_conv, trust_ir::CallingConv::Rust);
        let disclosure = module
            .spec_modules
            .iter()
            .find(|spec| spec.name == CLEAN_ORIGIN_DISCLOSURE_NAME)
            .expect("Clean-origin disclosure");
        let linked = disclosure
            .invariants
            .iter()
            .find(|invariant| invariant.name == "linked:1")
            .expect("calling-convention refusal is disclosed in-band");
        assert!(linked.formula.contains("calling convention ccc"), "{}", linked.formula);
        let coverage = coverage_section(&summary);
        assert!(coverage.contains("calling convention ccc"), "{coverage}");
        let validation = trust_ir_build::validate_module(&module);
        assert!(validation.is_empty(), "the refused module must remain valid: {validation:?}");
    }

    #[test]
    fn link_refuses_cross_calling_convention_before_rewriting_a_fndef_edge() {
        let exact = FuncTy { params: vec![Ty::U64], returns: vec![Ty::U64], is_vararg: false };
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
        let mut errors = Vec::new();
        let mut summary = append_clean_origin(
            &mut module,
            vec![CleanOriginIrOutcome::Emitted(clean_def_record_for_link())],
            &mut errors,
        );
        assert!(errors.is_empty(), "{errors:?}");
        let appended_id = summary.emitted[0].func_id;

        link_clean_origin_edges(&mut module, &declarations, &mut summary, &mut errors);

        assert!(errors.is_empty(), "the calling-convention mismatch is disclosed: {errors:?}");
        let row = &summary.linked[0];
        assert_eq!(row.edges_repointed, 0);
        assert_eq!(row.refusals.len(), 1, "{row:?}");
        assert!(row.refusals[0].contains("calling convention ccc"), "{row:?}");
        assert!(row.refusals[0].contains("uses rustcc"), "{row:?}");
        let (pointer_target, indirect_calling_conv) = module.functions[0]
            .blocks
            .iter()
            .flat_map(|block| &block.body)
            .fold((None, None), |(pointer_target, call_cc), node| match &node.inst {
                Inst::Const { value: Constant::FnDef(target), .. } => {
                    (Some(*target), call_cc)
                }
                Inst::CallIndirect { calling_conv, .. } => {
                    (pointer_target, Some(*calling_conv))
                }
                _ => (pointer_target, call_cc),
            });
        let pointer_target = pointer_target.expect("fixture retains the FnDef");
        assert_eq!(pointer_target, FuncId::new(1), "the FnDef stays on the C declaration");
        assert_ne!(pointer_target.index(), appended_id);
        assert_eq!(indirect_calling_conv, Some(trust_ir::CallingConv::C));
        let final_validation = trust_ir_build::validate_module(&module);
        assert!(final_validation.is_empty(), "the refused module stays valid: {final_validation:?}");
    }

    #[test]
    fn link_refuses_fndef_with_equal_but_distinct_signature_id() {
        let structurally_equal =
            FuncTy { params: vec![Ty::U64], returns: vec![Ty::U64], is_vararg: false };
        let (mut module, declarations) =
            caller_with_declared_fndef(structurally_equal, false);
        let mut errors = Vec::new();
        let mut summary = append_clean_origin(
            &mut module,
            vec![CleanOriginIrOutcome::Emitted(clean_def_record_for_link())],
            &mut errors,
        );
        assert!(errors.is_empty(), "{errors:?}");
        let appended_id = summary.emitted[0].func_id;

        link_clean_origin_edges(&mut module, &declarations, &mut summary, &mut errors);

        assert!(errors.is_empty(), "{errors:?}");
        let row = &summary.linked[0];
        assert_eq!(row.edges_repointed, 0);
        assert_eq!(row.refusals.len(), 1, "{row:?}");
        assert!(row.refusals[0].contains("FuncTyId(1)"), "{row:?}");
        assert!(row.refusals[0].contains("FuncTyId(0)"), "{row:?}");
        let pointer_target = module.functions[0]
            .blocks
            .iter()
            .flat_map(|block| &block.body)
            .find_map(|node| match &node.inst {
                Inst::Const { value: Constant::FnDef(target), .. } => Some(*target),
                _ => None,
            })
            .expect("fixture carries a reified function pointer");
        assert_eq!(pointer_target, FuncId::new(1));
        assert_ne!(pointer_target.index(), appended_id);
        let validation = trust_ir_build::validate_module(&module);
        assert!(validation.is_empty(), "the unused refused edge stays valid: {validation:?}");
    }

    #[test]
    fn link_refuses_fndef_signature_mismatch_without_rewriting() {
        let mismatched =
            FuncTy { params: vec![Ty::U64, Ty::U64], returns: vec![Ty::U64], is_vararg: false };
        let (mut module, declarations) = caller_with_declared_fndef(mismatched, false);
        let initial_validation = trust_ir_build::validate_module(&module);
        assert!(
            initial_validation.is_empty(),
            "the unused mismatched FnDef fixture exposes the shared-validator gap: \
             {initial_validation:?}"
        );
        let mut errors = Vec::new();
        let mut summary = append_clean_origin(
            &mut module,
            vec![CleanOriginIrOutcome::Emitted(clean_def_record_for_link())],
            &mut errors,
        );
        assert!(errors.is_empty(), "{errors:?}");
        let appended_id = summary.emitted[0].func_id;

        link_clean_origin_edges(&mut module, &declarations, &mut summary, &mut errors);

        assert!(errors.is_empty(), "{errors:?}");
        let row = &summary.linked[0];
        assert_eq!(row.source_def_index, 42);
        assert_eq!(row.edges_repointed, 0);
        assert_eq!(row.refusals.len(), 1, "{row:?}");
        assert!(row.refusals[0].contains("reified function-pointer edge carries FuncTyId"));
        let pointer_target = module.functions[0]
            .blocks
            .iter()
            .flat_map(|block| &block.body)
            .find_map(|node| match &node.inst {
                Inst::Const { value: Constant::FnDef(target), .. } => Some(*target),
                _ => None,
            })
            .expect("fixture carries a reified function pointer");
        assert_eq!(pointer_target, FuncId::new(1), "the refused edge stays on the declaration");
        assert_ne!(pointer_target.index(), appended_id);
        let final_validation = trust_ir_build::validate_module(&module);
        assert!(
            final_validation.is_empty(),
            "the fail-closed declaration edge must leave a valid module: {final_validation:?}"
        );
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

    #[test]
    fn general_definition_name_collision_is_recorded_under_the_general_namespace() {
        let mut module = Module::new("crate_under_test");
        let ty = module.add_func_type(FuncTy {
            params: Vec::new(),
            returns: Vec::new(),
            is_vararg: false,
        });
        module.add_function(Function::new(
            FuncId::new(0),
            "gen_callee", // held by another lane's row: the general definition is renamed
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
        assert_eq!(module.functions.len(), 3, "both general rows merge");
        let names: Vec<&str> = module.functions.iter().map(|f| f.name.as_str()).collect();
        assert_eq!(names, vec!["gen_callee", "general::gen_callee", "gen_caller"]);
        assert_eq!(
            summary.general_renamed,
            vec![("gen_callee".to_string(), "general::gen_callee".to_string())]
        );
        assert_eq!(summary.general_functions, vec!["general::gen_callee", "gen_caller"]);
        // The internal call edge is a FuncId edge: it still targets the (renamed) callee.
        let caller = &module.functions[2];
        assert!(
            caller.blocks[0]
                .body
                .iter()
                .any(|n| matches!(n.inst, Inst::Call { callee, .. } if callee == FuncId::new(1)))
        );
        assert!(summary.general.iter().all(|(_, d, _, _)| *d != "merge-refused"));
        assert_eq!(summary.general.iter().filter(|(_, d, _, _)| *d == "compiled").count(), 2);
        let cov = coverage_section(&summary);
        assert!(cov.contains("\"general_renamed\""));
        assert!(cov.contains("\"recorded_as\": \"general::gen_callee\""));
    }

    #[test]
    fn general_declaration_name_collision_still_refuses_the_whole_batch() {
        let mut module = Module::new("crate_under_test");
        let ty = module.add_func_type(FuncTy {
            params: Vec::new(),
            returns: Vec::new(),
            is_vararg: false,
        });
        module.add_function(Function::new(
            FuncId::new(0),
            "gen_extern",
            ty,
            trust_ir::BlockId::new(0),
        ));
        // A general module whose extra row is a DECLARATION named like an existing row.
        let mut src = general_two_fn_module();
        let decl_ty =
            src.add_func_type(FuncTy { params: Vec::new(), returns: Vec::new(), is_vararg: false });
        src.add_function(Function::new(
            FuncId::new(2),
            "gen_extern",
            decl_ty,
            trust_ir::BlockId::new(0),
        ));
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
