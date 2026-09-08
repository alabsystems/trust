// Trust: the Clean-origin trust-ir RECORDING PATH — increment IR-1 of
// docs/design/2026-08-27-two-language-direct-to-trust-ir.md (§3).
//
// This module answers the design decision `crates/trust-clean-ir/src/lib.rs`
// deliberately left open: WHERE the trust-ir spelling of a Clean-origin body is
// recorded. The ruling: it joins the same per-crate `trust_ir::Module` the
// direct THIR producer assembles, through a finalize-seam collection that
// RE-EARNS its own kernel verdict — the `clean_origin_export.rs` discipline
// ("folding the runs together would trade independence for compile time; do
// not"), applied to a second consumer.
//
// WHY RE-EARN RATHER THAN TRUST THE PROVIDER RUN. On a warm incremental cache
// `tcx.optimized_mir(def)` loads the gated body WITHOUT running the provider,
// so the demand below is NOT a gate execution. The fresh `admit_lowering` here
// is what earns the verdict, every time, against the exact cached body the
// compile will use. Any plan drift between the provider run and this seam
// surfaces as a fatal refusal — both spellings anchor by kernel defeq to the
// same declaration — never as a silent mismatch.
//
// REFUSAL SEMANTICS (design §3.1, the export lane's split):
//   * environment failure or a fresh `admit_lowering` refusal on a REGISTRY def
//     is FATAL at the registry span — the "environment disagrees with itself"
//     class; silence there would fail open;
//   * a `trust-clean-ir` capability refusal (`CleanIrRefusal`) is normally a
//     SKIP-WITH-REASON row — a lane that produces no binary must never fail a
//     compilation the MIR lane completes. W2's already-targeted WrappingBinOp
//     population is the bounded exception: signature lowering, Function
//     emission, or carrier-gate refusal is a compiler self-disagreement and is
//     fatal, never rerouted through the general lane. The refusal `Display`
//     carries its fix options (v7/D3) for every non-target shape.
//
// The caller (`rustc_interface::passes`) invokes this ONLY when verification is
// enabled: on verification-off artifact lanes there is deliberately no demand
// and no new fatal surface — the coverage sidecar records `recorded: false`
// with the reason instead (disclosed absence, never silent).

use rustc_middle::ty::TyCtxt;
use trust_ir::value::{FuncId, FuncTyId};
use trust_thir_lower::clean_origin_join::{
    CleanOriginIrOutcome, CleanOriginIrRecord, CleanOriginIrSkip, GeneralCleanIr, GeneralOutcome,
    GeneralRow,
};

use crate::clean_origin_mir::{
    clean_crate_environment, clean_origin_defs, clean_origin_registry_entry,
};

/// Collect the trust-ir spelling of every Clean-origin def in this crate,
/// re-earning the kernel faithfulness verdict per def.
///
/// Precondition (enforced by the caller, `rustc_interface::passes`):
/// verification is enabled. Under `-Ztrust-verify=off` this must not be
/// called — the artifact lanes there make no demand on Clean-origin bodies
/// and the recording is a disclosed absence instead.
pub fn collect_clean_origin_ir(tcx: TyCtxt<'_>) -> Vec<CleanOriginIrOutcome> {
    let defs: Vec<_> = clean_origin_defs(tcx).collect();
    // The GENERAL lane (totality campaign) runs whenever the crate has islands
    // at all — a crate whose declarations are all non-carrier (recursive
    // functions, inductives, matches) mints ZERO defs and still records.
    let has_islands = tcx.hir_crate_items(()).free_items().any(|item_id| {
        matches!(tcx.hir_item(item_id).kind, rustc_hir::ItemKind::CleanIsland { .. })
    });
    if defs.is_empty() && !has_islands {
        return Vec::new();
    }
    if defs.is_empty() {
        // General-only crate: the environment refusal here is a SKIP, not the
        // registry lane's fatal — no minted def's binary is at stake.
        let Some(session) = clean_crate_environment(tcx) else {
            return Vec::new();
        };
        let env = session.environment().expect("an untainted session has an environment");
        let no_planner_rows = rustc_data_structures::fx::FxHashSet::default();
        return match collect_general_clean_ir(tcx, env, &no_planner_rows) {
            Some(general) => vec![CleanOriginIrOutcome::General(general)],
            None => Vec::new(),
        };
    }

    // Demand every gated body first. Under verification this is deliberate
    // fail-closed tightening (design §3.1, disclosed): a minted-but-never-
    // demanded def whose gate would refuse now fails deterministically at
    // finalize instead of compiling as a latent landmine behind a callable
    // name. For every def a verified compile already demands, this is a cache
    // hit.
    for &def in &defs {
        let _ = tcx.optimized_mir(def.to_def_id());
    }

    // One environment for the whole collection: `clean_crate_environment`
    // re-elaborates the crate's islands (deliberately uncached), exactly as
    // the gate and export lanes do.
    let Some(session) = clean_crate_environment(tcx) else {
        // Mirror of `clean_origin_mir`'s environment fatal: a def in the
        // registry means the mint's kernel run succeeded, so a failed re-run
        // here is the environment disagreeing with itself.
        let (name, span) = defs
            .first()
            .and_then(|&d| clean_origin_registry_entry(tcx, d))
            .unwrap_or((String::from("<unknown>"), rustc_span::DUMMY_SP));
        tcx.dcx().span_fatal(
            span,
            format!(
                "internal: refusing to record the trust-ir spelling for Clean declaration \
                 `{name}` — re-checking this crate's Clean islands at the finalize seam did \
                 not produce a usable environment, while the mint's kernel run for the same \
                 islands succeeded. Options: run `scripts/submodule_sync.sh` (a stale \
                 `first-party/clean` worktree is the most common cause), re-run with \
                 `RUSTC_LOG=rustc_mir_transform::clean_origin_mir=debug` to see the island \
                 batch verdict, or report this as an environment self-disagreement."
            ),
        );
    };
    let env = session.environment().expect("an untainted session has an environment");

    let mut out = Vec::with_capacity(defs.len());
    for def in defs {
        let Some((name, span)) = clean_origin_registry_entry(tcx, def) else {
            // `defs` came from the registry; a missing row mid-iteration is a
            // compiler bug, not a user program state.
            tcx.dcx().bug("clean-origin def vanished from its own registry during collection");
        };
        let def_index = def.to_def_id().index.as_u32();
        // The linkage key: must be spelled exactly as the THIR ledger spells its
        // callee def_paths (`with_no_trimmed_paths`), or IR-5's edge matching
        // silently finds nothing (fail-closed, but the lane looks landed while
        // linking nothing).
        let def_path =
            rustc_middle::ty::print::with_no_trimmed_paths!(tcx.def_path_str(def.to_def_id()));

        // Side A, re-planned from the kernel environment (fresh, independent
        // of the provider run's plan).
        let plan = match trust_clean_origin::plan_clean_origin_body(env, &name) {
            Ok(plan) => plan,
            Err(refusal) => {
                // The provider served a body for this def (demanded above), so
                // its plan succeeded; a seam-time plan refusal is the
                // environment disagreeing with itself.
                tcx.dcx().span_fatal(
                    span,
                    format!(
                        "internal: the finalize-seam re-plan for Clean declaration `{name}` \
                         refused, while the code-generation plan for the same \
                         declaration succeeded moments earlier in this compile ({}). These \
                         are two runs of one planner over one kernel environment; a \
                         disagreement means the environment or the plan pipeline is not \
                         deterministic. Please report it.",
                        refusal.note()
                    ),
                );
            }
        };

        // Side B, re-extracted from the exact cached body this compile uses,
        // and the verdict RE-EARNED. `admit_lowering` refusing a body the
        // provider's own gate admitted is the same self-disagreement class.
        let body = tcx.optimized_mir(def.to_def_id());
        let extracted = trust_mir_extract::extract_function(tcx, body);
        if let Err(refusal) = trust_clean_origin::admit_lowering(env, &plan, &extracted) {
            tcx.dcx().span_fatal(
                span,
                format!(
                    "internal: the finalize-seam faithfulness re-check for Clean \
                     declaration `{name}` refused against the cached emitted \
                     body ({}) — a body the code-generation gate admitted in this same \
                     compile. The trust-ir spelling will not be recorded for a body the \
                     kernel does not identify with its declaration. Please report it.",
                    refusal.note()
                ),
            );
        }

        // The trust-ir spelling. Ids are placeholders: identity belongs to the
        // owning Module, and the append seam (`clean_origin_join`) mints the
        // real `FuncId`/`FuncTyId` at insertion.
        let shape = shape_tag(plan.shape());
        match trust_clean_ir::trust_ir_func_ty(plan.signature()) {
            Ok(signature) => {
                match trust_clean_ir::emit_clean_origin_function(
                    &plan,
                    FuncId::new(0),
                    FuncTyId::new(0),
                ) {
                    Ok(function) => {
                        // W2 carrier gate: this exact bounded shape may no longer
                        // escape on the historical kernel-TV/ungated rung. The
                        // independent production reflector reads `function`
                        // itself (not the sealed shape's operands), rebuilds a
                        // Clean term, and asks the kernel for whole-term defeq.
                        // A targeted refusal is an internal wrong-code signal:
                        // fatal here, never converted to a skip or weaker tier.
                        let gate = if matches!(
                            plan.shape(),
                            trust_clean_origin::CleanOriginShape::WrappingBinOp { .. }
                        ) {
                            Some(
                                trust_clean_ir_gate::admit_wrapping_binop(
                                    env,
                                    &plan,
                                    def_index,
                                    &def_path,
                                    &signature,
                                    &function,
                                )
                                .unwrap_or_else(|refusal| {
                                    tcx.dcx().span_fatal(
                                        span,
                                        format!(
                                            "internal: the independently reflected TrustIR body \
                                             for targeted Clean wrapping-binop `{name}` was refused \
                                             at the carrier gate ({}). This body is never demoted to \
                                             kernel-tv or structural evidence; report the compiler \
                                             disagreement.",
                                            refusal.note()
                                        ),
                                    )
                                }),
                            )
                        } else {
                            None
                        };
                        let (tv, tv_note) =
                            mint_kernel_tv(env, &name, shape, &signature, &function);
                        out.push(CleanOriginIrOutcome::Emitted(CleanOriginIrRecord {
                            def_index,
                            def_path,
                            clean_name: name,
                            shape,
                            signature,
                            function,
                            gate,
                            tv,
                            tv_note,
                        }))
                    }
                    Err(refusal) => {
                        let reason = trust_ir_precursor_refusal(
                            tcx,
                            span,
                            &plan,
                            &name,
                            "function-emission",
                            refusal.to_string(),
                        );
                        out.push(CleanOriginIrOutcome::Skipped(CleanOriginIrSkip {
                            def_index,
                            def_path,
                            clean_name: name,
                            shape,
                            reason,
                        }))
                    }
                }
            }
            Err(refusal) => {
                let reason = trust_ir_precursor_refusal(
                    tcx,
                    span,
                    &plan,
                    &name,
                    "signature-lowering",
                    refusal.to_string(),
                );
                out.push(CleanOriginIrOutcome::Skipped(CleanOriginIrSkip {
                    def_index,
                    def_path,
                    clean_name: name,
                    shape,
                    reason,
                }))
            }
        }
    }
    // The general lane covers what the planner did NOT emit. An EMITTED name
    // is excluded (its trust-ir row already exists at a stronger tier, and the
    // merge's name-identity guard would refuse the whole batch on the
    // collision — measured: `cleanWsum` refused `triRank` alongside it). A
    // planner SKIP row appended nothing, so its name stays eligible here.
    let planner_emitted: rustc_data_structures::fx::FxHashSet<String> = out
        .iter()
        .filter_map(|outcome| match outcome {
            CleanOriginIrOutcome::Emitted(record) => Some(record.clean_name.clone()),
            _ => None,
        })
        .collect();
    if let Some(general) = collect_general_clean_ir(tcx, env, &planner_emitted) {
        out.push(CleanOriginIrOutcome::General(general));
    }
    out
}

/// Preserve the historical skip-with-reason behavior outside W2, but make
/// every precursor refusal fatal once the sealed plan identifies the bounded
/// WrappingBinOp population. Calling this helper from BOTH lowering Err arms is
/// a source-pinned part of the gate: a target may never fall through into the
/// general recorder after signature or Function emission disagrees.
fn trust_ir_precursor_refusal(
    tcx: TyCtxt<'_>,
    span: rustc_span::Span,
    plan: &trust_clean_origin::CleanOriginPlan,
    clean_name: &str,
    stage: &'static str,
    detail: String,
) -> String {
    if matches!(plan.shape(), trust_clean_origin::CleanOriginShape::WrappingBinOp { .. }) {
        tcx.dcx().span_fatal(
            span,
            format!(
                "internal: targeted Clean wrapping-binop `{clean_name}` refused during TrustIR \
                 {stage} ({detail}). This targeted disagreement is fatal and is never recorded \
                 as a skip, rerouted to the general lane, or demoted; report the compiler bug."
            ),
        );
    }
    detail
}

/// A stable, short tag for the plan's shape, for coverage rows. Deliberately a
/// rendering of our own (the shape enum's `Debug` names carry payloads).
fn shape_tag(shape: &trust_clean_origin::CleanOriginShape) -> &'static str {
    use trust_clean_origin::CleanOriginShape as S;
    match shape {
        S::Projection { .. } => "projection",
        S::InductiveProjection { .. } => "inductive-projection",
        S::ConstantUint { .. } => "constant-uint",
        S::WrappingBinOp { .. } => "wrapping-binop",
        S::Composed { .. } => "composed",
        S::Select { .. } => "select",
        S::SelectLiteral { .. } => "select-literal",
        S::SelectOperands { .. } => "select-operands",
        S::SelectBeq { .. } => "select-beq",
        S::SelectBeqGeneral { .. } => "select-beq-general",
        S::RawBinOp { .. } => "raw-binop",
        S::StructuralNatRec { .. } => "structural-nat-rec",
        S::WellFoundedNatRec { .. } => "well-founded-nat-rec",
        // Deliberately no `_` arm: `CleanOriginShape` is non-`#[non_exhaustive]`
        // by design, so a new shape is a compile error here — a forced decision
        // about its recording tag — never a silent fall-through.
    }
}

// ── tier kernel-tv: the mint half (design §4) ───────────────────────────────
//
// For in-fragment shapes, mint the translation-validation payload — the
// `CleanTV.<fn>.denotes` obligation + CleanCic certificate — whose statement
// equates the denotation of the EMITTED trust-ir function with the denotation
// of the KERNEL DEFINITION, both at Nat mod 2^w. The kernel judgment itself is
// NOT run here: it runs once, independently, at the join seam, where
// `trust_ir_build::validate_module` routes the certificate to the
// `clean_backend_tv` re-checker, which RE-DERIVES the emitted side's
// denotation from the mini-module (synthesis-by-recomputation — the producer
// cannot choose the LHS) and has the CIC kernel decide definitional equality
// on theorem insertion.
//
// HONESTY (the TCB row in docs/TCB.md binds): the two denotation maps —
// clean-reflect's producing copy here and trust-ir-build's re-checking mirror —
// are trusted, unmechanized checker-spec with correlated authorship. And the
// judgment is at Nat mod 2^w, NEVER at the carrier: kernel defeq at Nat does
// not subsume representation faithfulness (the 08-04 G3 ruling), so kernel-tv
// is not an `admit_lowering` equivalent and licenses nothing toward codegen.

/// The minted TV payload, carried on the record for the join seam's
/// independent kernel re-check.
fn mint_kernel_tv(
    env: &clean_kernel::Environment,
    clean_name: &str,
    shape: &'static str,
    signature: &trust_ir::ty::FuncTy,
    function: &trust_ir::Function,
) -> (Option<trust_thir_lower::clean_origin_join::CleanTvMint>, Option<String>) {
    use trust_ir::proof::{
        CleanCicKernelRecheck, KERNEL_ANCHOR_CLEAN_BACKEND_TV, ObligationKind, ProofEvidence,
        ProofStatus, clean_cic_lineage_digest,
    };

    // Shape pre-filter: only the call-free straight-line shapes are inside the
    // TV denotation fragment today. Every skip reason carries its options
    // (v7/D3); the row stays tier `structural`, and a SKIP is never a verdict.
    match shape {
        "projection" | "constant-uint" | "wrapping-binop" | "composed" => {}
        "raw-binop" => {
            return (
                None,
                Some(
                    "kernel-tv not attempted: the denotation fragment has no Nat rule for \
                 BinOp::And/Or — Fragment-2 covers Add/Sub/Mul only (clean-reflect \
                 denote_binop, fail-closed) and trust-ir-build's clean_backend_tv mirror \
                 matches it. Options: (1) extend BOTH denotation copies in one increment \
                 with a bitwise Nat vocabulary plus probes-first kernel-agreement evidence; \
                 (2) rely on the MIR lane's admit_lowering, which already gates this shape \
                 at the carrier; (3) leave the row structural."
                        .to_string(),
                ),
            );
        }
        "select" | "select-literal" | "select-operands" | "select-beq" | "select-beq-general" => {
            return (
                None,
                Some(
                    "kernel-tv not attempted: this shape is emitted as a value-producing \
                 Inst::Select in one block, and the denotation fragment's only conditional \
                 form is the Fragment-3a CondBr diamond — Inst::Select has no denotation \
                 rule and is refused fail-closed. Options: (1) add a select rule denoting \
                 to the existing Bool.rec piecewise vocabulary to BOTH denotation copies in \
                 one increment; (2) re-spell the emission as the CondBr diamond the \
                 fragment already denotes; (3) leave the row structural."
                        .to_string(),
                ),
            );
        }
        "inductive-projection" => {
            return (
                None,
                Some(
                    "kernel-tv not attempted: the SOURCE side is a recursive definition whose \
                 projection-equality rests on an induction proof, and Eq.refl definitional \
                 equality cannot decide extensional equality — a source-side exclusion, \
                 not a walker gap. Options: keep faithfulness at the MIR lane's \
                 induction-backed gate; leave the row structural."
                        .to_string(),
                ),
            );
        }
        "structural-nat-rec" | "well-founded-nat-rec" => {
            return (
                None,
                Some(
                    "kernel-tv unreachable: the shape is a recording-path skip already (the \
                 recursion computes at unbounded Nat and needs a NatRuntime), and the \
                 Nat-mod-2^w vocabulary cannot state an unbounded computation. Options: \
                 land the design's §6.4 Nat-runtime modelling first; keep faithfulness at \
                 the MIR lane's kernel recursion gates."
                        .to_string(),
                ),
            );
        }
        other => {
            return (
                None,
                Some(format!(
                    "kernel-tv not attempted: shape `{other}` has no TV disposition recorded \
                 — a new shape must decide its denotation story explicitly. Options: add \
                 the shape to the mint pre-filter with its fragment argument, or leave \
                 the row structural."
                )),
            );
        }
    }

    // The emitted-side denotation, from a scratch mini-module shaped exactly
    // like the one the join seam will re-check (function id 0, signature id 0).
    let mut mini = trust_ir::Module::new(format!("clean-origin-tv::{clean_name}"));
    mini.func_types.push(signature.clone());
    let mut func = function.clone();
    func.id = trust_ir::value::FuncId::new(0);
    func.ty = trust_ir::value::FuncTyId::new(0);
    let func_name = func.name.clone();
    mini.functions.push(func);
    let function_ref = &mini.functions[0];

    let lhs = match clean_reflect::denote_function(&mini, function_ref) {
        Ok(denotation) => denotation,
        Err(refusal) => {
            return (
                None,
                Some(format!(
                    "kernel-tv not attempted: the emitted function is outside the denotation \
                 fragment ({refusal:?}). Options: widen BOTH denotation copies in one \
                 increment, or leave the row structural (mixed-width signatures are the \
                 common cause — the TV walker requires one uniform width, which the MIR \
                 gate does not)."
                )),
            );
        }
    };
    if !lhs.callees.is_empty() {
        return (
            None,
            Some(
                "kernel-tv not attempted: the emitted function carries call edges, and this \
             mint covers the call-free fragment only. Options: extend the mint to \
             Fragment-3b callee grounding, or leave the row structural."
                    .to_string(),
            ),
        );
    }

    // The source side: the declaration's ORIGINAL kernel definition — the same
    // provenance-gated value the plan pipeline reads.
    let kernel_name = clean_kernel::Name::from_string(clean_name);
    let Some(defn) = env.get_const(&kernel_name).and_then(|constant| constant.value.clone()) else {
        return (
            None,
            Some(
                "kernel-tv not attempted: the kernel environment holds no definition value \
             for this declaration at the mint seam — a state the plan pipeline gates \
             against, so report this if seen. The row stays structural."
                    .to_string(),
            ),
        );
    };
    let records = clean_reflect::RecordVocab::from_module(&mini);
    let rhs = match clean_reflect::denote_source(&defn, lhs.width, &lhs.callees, &records) {
        Ok(denotation) => denotation,
        Err(refusal) => {
            return (
                None,
                Some(format!(
                    "kernel-tv not attempted: the kernel definition is outside the source \
                 denotation fragment ({refusal:?}). Options: widen BOTH denotation \
                 copies' source recognition in one increment, or leave the row structural."
                )),
            );
        }
    };

    // The decodable payload, exactly as the clean-side minter builds it: the
    // comparand as `fun (x1…xn : Nat) => rhs.body` (the re-checker strips
    // `callees.len() + arity` binders — callees are empty here), the proof as
    // the Eq.refl telescope over the EMITTED denotation.
    let with_params = (0..rhs.arity).fold(rhs.body.clone(), |acc, _| {
        clean_kernel::Expr::lam(
            clean_kernel::BinderInfo::Default,
            clean_kernel::Expr::const_str("Nat"),
            acc,
        )
    });
    let callee_arities: Vec<usize> = lhs.callees.iter().map(|(_, arity)| *arity).collect();
    let proof = clean_reflect::tv_proof_term(&callee_arities, lhs.arity, &lhs.body);
    let (term, context) = match (
        trust_ir::proof::encode_clean_expr_v1(&proof),
        trust_ir::proof::encode_clean_expr_v1(&with_params),
    ) {
        (Ok(term), Ok(context)) => (term, context),
        (Err(reason), _) | (_, Err(reason)) => {
            return (
                None,
                Some(format!(
                    "kernel-tv not attempted: certificate payload failed to serialize \
                 ({reason}). Report this — the payload codec refusing a fragment term \
                 is a codec bound, not a program property."
                )),
            );
        }
    };

    let obligation = trust_ir::proof::ProofObligation::new(
        trust_ir::value::ProofId::new(0),
        ObligationKind::TranslationValidation,
        ProofStatus::Certified,
        format!(
            "clean-origin kernel-tv: '{func_name}' denotes its Clean definition at Nat \
             mod 2^{} (kernel-decided defeq of two MINTED denotations; carrier \
             faithfulness NOT established — G3)",
            lhs.width
        ),
    )
    .with_function(trust_ir::value::FuncId::new(0));
    let lineage = clean_cic_lineage_digest(&obligation);
    let certificate = trust_ir::proof::ProofCertificate {
        obligation: trust_ir::value::ProofId::new(0),
        prover: "trustc.clean-origin-tv".to_string(),
        evidence: ProofEvidence::CleanCic {
            term,
            context,
            lineage,
            kernel_recheck: Some(CleanCicKernelRecheck {
                module: "CleanCompiler.BackendTV".to_string(),
                theorems: vec![clean_reflect::tv_theorem_name(&func_name)],
                anchor: KERNEL_ANCHOR_CLEAN_BACKEND_TV.to_string(),
                allowed_axioms: Vec::new(),
            }),
        },
    };
    (Some(trust_thir_lower::clean_origin_join::CleanTvMint { obligation, certificate }), None)
}

// ── the GENERAL Clean lane (totality campaign) ──────────────────────────────
//
// The 13-shape planner is the OPTIMIZATION ladder, not the ceiling (the §6f
// ruling: the most powerful solution). This lane compiles EVERY computational
// island declaration — inductively-defined functions, matches, structures,
// typeclass instances, structural and well-founded recursion, higher-order
// code — through clean-compiler's general pipeline (kernel Expr → L5CNF →
// L5IR → trust_ir::Module, RuntimeLowering::ExternCalls) and records the
// result at tier `general`: claim-free, ungated, never a codegen input.
//
// Fail-closed shape, unlike the registry lane: EVERY failure here is a
// SKIP-with-reason row, never a fatal — general defs were never minted, no
// binary depends on them, and a capability gap in a recording lane must not
// break a compile. The one kernel-adjacent teeth: the emitted module's TV
// certificates (minted by clean-compiler's own kernel gate) are re-checked
// IN-TREE via `trust_ir_build::validate_module` (the clean_backend_tv mirror
// re-derives the emitted side) BEFORE the proof channels are stripped — a
// refusal there skips the whole batch loudly (`tv-refused-general`), because
// a mint-time kernel refusal is clean-compiler's own miscompile detector.

fn collect_general_clean_ir(
    tcx: TyCtxt<'_>,
    env: &clean_kernel::Environment,
    planner_emitted: &rustc_data_structures::fx::FxHashSet<String>,
) -> Option<GeneralCleanIr> {
    use rustc_ast::CleanDeclKind;

    // Every NAMED island declaration, in authored order, one entry per name.
    let mut names: Vec<String> = Vec::new();
    let mut seen = rustc_data_structures::fx::FxHashSet::default();
    for item_id in tcx.hir_crate_items(()).free_items() {
        let item = tcx.hir_item(item_id);
        let rustc_hir::ItemKind::CleanIsland { decls, .. } = item.kind else { continue };
        for decl in decls {
            if decl.name.as_str().is_empty() {
                continue;
            }
            // Kinds that can carry a computational value. Everything else
            // (theorem/axiom/example/commands) is decided by the kernel lookup
            // below anyway; this filter only trims obvious non-values.
            if !matches!(
                decl.kind,
                CleanDeclKind::Def
                    | CleanDeclKind::Codef
                    | CleanDeclKind::Instance
                    | CleanDeclKind::Opaque
                    | CleanDeclKind::Theorem
                    | CleanDeclKind::Axiom
            ) {
                continue;
            }
            let name = decl.name.to_string();
            // Already recorded by the planner lane at a stronger tier — the
            // general lane is defined as what lies OUTSIDE the planner.
            if planner_emitted.contains(&name) {
                continue;
            }
            if seen.insert(name.clone()) {
                names.push(name);
            }
        }
    }
    if names.is_empty() {
        return None;
    }

    let mut rows = Vec::with_capacity(names.len());
    let mut batch: Vec<clean_compiler::Decl> = Vec::new();
    let mut batch_names: Vec<String> = Vec::new();
    for name in names {
        let kernel_name = clean_kernel::Name::from_string(&name);
        let Some(info) = env.get_const(&kernel_name) else {
            rows.push(GeneralRow {
                clean_name: name,
                outcome: GeneralOutcome::Skipped {
                    reason: "declared in an island but absent from the kernel environment — \
                             report this (the session admitted the island, so every named \
                             declaration should be registered)"
                        .to_string(),
                },
            });
            continue;
        };
        match clean_compiler::constant_to_decl(env, info) {
            Ok(Some(decl)) => {
                batch.push(decl);
                batch_names.push(name);
            }
            Ok(None) => rows
                .push(GeneralRow { clean_name: name, outcome: GeneralOutcome::NotComputational }),
            Err(error) => rows.push(GeneralRow {
                clean_name: name,
                outcome: GeneralOutcome::Skipped {
                    reason: format!(
                        "the general L5CNF lowering refused this declaration ({error:?}). \
                         Options: spell the definition inside the supported computational \
                         surface, or leave it PROOF-side — recording is not calling, and \
                         nothing breaks."
                    ),
                },
            }),
        }
    }
    if batch.is_empty() {
        return Some(GeneralCleanIr { rows, module: None });
    }

    // The whole island batch compiles TOGETHER: intra-island calls resolve
    // internally; prelude/runtime dependencies ride as bodyless extern
    // declarations (RuntimeLowering::ExternCalls), disclosed by presence.
    let target = &tcx.sess.target;
    let emit_config = clean_compiler::emit_trust_ir::TrustIrConfig {
        module_name: format!("clean-general::{}", tcx.crate_name(rustc_span::def_id::LOCAL_CRATE)),
        use_clean_dialect: false,
        runtime_lowering: clean_compiler::emit_trust_ir::RuntimeLowering::ExternCalls,
        // Mirrors `crate_module::stamp_target_info_if_vacuous` exactly — the
        // merge asserts equality against the crate module's stamp.
        target_info: Some(trust_ir::TargetInfo {
            triple: target.llvm_target.to_string(),
            pointer_size: u32::from(target.pointer_width / 8),
            endianness: match target.endian {
                rustc_abi::Endian::Little => trust_ir::Endianness::Little,
                rustc_abi::Endian::Big => trust_ir::Endianness::Big,
            },
            abi: None,
            struct_passing: trust_ir::StructPassingPolicy::Unclassified,
        }),
        ..Default::default()
    };
    let pipeline_config = clean_compiler::pass_manager::PipelineConfig::default();
    match clean_compiler::pass_manager::compile_lcnf_to_trust_ir_with_report(
        &batch,
        env,
        &pipeline_config,
        &emit_config,
    ) {
        Ok((mut module, report)) => {
            // Independent in-tree re-check of the mint's TV certificates (the
            // clean_backend_tv mirror re-derives the emitted side), BEFORE the
            // proof channels are stripped for the claim-free publication.
            let validation_errors = trust_ir_build::validate_module(&module);
            if !validation_errors.is_empty() {
                let mut rendered: Vec<String> =
                    validation_errors.iter().take(3).map(|e| format!("{e:?}")).collect();
                if validation_errors.len() > 3 {
                    rendered.push(format!("... and {} more", validation_errors.len() - 3));
                }
                let reason = format!(
                    "tv-refused-general: the in-tree re-check refused the general module \
                     ({}) — a mint-time certificate or module shape the mirror could not \
                     re-derive. The whole batch is skipped, never published unvalidated. \
                     Report this pairing.",
                    rendered.join("; ")
                );
                for name in batch_names {
                    rows.push(GeneralRow {
                        clean_name: name,
                        outcome: GeneralOutcome::Skipped { reason: reason.clone() },
                    });
                }
                return Some(GeneralCleanIr { rows, module: None });
            }
            // Claim-free publication: strip every proof channel. The TV
            // verdicts survive as per-row disclosure bits only.
            module.proof_obligations.clear();
            module.proof_certificates.clear();
            module.obligation_diagnostics.clear();
            for function in &mut module.functions {
                function.proofs.clear();
                function.summary = None;
            }
            let certified: rustc_data_structures::fx::FxHashSet<&str> =
                report.certified.iter().map(String::as_str).collect();
            for name in batch_names {
                let tv = certified.contains(name.as_str());
                rows.push(GeneralRow {
                    clean_name: name,
                    outcome: GeneralOutcome::Compiled { tv_mint_certified: tv },
                });
            }
            Some(GeneralCleanIr { rows, module: Some(module) })
        }
        Err(error) => {
            let reason = format!(
                "the general pipeline refused the island batch ({error:?}). Options: the \
                 refusal names the declaration and construct — spell it inside the \
                 compilable surface, split the island so the refusing declaration stands \
                 alone, or leave it PROOF-side."
            );
            for name in batch_names {
                rows.push(GeneralRow {
                    clean_name: name,
                    outcome: GeneralOutcome::Skipped { reason: reason.clone() },
                });
            }
            Some(GeneralCleanIr { rows, module: None })
        }
    }
}
