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
// WHEN IT RUNS (plan step 3.5, docs/design/2026-10-02-step3-lean-through-trust-ir.md §5.1).
// The caller (`rustc_interface::passes`) chooses the lane ([`RecorderLane`]):
//   * on F1 (`-Ztrust-cg-frontend=trust-ir` with the trust-ir producer running), on EVERY
//     compile, verification on or off: the carrier gate is a compilation-correctness check (08-04
//     §5(b)2) and F1 has no MIR fallback, so a verify-off F1 compile must record. On F1 the
//     recorder demands no `clean_origin_mir` body at all: no eager demand, no per-row MIR
//     re-earn. A row's verdict there is the carrier gate's on the published Function, re-earned
//     at this seam every compile (the IR-D1 discipline, kept: what changed is which thing ships).
//     The MIR re-earn is the test-only oracle's (`tests/run-make/trust-cg-f1-clean-recorder`
//     compiles each fixture on this MIR lane too and requires the same rows);
//   * on every other lane only with verification on (the MIR lane below, as before);
//     verification-off artifact lanes make no demand and no new fatal surface — the coverage
//     sidecar records `recorded: false` with the reason instead (disclosed absence, never silent).

use rustc_hir::intravisit::{self, Visitor};
use rustc_middle::ty::TyCtxt;
use trust_ir::value::{FuncId, FuncTyId};
use trust_thir_lower::clean_origin_join::{
    CleanOriginIrOutcome, CleanOriginIrRecord, CleanOriginIrSkip, CleanOriginRustCallRecord,
    CleanOriginRustCallee, GeneralCleanIr, GeneralOutcome, GeneralRow, MirGateAtSeam,
};

use crate::clean_origin_mir::{
    clean_crate_environment, clean_origin_defs, clean_origin_registry_entry,
};

mod source_equations;
// Trust (plan step 3.5): the reach counter, for `rustc_interface::passes`, which does not link
// trust-thir-lower directly.
pub use trust_thir_lower::clean_origin_reach;
use trust_thir_lower::clean_origin_reach::ReachLane;

/// Plan step 3.5 (design §5.1): which lane the Clean recorder runs on, chosen by
/// `rustc_interface::passes` ([`recorder_lane`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RecorderLane {
    /// The MIR lane (verification on, not F1): every gated body is demanded and each row's
    /// kernel verdict is re-earned against its emitted MIR at this seam, as before step 3.5.
    MirReearn,
    /// F1, verification on or off: no `clean_origin_mir` body is demanded. The fed signature is
    /// checked against the plan without MIR; purity and the cross-language cycle are decided on
    /// trust-ir after the finalize ([`check_rust_callees_on_f1`]).
    F1,
}

/// Whether this compile is F1 with the trust-ir producer running (`-Ztrust-cg-frontend=trust-ir`
/// and `-Ztrust-ir-lower` or `--emit=trust-ir`): the compile on which the recorder runs whatever
/// `-Ztrust-verify` says and the analysis-seam eager demands of `clean_origin_mir` do not run.
/// F1 without the producer refuses every item before codegen (`-Ztrust-cg-frontend=trust-ir
/// requires the direct source (THIR) -> trust-ir producer`) and keeps the eager demands.
pub fn records_on_f1(tcx: TyCtxt<'_>) -> bool {
    tcx.sess.trust_cg_frontend_is_trust_ir()
        && (tcx.sess.trust_ir_lower_enabled()
            || tcx.sess.opts.output_types.contains_key(&rustc_session::config::OutputType::TrustIr))
}

/// The lane the recorder runs on in this compile, or `None` (a verification-off compile that is
/// not F1: nothing is recorded, `recorded: false`).
pub fn recorder_lane(tcx: TyCtxt<'_>) -> Option<RecorderLane> {
    if records_on_f1(tcx) {
        Some(RecorderLane::F1)
    } else if tcx.sess.trust_verification_enabled() {
        Some(RecorderLane::MirReearn)
    } else {
        None
    }
}

/// Trust (2026-09-16): every Clean-origin def this crate's own Rust code NAMES,
/// derived from HIR alone.
///
/// # Why a second answer to a question that already had one
///
/// `trust_thir_lower::crate_module::referenced_clean_origin_defs` answers the
/// same question off the direct-THIR producer's registry, and it is the better
/// answer where it is available: it sees the EMITTED call and address-taken
/// edges, so it cannot be fooled by a reference the front end resolved and the
/// body then discarded. But `crate_module::record` — the `mir_built` hook that
/// fills that registry — is gated on `sess.trust_ir_lower_enabled()`, so on a
/// crate compiled without `-Ztrust-ir-lower` the registry is EMPTY and the
/// question goes unanswered.
///
/// # What that cost
///
/// The Clean-origin CALL gate — `clean_origin_mir`'s refusal that a `def` whose
/// body reads a `static` or calls an impure Rust fn "cannot be called from Rust"
/// — runs inside the `optimized_mir` provider for the Clean-origin def. Nothing
/// demands that MIR for a binary crate compiled with `--emit metadata`:
/// `run_required_analyses` walks bodies but not this one, and
/// `trust_ensure_whole_crate_verification` returns early under
/// `-Ztrust-verify=off`. So the ONLY demand was the one inside
/// `rustc_interface`'s `-Ztrust-ir-lower` block, and the gate silently did not
/// run on any other lane.
///
/// Measured 2026-09-16 on `tests/ui/trust/clean_origin_static_read_refused.rs`,
/// whose `applyRead` reads a `static mut` and returns 7 and then 19 for the same
/// argument: the `plain_on`/`optimized_on` revisions refuse it and the
/// `plain_off`/`optimized_off` revisions compiled it, differing only in
/// `-Ztrust-ir-lower`. The island is a LANGUAGE surface (v7/D1) and its call
/// gate is kernel-backed and deliberately not behind `-Ztrust-verify=off`
/// (`docs/design/2026-08-04-two-language-compiler-architecture.md`), so an
/// artifact-lane flag must not decide whether it runs.
///
/// # What this answers, exactly
///
/// A NAME, not an emitted edge: any path in any local body that resolves to one
/// of `tcx.resolutions(()).clean_origin_defs`. That is deliberately WIDER than
/// the producer's answer — it includes a reference the body later drops — and
/// wider is the safe direction here, because the consequence of an extra entry
/// is that a `def` the user wrote down gets its own well-formedness checked,
/// while the consequence of a missing one is the silent acceptance above.
///
/// It is NOT widened to every Clean-origin def in the crate. The gate's own
/// message is "cannot be CALLED FROM RUST"; a `def` no Rust code names has no
/// call to refuse, and reporting one would invent a diagnostic about code the
/// user never wrote. Unnamed defs stay undemanded, exactly as before.
///
/// Empty (and free) when the crate has no `clean { … }` island at all, which is
/// every crate but a handful.
pub fn hir_named_clean_origin_defs(tcx: TyCtxt<'_>) -> Vec<rustc_span::def_id::LocalDefId> {
    use rustc_data_structures::fx::FxIndexSet;
    if tcx.resolutions(()).clean_origin_defs.is_empty() {
        return Vec::new();
    }
    struct NamedCleanDefs<'tcx> {
        tcx: TyCtxt<'tcx>,
        found: FxIndexSet<rustc_span::def_id::LocalDefId>,
    }
    impl<'v, 'tcx> Visitor<'v> for NamedCleanDefs<'tcx> {
        fn visit_expr(&mut self, expr: &'v rustc_hir::Expr<'v>) {
            if let rustc_hir::ExprKind::Path(rustc_hir::QPath::Resolved(_, path)) = &expr.kind
                && let rustc_hir::def::Res::Def(_, did) = path.res
                && let Some(local) = did.as_local()
                && crate::clean_origin_mir::is_clean_origin(self.tcx, local)
            {
                self.found.insert(local);
            }
            intravisit::walk_expr(self, expr);
        }
    }
    let mut visitor = NamedCleanDefs { tcx, found: FxIndexSet::default() };
    for owner in tcx.hir_body_owners() {
        let body = tcx.hir_body_owned_by(owner);
        visitor.visit_expr(&body.value);
    }
    visitor.found.into_iter().collect()
}

/// Collect the trust-ir spelling of every Clean-origin def in this crate on `lane`
/// ([`recorder_lane`]): on the MIR lane re-earning the kernel faithfulness verdict of each
/// def's emitted MIR, on F1 demanding no MIR at all (plan step 3.5).
pub fn collect_clean_origin_ir(tcx: TyCtxt<'_>, lane: RecorderLane) -> Vec<CleanOriginIrOutcome> {
    let defs: Vec<_> = clean_origin_defs(tcx).collect();
    // The GENERAL lane (totality campaign) runs whenever the crate has islands
    // at all — a crate whose declarations are all non-carrier (recursive
    // functions, inductives, matches) mints ZERO defs and still records.
    let has_islands = tcx.hir_crate_items(()).free_items().any(|item_id| {
        tcx.def_kind(item_id.owner_id) == rustc_hir::def::DefKind::GlobalAsm
            && matches!(tcx.hir_item(item_id).kind, rustc_hir::ItemKind::CleanIsland { .. })
    });
    if defs.is_empty() && !has_islands {
        return Vec::new();
    }
    if defs.is_empty() {
        // General-only crate: the environment refusal here is a SKIP, not the
        // registry lane's fatal — no minted def's binary is at stake.
        let Some(env) = clean_crate_environment(tcx) else {
            return Vec::new();
        };
        let env = &*env;
        let no_planner_rows = rustc_data_structures::fx::FxHashSet::default();
        return match collect_general_clean_ir(tcx, env, &no_planner_rows) {
            Some(general) => vec![CleanOriginIrOutcome::General(general)],
            None => Vec::new(),
        };
    }

    // Demand every gated body first (the MIR lane only). Under verification this is deliberate
    // fail-closed tightening (design §3.1, disclosed): a minted-but-never-
    // demanded def whose gate would refuse now fails deterministically at
    // finalize instead of compiling as a latent landmine behind a callable
    // name. For every def a verified compile already demands, this is a cache
    // hit.
    //
    // Trust (plan step 3.5, design §5.1): NOT on F1. F1 ships the trust-ir row, never this MIR,
    // so on F1 the MIR body is no codegen input and its gate is no verdict of this recorder; the
    // language refusals that ran inside it are decided on trust-ir instead
    // ([`check_rust_callees_on_f1`]), and the MIR lane's verdict is compared with F1's by the
    // test-only oracle. Each demand here is charged to the reach counter's `recorder` lane.
    if lane == RecorderLane::MirReearn {
        for &def in &defs {
            let _ask = clean_origin_reach::ask(tcx.sess, ReachLane::Recorder);
            let _ = tcx.optimized_mir(def.to_def_id());
        }
    }

    // One environment for the whole collection: `clean_crate_environment`
    // returns the session-cached kernel environment for this crate's islands.
    let Some(env) = clean_crate_environment(tcx) else {
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
    let env = &*env;

    let mut out = Vec::with_capacity(defs.len());
    let mut planner_emitted = rustc_data_structures::fx::FxHashSet::default();
    // Plan step 3.5: what this lane does with each def's MIR body, stated in the disclosure.
    let mir_gate = match lane {
        RecorderLane::MirReearn => MirGateAtSeam::Reearned,
        RecorderLane::F1 => MirGateAtSeam::NotOnF1,
    };
    for def in defs {
        let Some((name, span)) = clean_origin_registry_entry(tcx, def) else {
            // `defs` came from the registry; a missing row mid-iteration is a
            // compiler bug, not a user program state.
            tcx.dcx().bug("clean-origin def vanished from its own registry during collection");
        };
        let declaration = crate::clean_origin_mir::clean_source_name(tcx, &name, span);
        let def_index = def.to_def_id().index.as_u32();
        // The linkage key: must be spelled exactly as the THIR ledger spells its
        // callee def_paths (`with_no_trimmed_paths`), or IR-5's edge matching
        // silently finds nothing (fail-closed, but the lane looks landed while
        // linking nothing).
        let def_path =
            rustc_middle::ty::print::with_no_trimmed_paths!(tcx.def_path_str(def.to_def_id()));

        // Side A, re-planned from the kernel environment (fresh, independent
        // of the provider run's plan).
        // Trust (W5): planned over the SAME callee table the provider's gate
        // planned over, or a Lean-calls-Rust def would refuse here as "outside
        // the fragment" and trip the self-disagreement fatal below.
        let plan = match trust_clean_origin::plan_clean_origin_body_with_rust_callees_for_name(
            env,
            &declaration,
            &crate::clean_origin_mir::rust_callee_table(tcx),
        ) {
            Ok(plan) => plan,
            Err(refusal) => {
                // On the MIR lane the provider served a body for this def (demanded above), so
                // its plan succeeded; on F1 the mint planned it (a `DefId` is minted only for a
                // def `plan_clean_origin_body` can plan). Either way a seam-time plan refusal is
                // the environment disagreeing with itself.
                let earlier = match lane {
                    RecorderLane::MirReearn => {
                        "the code-generation plan for the same declaration succeeded moments \
                         earlier in this compile"
                    }
                    RecorderLane::F1 => {
                        "the mint planned the same declaration earlier in this compile (a def is \
                         minted only when it can be planned)"
                    }
                };
                tcx.dcx().span_fatal(
                    span,
                    format!(
                        "internal: the finalize-seam re-plan for Clean declaration `{name}` \
                         refused, while {earlier} ({}). These \
                         are two runs of one planner over one kernel environment; a \
                         disagreement means the environment or the plan pipeline is not \
                         deterministic. Please report it.",
                        refusal.note()
                    ),
                );
            }
        };

        match lane {
            // Side B, re-extracted from the exact cached body this compile uses,
            // and the verdict RE-EARNED. `admit_lowering` refusing a body the
            // provider's own gate admitted is the same self-disagreement class.
            RecorderLane::MirReearn => {
                let _ask = clean_origin_reach::ask(tcx.sess, ReachLane::Recorder);
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
            }
            // Trust (plan step 3.5, design §5.1): no MIR body on F1. What the MIR lane's
            // provider checked beside its gate, and F1 still needs, is checked here without it:
            // the signature every Rust call was type-checked against (`fn_sig`, fed at the mint)
            // must be the one the plan's carriers denote, or the trust-ir row would compute at a
            // signature no caller was checked against. Purity and the cross-language cycle of a
            // `RustCallChain` plan are decided on trust-ir once the module exists
            // ([`check_rust_callees_on_f1`]), so the plan's callee identities are kept for it.
            RecorderLane::F1 => {
                crate::clean_origin_mir::check_fed_signature(tcx, def, &plan, &name, env, span);
                if let trust_clean_origin::CleanOriginShape::RustCallChain { nodes } = plan.shape()
                {
                    let callees: Vec<rustc_span::def_id::DefId> = nodes
                        .iter()
                        .map(|node| node.callee)
                        .collect::<std::collections::BTreeSet<_>>()
                        .into_iter()
                        .map(|index| {
                            crate::clean_origin_mir::resolve_rust_callee(tcx, &plan, index, span)
                        })
                        .collect();
                    tcx.sess.with_trust_compiler_state::<F1RustCallPlans, _>(|plans| {
                        plans.0.push(F1RustCallPlan {
                            def,
                            name: name.clone(),
                            def_path: def_path.clone(),
                            span,
                            callees,
                        })
                    });
                }
            }
        }

        // The trust-ir spelling. Ids are placeholders: identity belongs to the
        // owning Module, and the append seam (`clean_origin_join`) mints the
        // real `FuncId`/`FuncTyId` at insertion.
        let shape = shape_tag(plan.shape());
        // Trust (WS5.2, F-087/F-092): the minted Rust item's LINK-TIME SYMBOL. Every row
        // this def can become (planner or Rust-call) is NAMED by it — never by the bare Lean
        // leaf, which is how an island's `m::program` collided with a Rust `program` — and a
        // Rust caller's declaration of the item carries the same symbol, which is what lets
        // the join put the definition in that declaration's row. A Clean-origin def is a
        // monomorphic Rust item, so a refusal here is a compiler disagreement for a gate
        // target (fatal) and a disclosed skip otherwise.
        let link_symbol = match trust_thir_lower::link_symbol::definition_link_symbol(
            tcx,
            def.to_def_id(),
            &def_path,
        ) {
            Ok(symbol) => symbol,
            Err(reason) => {
                let reason =
                    trust_ir_precursor_refusal(tcx, span, &plan, &name, "link-symbol", reason);
                out.push(CleanOriginIrOutcome::Skipped(CleanOriginIrSkip {
                    def_index,
                    def_path,
                    clean_name: name,
                    shape,
                    gate_target: trust_clean_ir_gate::gate_targets(&plan),
                    reason,
                }));
                continue;
            }
        };
        // Trust: a Rust call cannot be emitted into the placeholder mini-module.
        // Preserve the freshly checked plan and exact registered source identities
        // until the owning module can bind them to its actual spliced Rust bodies.
        // The general lane remains eligible: if this pending spelling cannot be
        // linked, its existing computational body must not disappear from coverage.
        if matches!(plan.shape(), trust_clean_origin::CleanOriginShape::RustCallChain { .. }) {
            match collect_rust_call_callees(tcx, &plan, span) {
                Ok(callees) => {
                    out.push(CleanOriginIrOutcome::RustCalls(CleanOriginRustCallRecord {
                        def_index,
                        def_path,
                        link_symbol,
                        clean_name: name,
                        plan,
                        callees,
                        mir_gate,
                    }))
                }
                Err(reason) => {
                    let reason = trust_ir_precursor_refusal(
                        tcx,
                        span,
                        &plan,
                        &name,
                        "Rust-call identity collection",
                        reason,
                    );
                    out.push(CleanOriginIrOutcome::Skipped(CleanOriginIrSkip {
                        def_index,
                        def_path,
                        clean_name: name,
                        shape,
                        gate_target: trust_clean_ir_gate::gate_targets(&plan),
                        reason,
                    }));
                }
            }
            continue;
        }
        match trust_clean_ir::trust_ir_func_ty(plan.signature()) {
            Ok(signature) => {
                match trust_clean_ir::emit_clean_origin_function(
                    &plan,
                    FuncId::new(0),
                    FuncTyId::new(0),
                ) {
                    Ok(mut function) => {
                        // Trust (WS5.2): name the Function by the Rust item's link-time symbol
                        // (the Lean spelling moves to `display_path`) BEFORE the carrier gate
                        // mints its token and before the TV mint, so both authenticate the
                        // final Function. A binding refusal is an emitter disagreement: fatal
                        // for a gate target, a disclosed skip otherwise.
                        if let Err(reason) =
                            trust_thir_lower::link_symbol::bind_clean_origin_link_symbol(
                                &mut function,
                                &link_symbol,
                            )
                        {
                            let reason = trust_ir_precursor_refusal(
                                tcx,
                                span,
                                &plan,
                                &name,
                                "link-symbol",
                                reason,
                            );
                            out.push(CleanOriginIrOutcome::Skipped(CleanOriginIrSkip {
                                def_index,
                                def_path,
                                clean_name: name,
                                shape,
                                gate_target: trust_clean_ir_gate::gate_targets(&plan),
                                reason,
                            }));
                            continue;
                        }
                        // W2 carrier gate: this exact bounded shape may no longer
                        // escape on the historical kernel-TV/ungated rung. The
                        // independent production reflector reads `function`
                        // itself (not the sealed shape's operands), rebuilds a
                        // Clean term, and asks the kernel for whole-term defeq.
                        // A targeted refusal is an internal wrong-code signal:
                        // fatal here, never converted to a skip or weaker tier.
                        let gate_target = trust_clean_ir_gate::gate_targets(&plan);
                        let gate = if gate_target {
                            Some(
                                trust_clean_ir_gate::admit_clean_origin(
                                    env, &plan, def_index, &def_path, &signature, &function,
                                )
                                .unwrap_or_else(|refusal| {
                                    tcx.dcx().span_fatal(
                                        span,
                                        format!(
                                            "internal: the independently reflected TrustIR body \
                                             for targeted Clean `{shape}` `{name}` was refused at \
                                             the carrier gate ({}). This body is never demoted to \
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
                        // Trust (plan step 3.4, design §4.2): the environment this row's
                        // verdict comes from, named beside the token so the append seam can
                        // refuse a token minted in another one. Targeted rows only (the
                        // join's exact-set contract is token <=> environment); a closure that
                        // cannot be digested is the same fatal class as a gate refusal.
                        let gate_environment = gate_target.then(|| {
                            trust_clean_ir_gate::GateEnvironment::of(env, plan.declaration())
                                .unwrap_or_else(|refusal| {
                                    tcx.dcx().span_fatal(
                                        span,
                                        format!(
                                            "internal: the kernel environment of targeted Clean \
                                             `{shape}` `{name}` could not be digested for its \
                                             carrier-gate token ({}). The row is never published \
                                             without the environment its verdict was decided in; \
                                             report this.",
                                            refusal.note()
                                        ),
                                    )
                                })
                        });
                        let (tv, tv_note) =
                            mint_kernel_tv(env, &declaration, &name, shape, &signature, &function);
                        planner_emitted.insert(declaration.clone());
                        out.push(CleanOriginIrOutcome::Emitted(CleanOriginIrRecord {
                            def_index,
                            def_path,
                            clean_name: name,
                            shape,
                            gate_target,
                            signature,
                            function,
                            gate,
                            gate_environment,
                            tv,
                            tv_note,
                            mir_gate,
                        }))
                    }
                    Err(refusal) => {
                        let reason = trust_ir_precursor_refusal(
                            tcx,
                            span,
                            &plan,
                            &name,
                            "function-emission",
                            trust_clean_ir::planner_skip_reason(plan.shape(), &refusal),
                        );
                        out.push(CleanOriginIrOutcome::Skipped(CleanOriginIrSkip {
                            def_index,
                            def_path,
                            clean_name: name,
                            shape,
                            gate_target: trust_clean_ir_gate::gate_targets(&plan),
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
                    trust_clean_ir::planner_skip_reason(plan.shape(), &refusal),
                );
                out.push(CleanOriginIrOutcome::Skipped(CleanOriginIrSkip {
                    def_index,
                    def_path,
                    clean_name: name,
                    shape,
                    gate_target: trust_clean_ir_gate::gate_targets(&plan),
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
    if let Some(general) = collect_general_clean_ir(tcx, env, &planner_emitted) {
        out.push(CleanOriginIrOutcome::General(general));
    }
    out
}

// Trust: collect identities, never module ids. On the MIR lane PURE was demanded above and the
// cached MIR was independently re-admitted before this function is reached; on F1 (plan step
// 3.5) purity and the cross-language cycle are decided on trust-ir after the finalize
// ([`check_rust_callees_on_f1`]) and a refusal there is fatal before codegen. These facts do not
// establish a Rust callee's refinement or NoPanic judgment.
fn collect_rust_call_callees(
    tcx: TyCtxt<'_>,
    plan: &trust_clean_origin::CleanOriginPlan,
    span: rustc_span::Span,
) -> Result<Vec<CleanOriginRustCallee>, String> {
    use std::collections::BTreeSet;

    let trust_clean_origin::CleanOriginShape::RustCallChain { nodes } = plan.shape() else {
        return Err("internal: Rust call identity collection requires a RustCallChain plan".into());
    };
    trust_clean_ir::trust_ir_func_ty(plan.signature()).map_err(|refusal| refusal.to_string())?;
    let used: BTreeSet<_> = nodes.iter().map(|node| node.callee).collect();
    used.into_iter()
        .map(|plan_index| {
            let def_id = crate::clean_origin_mir::resolve_rust_callee(tcx, plan, plan_index, span);
            let Some(local_def_id) = def_id.as_local() else {
                return Err("Rust call recording requires an exact registered local function; \
                    imported callee identities need a checked cross-crate transport"
                    .into());
            };
            let sig = tcx.fn_sig(def_id).instantiate_identity().skip_binder();
            if sig.abi() != rustc_abi::ExternAbi::Rust || sig.c_variadic() {
                return Err(format!(
                    "Rust call recording for `{}` requires its exact non-variadic Rust ABI; \
                     the registered callee has ABI {:?} and variadic={}. Options: extend the \
                     checked call transport for that ABI before recording this edge",
                    plan.callees()[plan_index].clean_name,
                    sig.abi(),
                    sig.c_variadic(),
                ));
            }
            let signature = trust_clean_ir::rust_callee_func_ty(&plan.callees()[plan_index])
                .map_err(|refusal| refusal.to_string())?;
            Ok(CleanOriginRustCallee::from_def_id(
                tcx,
                plan_index,
                local_def_id,
                signature,
                &plan.callees()[plan_index],
            ))
        })
        .collect()
}

// WS5.14: `planner_skip_reason` moved to `trust_clean_ir`, beside the refusal
// it annotates, so its text is unit-testable against real planned Clean
// declarations instead of only through a stage-1 compile. It now matches on the
// SHAPE VARIANT rather than on `shape_tag`'s rendered string, so renaming a
// coverage tag cannot silently drop the note.

/// Preserve the historical skip-with-reason behavior outside W2, but make
/// every precursor refusal fatal once the sealed plan is a carrier-gate target
/// (`trust_clean_ir_gate::gate_targets`: wrapping-binop, composed, projection and
/// constant-uint at an exact UInt carrier, each only when the declaration's own value is
/// that body — `CleanOriginPlan::source_is_direct`). Calling this helper from BOTH lowering Err arms is
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
    if trust_clean_ir_gate::gate_targets(plan) {
        tcx.dcx().span_fatal(
            span,
            format!(
                "internal: targeted Clean `{}` `{clean_name}` refused during TrustIR \
                 {stage} ({detail}). This targeted disagreement is fatal and is never recorded \
                 as a skip, rerouted to the general lane, or demoted; report the compiler bug.",
                shape_tag(plan.shape())
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
        // Trust (W6, Rust-calls-Clean): a comparison returned as `Bool`.
        S::DecideComparison { .. } => "comparison-value",
        // Trust (W6, Rust-calls-Clean): a boolean negation/connective.
        S::BoolNot { .. } => "bool-not",
        S::BoolConnective { .. } => "bool-connective",
        // Trust: direct Boolean expression emission grants no new gate tier.
        S::BoolExpression { .. } => "bool-expression",
        // Trust: bounded conditional dataflow retains its own disclosed coverage.
        S::UnsignedConditional { .. } => "unsigned-conditional",
        S::StructuralNatRec { .. } => "structural-nat-rec",
        S::WellFoundedNatRec { .. } => "well-founded-nat-rec",
        // Trust (W5): recorded as a disclosed skip — `trust-clean-ir` refuses
        // it by name (`ShapeNotYetSpelled`) and it is never a gate target.
        S::RustCallChain { .. } => "rust-call-chain",
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
    declaration: &clean_kernel::Name,
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
                    "kernel-tv unreachable: the shape is a recording-path skip already (its \
                 `Nat -> Nat` signature is refused by the carrier walk above, before the \
                 body emitter runs — see `trust_clean_ir::planner_skip_reason` for what the actual \
                 blocker is), and the Nat-mod-2^w vocabulary cannot state an unbounded \
                 computation anyway. Options: land the design's §6.4 Nat-runtime \
                 modelling first; keep faithfulness at the MIR lane's kernel recursion \
                 gates."
                        .to_string(),
                ),
            );
        }
        "comparison-value" => {
            return (
                None,
                Some(
                    "kernel-tv not attempted: the shape emits an `Inst::ICmp` producing an \
                 `i1` result, and the denotation fragment has no ICmp/Bool-valued rule — \
                 its only Bool former is the Fragment-3a CondBr diamond's branch \
                 condition, not a returned decision. Options: (1) add an ICmp-to-Bool \
                 rule to BOTH denotation copies in one increment with probes-first \
                 kernel-agreement evidence; (2) rely on the MIR lane's admit_lowering, \
                 which already gates this shape at the carrier via \
                 `admit_comparison_function` and the kernel def-eq gate; (3) leave the \
                 row structural."
                        .to_string(),
                ),
            );
        }
        "bool-not" | "bool-connective" => {
            return (
                None,
                Some(
                    "kernel-tv not attempted: the shape emits the Bool connective \
                 `Inst::BinOp(BXor|BAnd|BOr)` (negation spelled `bxor %b, true`, WS5.13) \
                 at the `i1` result carrier, and the MINT's denotation copy has no `bool` \
                 carrier and no `B*` rule — measured at the pinned clean: \
                 `clean_reflect::denote_function` refuses a `bool` return (its fragment is \
                 U8/U16/U32/U64) and every `BAnd`/`BOr`/`BXor`, fail-closed, so no \
                 certificate can be minted. The RE-CHECK copy is already ahead of it: \
                 trust-ir-build's `clean_backend_tv` admits `Bool` and denotes \
                 `band`/`bor`/`bxor` as `Bool.and`/`Bool.or`/`Bool.xor` at the pinned \
                 trust-ir. Options: (1) add the `bool` carrier and the `B*` rules to \
                 `clean_reflect`'s denotation with probes-first kernel-agreement evidence \
                 against the trust-ir-build copy; (2) rely on the \
                 MIR lane's admit_lowering, which already gates this shape at `Bool` via \
                 `admit_bool_value_function` and the kernel def-eq gate; (3) leave the \
                 row structural."
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
    let Some(defn) = env.get_const(declaration).and_then(|constant| constant.value.clone()) else {
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
    // Trust (CLEAN-TV-SOURCE-DICTIONARY-ENV-1): the source is denoted IN this island's
    // checked kernel environment. Clean 6fa7151da made a class dispatcher's meaning the
    // stored field of its actual dictionary (`a + b` is `HAdd.hAdd … inst a b`, and a
    // valid `HAdd` dictionary may store something other than addition), and a NAMED
    // dictionary (`instHAddUInt64`, `instOfNatUInt64 1`) resolves only by unfolding it in
    // the environment the source was checked in; the environment-free `denote_source`
    // refuses every one, which left every carrier-gated `+`/`-`/`*` row without its
    // kernel-TV companion (fatal). The legacy wrapper still refuses a walk that needs
    // an original-source equation (a propositional `ite`), which this Eq.refl mint
    // cannot carry, so that refusal stays a refusal.
    let rhs = match clean_reflect::denote_source_in_environment(
        &defn,
        lhs.width,
        &lhs.callees,
        &records,
        env,
    ) {
        Ok(denotation) => denotation,
        // Trust (2026-09-28): read the definition through the SAME helper
        // expansion the planner read it through (`expand_named_lean_calls`), and
        // only when the declaration as written is outside the fragment, so no
        // row that minted before changes. `def viaId x := idA x` plans as a
        // projection through that expansion, which makes it a gate target, and
        // a target without a TV companion is fatal: every verify-on build of a
        // crate holding such a `def` died, called or not. The kernel still
        // decides the TV equation, and the carrier gate still reads the
        // ORIGINAL declaration.
        Err(refusal) => {
            let expanded = trust_clean_origin::expand_named_lean_calls(env, declaration, &defn);
            match expanded.as_ref().map(|expanded| {
                expanded.as_ref().map(|expanded| {
                    clean_reflect::denote_source_in_environment(
                        expanded,
                        lhs.width,
                        &lhs.callees,
                        &records,
                        env,
                    )
                })
            }) {
                Ok(Some(Ok(denotation))) => denotation,
                _ => {
                    return (
                        None,
                        Some(format!(
                            "kernel-tv not attempted: the kernel definition is outside the \
                         source denotation fragment ({refusal:?}), also after expanding its \
                         Lean helper calls. Options: widen BOTH denotation copies' source \
                         recognition in one increment, or leave the row structural."
                        )),
                    );
                }
            }
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
                // This TV lane has no statement/environment binding carrier.
                binding: None,
            }),
        },
        // v41 `assurance` is a COVERAGE projection from a native evidence
        // bundle. A Clean-origin translation-validation certificate has no
        // such bundle: its discharge is a kernel decision about a denotation,
        // not a bounded or unbounded native check. `None` is NOT RECORDED,
        // which a fail-closed consumer must read as UNKNOWN coverage — the
        // only honest value here.
        assurance: None,
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
//
// Trust (CLEAN-GENERAL-DEFERRED-1): the lane compiles from `clean_crate_environment`,
// which holds the PRE-ADMISSION prefix only (E9-DEFERRED-SUFFIX-ENV-1). A
// declaration of the deferred suffix is skipped by placement with its own
// reason ([`DEFERRED_ISLAND_SKIP`]) and is never looked up in that environment.

/// Trust (CLEAN-GENERAL-DEFERRED-1): the general lane's skip reason for a declaration
/// in the deferred island suffix. Before, such a declaration was looked up in
/// the prefix environment, missed, and was recorded as "absent from the kernel
/// environment — report this", a compiler defect that does not exist.
const DEFERRED_ISLAND_SKIP: &str = "deferred-island: declared in an island at or after the \
    first island that names `trust_import_*`. This lane compiles from the pre-admission \
    environment, the islands before that one; the deferred suffix is elaborated only after this \
    crate's program admissions are minted, against admissions that environment does not hold, so \
    the general lane does not compile its declarations yet. A capability gap of this lane, not a \
    compiler defect. Options: move the declaration into an island placed before the first island \
    that names `trust_import_*`, or leave it PROOF-side — recording is not calling, and nothing \
    breaks.";

fn collect_general_clean_ir(
    tcx: TyCtxt<'_>,
    env: &clean_kernel::Environment,
    planner_emitted: &rustc_data_structures::fx::FxHashSet<clean_kernel::Name>,
) -> Option<GeneralCleanIr> {
    use rustc_ast::CleanDeclKind;

    // Trust (CLEAN-GENERAL-DEFERRED-1): the islands `env` does not hold. `env` came from
    // `clean_crate_environment`, which returns one only after recovering every
    // island's bytes through the walk this reads, so `None` is a compiler bug.
    let Some(deferred_islands) = crate::clean_origin_mir::deferred_suffix_islands(tcx) else {
        tcx.dcx().bug(
            "the general Clean lane holds a kernel environment for this crate's islands, but \
             their sources could not be recovered for the deferred-suffix partition",
        );
    };
    // Every NAMED island declaration, in authored order, one entry per name,
    // carrying the surface kind — the batch loop below needs it to refuse the
    // proof-side kinds before the kernel lookup — and whether its island is in
    // the deferred suffix, which `env` does not hold.
    let mut names: Vec<(String, clean_kernel::Name, CleanDeclKind, bool)> = Vec::new();
    let mut seen = rustc_data_structures::fx::FxHashSet::default();
    for item_id in tcx.hir_crate_items(()).free_items() {
        if tcx.def_kind(item_id.owner_id) != rustc_hir::def::DefKind::GlobalAsm {
            continue;
        }
        let item = tcx.hir_item(item_id);
        let rustc_hir::ItemKind::CleanIsland { decls, .. } = item.kind else { continue };
        let deferred = deferred_islands.contains(&item_id.owner_id.def_id);
        for decl in decls {
            if decl.name.as_str().is_empty() {
                continue;
            }
            // Kinds this lane CONSIDERS. `Def`/`Codef`/`Instance`/`Opaque`
            // can carry a computational value. `Theorem`/`Axiom` never can —
            // they are kept here only so each still gets a disclosed
            // `NotComputational` row, and are refused BY KIND in the batch
            // loop below (see the comment there: the kernel lookup does NOT
            // refuse a theorem). Everything else (example/inductive/structure/
            // commands) is out of this lane's scope entirely.
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
            let declaration = crate::clean_origin_mir::clean_source_name(tcx, &name, decl.span);
            // Already recorded by the planner lane at a stronger tier — the
            // general lane is defined as what lies OUTSIDE the planner.
            if planner_emitted.contains(&declaration) {
                continue;
            }
            if seen.insert(declaration.clone()) {
                names.push((name, declaration, decl.kind, deferred));
            }
        }
    }
    if names.is_empty() {
        return None;
    }

    let mut rows = Vec::with_capacity(names.len());
    let mut batch: Vec<clean_compiler::Decl> = Vec::new();
    let mut batch_names: Vec<String> = Vec::new();
    let mut batch_sources: Vec<(String, clean_kernel::Name)> = Vec::new();
    for (name, declaration, kind, deferred) in names {
        // A PROOF-SIDE DECLARATION NEVER ENTERS THE COMPILED BATCH.
        //
        // Refused here BY KIND, because the kernel lookup below does not
        // refuse it — the two halves differ, and only one of them is a gap:
        //
        //   * `axiom` registers as `ConstantInfo { value: None }`
        //     (clean-kernel `env/decl_add.rs`, the `Declaration::Axiom` arm),
        //     so `constant_to_decl` already returns `Ok(None)` and the row is
        //     already `NotComputational`. For axioms this arm is
        //     belt-and-braces: it states the invariant rather than repairing
        //     a live hole.
        //
        //   * `theorem` registers as `ConstantInfo { value: Some(proof),
        //     kind: ConstantKind::Theorem }` (same file, the
        //     `Declaration::Theorem` arm — the kernel keeps the PROOF TERM as
        //     the value). `constant_to_decl` therefore sees a value, finds the
        //     declared type Prop-valued (`prop_valued_const`), and returns
        //     `Ok(Some(decl))` with the erased-stub body — which
        //     `emit_trust_ir` lowers without complaint (`IRType::Erased` ->
        //     `Ty::Ptr`). The proof object would be PUBLISHED as a callable
        //     function row in the shared two-language module and counted
        //     `Compiled` in the coverage census. Measured on the 2026-08-30
        //     baseline corpus: 20 theorem rows recorded `general:compiled`
        //     (e.g. `le_self` in `clean_symbol_graph_axiom_disclosed_control.rs`,
        //     an island whose sole declaration is a theorem), against
        //     `not-computational (proof-only): 0`. A theorem has no
        //     computational meaning; this is the real fix.
        //
        // The authority is the Clean parser's SYNTACTIC classification, which
        // is the right one for a fail-closed exclusion: if the source said
        // `theorem`, this lane declines to compile it whatever the kernel
        // later made of it. `GeneralOutcome::NotComputational` is already
        // documented as the theorem/axiom/opaque/ctor disposition, and
        // `append_clean_origin` already discloses it as `not-computational`.
        if matches!(kind, CleanDeclKind::Theorem | CleanDeclKind::Axiom) {
            rows.push(GeneralRow { clean_name: name, outcome: GeneralOutcome::NotComputational });
            continue;
        }
        // Trust (CLEAN-GENERAL-DEFERRED-1): skipped by PLACEMENT, after the proof-side
        // kinds (a deferred theorem is still `NotComputational`, which is true
        // wherever it is placed) and before the lookup. `env` holds none of the
        // suffix's declarations, so a lookup could only miss, or answer for a
        // different constant that happens to share the name.
        if deferred {
            rows.push(GeneralRow {
                clean_name: name,
                outcome: GeneralOutcome::Skipped { reason: DEFERRED_ISLAND_SKIP.to_string() },
            });
            continue;
        }
        let Some(info) = env.get_const(&declaration) else {
            rows.push(GeneralRow {
                clean_name: name,
                outcome: GeneralOutcome::Skipped {
                    reason: "declared in a pre-admission island but absent from the kernel \
                             environment — report this (the session admitted the island, so \
                             every named declaration should be registered)"
                        .to_string(),
                },
            });
            continue;
        };
        match clean_compiler::constant_to_decl(env, info) {
            Ok(Some(decl)) => {
                batch_sources.push((
                    clean_compiler::emit_trust_ir_link::link_symbol(&decl.name),
                    declaration,
                ));
                batch.push(decl);
                batch_names.push(name);
            }
            Ok(None) => rows
                .push(GeneralRow { clean_name: name, outcome: GeneralOutcome::NotComputational }),
            // Trust: the refusal's Display text, never its Debug form (Clean R80;
            // `general_declaration_refusal`).
            Err(error) => rows.push(GeneralRow {
                clean_name: name,
                outcome: GeneralOutcome::Skipped { reason: general_declaration_refusal(&error) },
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
            if let Err(error) = source_equations::recheck(&module, env, &batch_sources, &report) {
                let reason = format!(
                    "source-equation-refused-general: {error}. The whole batch is skipped before \
                     proof stripping; no source theorem or body license is inferred from absence."
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
            if let Err(error) = source_equations::strip_for_general(&mut module) {
                let reason = format!("claim-free-refused-general: {error}");
                for name in batch_names {
                    rows.push(GeneralRow {
                        clean_name: name,
                        outcome: GeneralOutcome::Skipped { reason: reason.clone() },
                    });
                }
                return Some(GeneralCleanIr { rows, module: None });
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
            // Trust: the refusal's Display text, never its Debug form (Clean R80;
            // `general_batch_refusal`).
            let reason = general_batch_refusal(&error);
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

// ── the Rust-callee rules on F1 (plan step 3.5) ─────────────────────────────
//
// On the MIR lane a `RustCallChain` def's Rust callees are checked inside the
// `clean_origin_mir` provider: purity by `rust_callee_is_pure` over MIR, the
// cross-language cycle by `callee_reaches_a_gate_on_this_stack`. F1 builds no such
// MIR (design §5.7), so on F1 both are decided over the crate's trust-ir once the
// finalize has assembled it and the effect-conservation check has judged it
// (`trust_thir_lower::clean_origin_purity`, design §5.1, §2.3, §12 item 8). They are
// the LANGUAGE's refusals, fatal on F1 as on the MIR lane, whatever `-Ztrust-verify`
// says.

/// One `RustCallChain` plan the F1 recorder saw: the def, and the exact Rust definitions its
/// plan calls (resolved through the registry the mint and the MIR lane resolve through).
struct F1RustCallPlan {
    def: rustc_span::def_id::LocalDefId,
    name: String,
    def_path: String,
    span: rustc_span::Span,
    callees: Vec<rustc_span::def_id::DefId>,
}

/// Session state: the F1 recorder's `RustCallChain` plans, for [`check_rust_callees_on_f1`].
#[derive(Default)]
struct F1RustCallPlans(Vec<F1RustCallPlan>);

// Trust: the general lane's two refusal reasons (Clean R80; Clean R151
// consumer (3); `docs/DECISION_QUEUE.md` R80-CONSUMERS-1). They reach the user
// through the coverage sidecar (`clean_origin.general[].reason`), so they carry
// the refusal's Display text: what it says, in the user's terms, with its own
// options. The Debug form they printed before named Rust fields
// (`ImplementedByOrder { referrer: Name(..), .. }`) and dropped the options.
fn general_declaration_refusal(error: &clean_compiler::CompilerError) -> String {
    format!(
        "the general L5CNF lowering refused this declaration: {}",
        with_options(
            error,
            "Options: spell the definition inside the supported computational surface, or \
             leave it PROOF-side — recording is not calling, and nothing breaks."
        )
    )
}

// Trust: see `general_declaration_refusal`.
fn general_batch_refusal(error: &clean_compiler::pass_manager::PipelineError) -> String {
    format!(
        "the general pipeline refused the island batch: {}",
        with_options(
            error,
            "Options: the refusal names the declaration and construct — spell it inside the \
             compilable surface, split the island so the refusing declaration stands alone, or \
             leave it PROOF-side."
        )
    )
}

// Trust: a refusal's Display text closed by exactly one full stop (Clean's
// `implemented-by-order` text ends its own sentence), then the lane's options
// unless the refusal names options of its own: that text's ("write the
// attribute on the declaration, or before every use of it") are about the
// attribute, and the lane's, about the computational surface, would not apply.
fn with_options(error: &dyn std::fmt::Display, lane_options: &str) -> String {
    let text = error.to_string();
    let sentence = if text.ends_with('.') { text } else { format!("{text}.") };
    if sentence.contains("Options:") { sentence } else { format!("{sentence} {lane_options}") }
}

/// The Clean def's refusal, in the MIR lane's own headline (`clean_origin_mir::refuse`): the
/// language refused the program, the rule and the options are in the note.
fn refuse_on_f1(
    tcx: TyCtxt<'_>,
    span: rustc_span::Span,
    name: &str,
    note: String,
) -> rustc_span::ErrorGuaranteed {
    tcx.dcx()
        .struct_span_err(span, format!("Clean declaration `{name}` cannot be called from Rust"))
        .with_note(note)
        .emit_err()
}

/// Plan step 3.5 (design §5.1): THE CLEAN LANGUAGE'S RUST-CALLEE RULES ON F1, after
/// `trust_ir_crate_finalize`. Every `RustCallChain` def the recorder saw is judged on trust-ir:
///
/// * a CROSS-LANGUAGE CYCLE on the published module's call graph is refused;
/// * each Rust callee's PURITY is decided on its conserved trust-ir effect census
///   (`clean_origin_purity::rust_callee_purity`): IMPURE is refused; PURE passes; UNDECIDED
///   (an upstream body, a body whose trust-ir is not conserved, a def the recorder published no
///   row for) is not a pass, and the MIR walk is consulted for it TO REFUSE ONLY
///   (docs/DECISION_QUEUE.md STEP3.5-PURITY-UNDECIDED): it never turns UNDECIDED into PURE, and it
///   stops at every Clean-origin def instead of building its `clean_origin_mir` body, so F1 never
///   accepts a program the MIR lane refuses while no `clean_origin_mir` body is read.
///
/// When the finalize published no module (a verification-off compile reports its finalization
/// errors as warnings and goes on, and F1 then refuses every item for want of a handoff), the
/// census has nothing to read, so the MIR lane's language gate runs instead, exactly as before
/// step 3.5: every HIR-named or MIR-referenced def's `clean_origin_mir` body is demanded, charged
/// to the reach counter's `recorder` lane, which F1 prints. Every refusal is reported, then the
/// compile stops.
pub fn check_rust_callees_on_f1(tcx: TyCtxt<'_>) {
    use trust_thir_lower::clean_origin_purity::{
        CalleePurity, cross_language_cycles, disclosed_emitted_rows, rust_callee_purity,
    };
    let plans = tcx.sess.with_trust_compiler_state::<F1RustCallPlans, _>(std::mem::take).0;
    if tcx.resolutions(()).clean_origin_defs.is_empty() {
        return;
    }
    let conserved = trust_thir_lower::effect_conservation::conserved_function_ids(tcx.sess);
    let published = trust_thir_lower::crate_module::with_published_crate_module(tcx.sess, |p| {
        p.ok().map(|p| p.module().clone())
    });
    let (Some(module), Ok(conserved)) = (published, conserved) else {
        crate::clean_origin_references::demand_referenced(tcx);
        for def in hir_named_clean_origin_defs(tcx) {
            let _ask = clean_origin_reach::ask(tcx.sess, ReachLane::Recorder);
            let _ = tcx.optimized_mir(def.to_def_id());
        }
        return;
    };
    let mut refused: Option<rustc_span::ErrorGuaranteed> = None;
    let rows = disclosed_emitted_rows(&module);
    // Human-facing diagnostics name the source def path (`display_path`), not the
    // link-time symbol `name` has carried since WS5.2 (F-087) — the MIR lane's twin
    // diagnostic says `fn inc`, and `fn _RNvCs...3inc` tells the author nothing.
    let name_of = |id: trust_ir::FuncId| {
        module.function_by_id(id).map_or_else(
            || format!("FuncId({})", id.index()),
            |f| f.display_path.clone().unwrap_or_else(|| f.name.clone()),
        )
    };
    let def_of_path = |def_path: &str| {
        clean_origin_defs(tcx).find(|def| {
            rustc_middle::ty::print::with_no_trimmed_paths!(tcx.def_path_str(def.to_def_id()))
                == def_path
        })
    };

    // The cross-language cycle, on the published module's call graph.
    let mut cyclic = rustc_data_structures::fx::FxHashSet::default();
    for cycle in cross_language_cycles(&module) {
        let path: Vec<String> =
            cycle.path.iter().map(|id| format!("`{}`", name_of(*id))).collect();
        let attributed = rows
            .iter()
            .find(|row| row.func_id == cycle.clean)
            .and_then(|row| def_of_path(&row.def_path))
            .and_then(|def| clean_origin_registry_entry(tcx, def).map(|entry| (def, entry)));
        let Some((def, (name, span))) = attributed else {
            // Fail closed: a cycle through a Clean-origin Function this compile cannot map back
            // to a minted def (no emitted disclosure row, or a row whose path names no def) is
            // still a cycle of the program. It is refused at the crate, never skipped.
            refused = Some(
                tcx.dcx()
                    .struct_span_err(
                        tcx.def_span(rustc_hir::def_id::CRATE_DEF_ID),
                        format!(
                            "a Clean-origin function takes part in a CROSS-LANGUAGE CYCLE ({}, on \
                             this crate's published trust-ir call graph: F1 decides the rule \
                             there, plan step 3.5)",
                            path.join(" -> ")
                        ),
                    )
                    .with_note(
                        "a Clean `def` may not take part in a cross-language cycle. This cycle \
                         passes through a Clean-origin trust-ir Function that no emitted \
                         clean-origin disclosure row maps to a minted def, so it cannot be \
                         attributed to a declaration; it is refused rather than skipped. \
                         options: give the Rust side a base case that does not call back into \
                         Clean; or move the recursion wholly into Clean",
                    )
                    .emit_err(),
            );
            continue;
        };
        cyclic.insert(def);
        let rust = cycle
            .path
            .iter()
            .find(|id| {
                module
                    .function_by_id(**id)
                    .is_some_and(|f| f.producer != Some(trust_ir::Producer::Clean))
            })
            .map_or_else(String::new, |id| name_of(*id));
        refused = Some(refuse_on_f1(
            tcx,
            span,
            &name,
            format!(
                "a Clean `def` may not take part in a CROSS-LANGUAGE CYCLE, but `{name}` calls \
                 Rust `fn {rust}`, which leads back to `{name}` ({}, on this crate's published \
                 trust-ir call graph: F1 decides the rule there, plan step 3.5). The \
                 faithfulness gate models a Rust callee as a pure value the kernel already \
                 checked; a callee whose own body depends on this declaration has no such value, \
                 and the emitted body would have to be gated against itself. options: give the \
                 Rust side a base case that does not call back into `{name}`; or move the \
                 recursion wholly into Clean, where it is checked as a well-founded definition; \
                 or compute the recursive part in Rust and pass its result into the `def` as an \
                 argument.",
                path.join(" -> ")
            ),
        ));
    }

    // Purity, on the conserved trust-ir effect census, with the MIR walk as a refusal-only
    // backstop where the census cannot decide. The backstop is told every plan's Rust callees, so
    // it can walk through a Clean-origin def it reaches and see a cycle the module cannot show
    // (a Rust callee the producer did not assemble has no body, so no edge, in the module).
    let plan_callees: rustc_data_structures::fx::FxHashMap<
        rustc_span::def_id::LocalDefId,
        Vec<rustc_span::def_id::DefId>,
    > = plans.iter().map(|plan| (plan.def, plan.callees.clone())).collect();
    for plan in &plans {
        if cyclic.contains(&plan.def) {
            continue;
        }
        let row = rows.iter().find(|row| row.def_path == plan.def_path);
        let verdict = match row.and_then(|row| module.function_by_id(row.func_id)) {
            Some(function) => {
                let mut callees = Vec::new();
                for node in function.blocks.iter().flat_map(|block| block.body.iter()) {
                    if let trust_ir::Inst::Call { callee, .. } = &node.inst
                        && !callees.contains(callee)
                    {
                        callees.push(*callee);
                    }
                }
                let mut verdict = CalleePurity::Pure;
                for callee in callees {
                    match rust_callee_purity(&module, &conserved, callee) {
                        CalleePurity::Pure => {}
                        impure @ CalleePurity::Impure { .. } => {
                            verdict = impure;
                            break;
                        }
                        undecided => {
                            if verdict == CalleePurity::Pure {
                                verdict = undecided;
                            }
                        }
                    }
                }
                verdict
            }
            None => CalleePurity::Undecided {
                function: plan.name.clone(),
                reason: "the recorder published no trust-ir row for it (its Rust-call identities \
                         could not be recorded), so there is no Function to read"
                    .to_string(),
            },
        };
        match verdict {
            CalleePurity::Pure => {}
            CalleePurity::Impure { function, finding } => {
                refused = Some(refuse_on_f1(
                    tcx,
                    plan.span,
                    &plan.name,
                    format!(
                        "a Clean `def` may only call a PURE Rust fn, but `{}` calls Rust code \
                         that is not provably pure: on the conserved trust-ir effect census, \
                         `{function}` {finding} (F1 decides purity on the callee's trust-ir, plan \
                         step 3.5). The faithfulness gate treats a Rust callee as a pure value the \
                         kernel checked, so it cannot model those effects, and duplicating or \
                         reordering the call would change behaviour. options: make the callee a \
                         pure function of its arguments; or compute the effectful value in Rust \
                         and pass it into the Clean `def` as an argument.",
                        plan.name
                    ),
                ));
            }
            CalleePurity::Undecided { function, reason } => {
                let mut backstop_refused = false;
                for &callee in &plan.callees {
                    let mut visited = std::collections::HashSet::new();
                    let backstop = crate::clean_origin_mir::CleanOriginBackstop {
                        origin: plan.def,
                        rust_callees: &plan_callees,
                        cycle: std::cell::Cell::new(false),
                    };
                    if crate::clean_origin_mir::rust_callee_is_pure_backstop(
                        tcx,
                        callee,
                        &mut visited,
                        &backstop,
                    ) {
                        continue;
                    }
                    let callee_path =
                        rustc_middle::ty::print::with_no_trimmed_paths!(tcx.def_path_str(callee));
                    if backstop.cycle.get() {
                        refused = Some(refuse_on_f1(
                            tcx,
                            plan.span,
                            &plan.name,
                            format!(
                                "a Clean `def` may not take part in a CROSS-LANGUAGE CYCLE, but \
                                 `{}` calls Rust `fn {callee_path}`, which leads back to `{}`. \
                                 The conserved trust-ir effect census could not decide this \
                                 callee (`{function}`: {reason}) and this crate's published \
                                 trust-ir has no edge for the cycle, so F1 found it with the MIR \
                                 walk of the Rust callees, which it uses only to refuse (plan \
                                 step 3.5). The faithfulness gate models a Rust callee as a pure \
                                 value the kernel already checked; a callee whose own body \
                                 depends on this declaration has no such value. options: give \
                                 the Rust side a base case that does not call back into the \
                                 `def`; or move the recursion wholly into Clean, where it is \
                                 checked as a well-founded definition; or compute the recursive \
                                 part in Rust and pass its result into the `def` as an argument.",
                                plan.name, plan.name
                            ),
                        ));
                        backstop_refused = true;
                        break;
                    }
                    refused = Some(refuse_on_f1(
                        tcx,
                        plan.span,
                        &plan.name,
                        format!(
                            "a Clean `def` may only call a PURE Rust fn, but `{callee_path}` is \
                             not provably pure. The conserved trust-ir effect census could not \
                             decide it (`{function}`: {reason}), so F1 consulted the MIR walk, \
                             which it uses only to refuse while the census cannot decide (plan \
                             step 3.5), and the walk found that it (or something it calls) \
                             accesses global or aliased mutable state (a `static`, an atomic, a \
                             raw pointer, interior mutability) or is otherwise unanalyzable. \
                             options: make `{callee_path}` a pure function of its arguments; or \
                             compute the effectful value in Rust and pass it into the Clean \
                             `def` as an argument."
                        ),
                    ));
                    backstop_refused = true;
                    break;
                }
                tracing::debug!(
                    def = %plan.def_path,
                    undecided = %function,
                    %reason,
                    backstop_refused,
                    "clean-origin F1: Rust-callee purity undecided on the trust-ir census; the MIR \
                     backstop was consulted to refuse only (an unrefused row stays below `gate`, \
                     never licensed)"
                );
            }
        }
    }
    if let Some(guar) = refused {
        guar.raise_fatal();
    }
}

// Trust: the general lane's refusal reasons are asserted exactly in `tests.rs`
// (Clean R80; Clean R151 consumer (3); `docs/DECISION_QUEUE.md`
// R80-CONSUMERS-1), outside this file as tidy's `unit_tests` check requires;
// `mint_kernel_tv` over real elaborated island source
// (CLEAN-TV-SOURCE-DICTIONARY-ENV-1) is its child `tests/kernel_tv.rs`.
#[cfg(test)]
mod tests;
