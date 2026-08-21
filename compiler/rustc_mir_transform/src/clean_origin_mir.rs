// Trust (I5, `docs/design/2026-08-04-two-language-compiler-architecture.md` §7):
// THE SOLE CONSTRUCTOR OF A CLEAN-ORIGIN `Body`.
//
// This whole file is Trust-owned; it has no upstream counterpart.
//
// ════════════════════════════════════════════════════════════════════════════
// WHY THIS IS THE MOST DANGEROUS FILE IN THE VERIFIER
//
// Every other direction in Trust is refutation-shaped: it can only decline to
// prove something, so a disagreement costs a failed build. This is the ONE
// direction that PRODUCES A VALUE. A disagreement here is a WRONG BINARY —
// a program that computes something other than the declaration it was written
// from, with a green build in front of it.
//
// Three consequences, all of them structural rather than advisory:
//
//   1. `clean_origin_mir` is the ONLY function that returns a Clean-origin
//      `Body`, and it cannot return one without holding a
//      `trust_clean_origin::Faithful` — a token whose only constructor is the
//      kernel-backed gate. There is no second path and no debug path.
//   2. It is called from BOTH `inner_optimized_mir` and `inner_mir_for_ctfe`,
//      at the very top of each, so compile-time evaluation is covered. A gate
//      installed only on the codegen arm would be bypassed by every `const` in
//      the program while the value still got baked into the binary.
//   3. **No verification switch disables it.** The faithfulness gate is a
//      compilation-correctness check on emitted code, not a proof obligation,
//      so it is deliberately NOT behind `verification_enabled` and NOT behind
//      `-Ztrust-verify=off`. `tests/ui/trust/clean_origin_const_ctfe.rs`
//      compiles with `-Z trust-verify=off` on purpose: a gate that vanishes
//      under a flag is a lint, not a gate.
//
// A refusal here is therefore FATAL. There is no degraded mode in which a
// disagreeing body is emitted with a warning, and no fallback to some other
// body: a Clean-origin def has no other body to fall back to, and inventing one
// is precisely the wrong-binary outcome.
//
// ════════════════════════════════════════════════════════════════════════════
// THE ROUND TRIP, AND WHY IT IS NOT CIRCULAR
//
//   Clean `def` --plan--> CleanOriginPlan --emit--> mir::Body        (side A ->)
//   mir::Body --trust_mir_extract::extract_function--> VerifiableFunction
//             --trust_types::recognize_admissible_body--> AdmissibleBody
//             --trust_spec_elab::admit_projection_function   (Projection)
//               | trust_spec_elab::admit_expr_function       (WrappingBinOp)
//                                                  --> kernel Expr  (side B)
//             --trust_clean_origin::check_faithful--> Faithful | refusal
//
// The three middle steps are the E6 **Rust -> Clean** kernel-import path. Every
// one of them was written for the opposite direction — reflecting a Rust `fn`
// into Clean so a contract can name it — years before this lane existed, and
// none of them knows anything about Clean-origin bodies. That is the entire
// reason the comparison means something: the emitter below produces the MIR,
// and a completely independent reader turns that MIR back into a kernel term.
//
// STANDING PROHIBITION, the same one that freezes `crates/trust-clean/src/
// reflect.rs`: if a Clean-origin body fails the gate, the fix is NEVER to edit
// `recognize_admissible_body`, `admit_*_function`, or the extractor. Those are
// side B's producers. Editing them to make side B agree converts the gate from
// a semantics check into a round trip, and the mutation control
// (`crates/trust-clean-origin/tests/control_3_clean_origin_emitter_mutation.rs`)
// would go green while measuring nothing.
//
// ════════════════════════════════════════════════════════════════════════════
// CRATE TOPOLOGY — a deliberate deviation from the brief, stated so it is a
// decision and not a drift.
//
// The plan said `clean_origin_mir` would live in `crates/trust-clean-origin`.
// It lives here instead, because that crate would then name `rustc_middle` and
// leave the `crates/` workspace (it would join `trust-mir-extract` in the
// `exclude` list), which takes its two existing controls — the mint
// preconditions and the frozen-R mutation — off the fast `cargo test` lane and
// onto `x.py test --stage 1`. Design doc §8's own stated reason for the fast
// lane is that "all of the kernel and carrier reasoning stays" on it, so paying
// a compiler build to run a kernel decision procedure works against the reason
// the split exists.
//
// Nothing about the seal moves. `Faithful` is still constructible only inside
// `trust-clean-origin`, and this file still cannot produce a `Body` without
// one. What lives here is only the part that genuinely needs a `TyCtxt`: the
// `mir::Body` construction and the extractor call. Every decision — the plan,
// the shape recognition, the carrier signature, the round trip, the gate —
// lives in `trust_clean_origin::emit` and is mutation-tested without a compiler.

use rustc_abi::Size;
use rustc_data_structures::thin_vec::ThinVec;
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_index::IndexVec;
use rustc_middle::mir::interpret::Scalar;
use rustc_middle::mir::{
    BasicBlock, BasicBlockData, BinOp, Body, CallSource, ClearCrossCrate, Local, LocalDecl,
    MirPhase, MirSource, Operand, Place, Rvalue, RuntimePhase, SourceInfo, SourceScopeData,
    Statement, StatementKind, SwitchTargets, Terminator, TerminatorKind, UnwindAction, WithRetag,
};
use rustc_middle::ty::fast_reject::SimplifiedType;
use rustc_middle::ty::{GenericArg, Ty, TyCtxt, UintTy};
use rustc_span::{Span, Spanned, sym};
use trust_clean_origin::{CleanOriginPlan, CleanOriginShape, EmitRefusal};
use trust_types::admissible_body::{ArithBinOp, ArithExpr, ArithOperand, SelectCmp};

/// Everything needed to originate a body for one Clean declaration.
///
/// Produced by the mint site, which is where the three I5 preconditions
/// (`KernelChecked`, audited-empty axiom closure, total carrier) are decided.
/// It carries the crate's Clean [`Environment`](clean_kernel::Environment)
/// because the gate must read side A out of the environment the KERNEL
/// registered, never out of anything this file reconstructs.
pub(crate) struct CleanOriginDecl<'a> {
    /// The Clean declaration name, as the kernel knows it.
    pub(crate) name: &'a str,
    /// The crate-local Clean environment holding the declaration.
    pub(crate) env: &'a clean_kernel::Environment,
    /// The span of the declaration inside its `clean { … }` island, for
    /// diagnostics that must land where the user can see them.
    pub(crate) span: Span,
}

/// Every def in this crate that originated from a Clean island declaration.
///
/// # IT IS AN ENUMERATION, NOT A FILTER, AND THAT IS NOT A STYLE CHOICE
///
/// `mir_keys` needs to *find* these defs. Every `tcx`-side inventory available
/// there — `hir_body_owners`, `hir_crate_items(()).definitions()`,
/// `hir_crate_items(()).free_items()` — is derived from HIR, and a Clean-origin
/// def is exactly the thing that has none. A predicate applied to any of them
/// would be vacuously false forever while *looking* like a working filter. So
/// the registry is the source and the predicate is derived from it, never the
/// other way round.
///
/// The registry is written by the ONE site that can mint a Clean-origin
/// `DefId` — `rustc_resolve`'s `trust_mint_clean_island_decls`, which cannot
/// mint without a `KernelChecked` status, an audited-empty axiom closure and a
/// total carrier — and carried here through `ResolverGlobalCtxt`. It is empty
/// in every crate with no `clean { … }` island.
pub(crate) fn clean_origin_defs(tcx: TyCtxt<'_>) -> impl Iterator<Item = LocalDefId> {
    tcx.resolutions(()).clean_origin_defs.iter().map(|&(def, _, _)| def)
}

/// Whether `def` originated from a Clean island declaration.
///
/// Derived from [`clean_origin_defs`], never from an independent test — see
/// that function's second heading for why the direction matters.
pub(crate) fn is_clean_origin(tcx: TyCtxt<'_>, def: LocalDefId) -> bool {
    clean_origin_registry_entry(tcx, def).is_some()
}

/// The registry row for `def`: the Clean declaration name and the span inside
/// the island. `None` for every ordinary Rust item.
///
/// Trust: (I7) — `pub(crate)` for the export provider (`clean_origin_export`),
/// which must look up the SAME registry row the sole constructor uses.
pub(crate) fn clean_origin_registry_entry(
    tcx: TyCtxt<'_>,
    def: LocalDefId,
) -> Option<(String, Span)> {
    tcx.resolutions(())
        .clean_origin_defs
        .iter()
        .find(|&&(candidate, _, _)| candidate == def)
        .map(|&(_, name, span)| (name.to_string(), span))
}

/// The crate's Clean environment, re-checked at MIR time.
///
/// # Why this is checked AGAIN rather than carried from the mint
///
/// The mint decision runs in `rustc_resolve`, and its verdict is what makes the
/// NAME exist. Carrying the `Environment` itself forward would put
/// `clean-kernel` in `rustc_middle` (`ResolverGlobalCtxt` is where a resolver
/// output has to live) for the benefit of one lane.
///
/// More to the point, a second run is the honest thing here rather than a
/// weaker one. The gate's whole claim is about the environment the KERNEL
/// registered, and this IS that pipeline — `CleanIslandSession::check_all` is
/// the same authoritative whole-crate, header-first check `trust_verify.rs`
/// runs, over the same island bytes (the parser captured them onto the HIR node
/// under ruling v7/D1, so the elaborator sees the same bytes by construction).
/// If the two runs ever disagreed, the mint would have created a name whose
/// declaration this run cannot plan or admit, and the result is a FATAL refusal
/// below — never an emitted body. Fail-closed in the direction that matters.
///
/// `None` means the session was tainted or an island's bytes could not be
/// recovered. For a def that is in the registry, that is a hard failure, not a
/// "carry on": see [`clean_origin_mir`].
///
/// COST, stated: this elaborates the crate's islands once per Clean-origin
/// body. There is deliberately no cache — a cache keyed on nothing is a
/// crate-global mutable, and the population is one entry per callable Clean
/// declaration.
/// Trust: (I7) — the crate's `clean { … }` island sources in authored order, or
/// `None` when an island's bytes could not be recovered. Factored out of
/// [`clean_crate_environment`] and shared with the `trust_clean_island_sources`
/// query so the transported sources and the environment the gate ran over
/// cannot disagree.
pub(crate) fn collect_island_sources(tcx: TyCtxt<'_>) -> Option<Vec<String>> {
    let mut islands: Vec<(rustc_span::Span, String)> = Vec::new();
    for item_id in tcx.hir_crate_items(()).free_items() {
        let item = tcx.hir_item(item_id);
        let rustc_hir::ItemKind::CleanIsland { content_span, text, .. } = item.kind else {
            continue;
        };
        let text = if text.is_empty() {
            tcx.sess.source_map().span_to_snippet(content_span).ok()?
        } else {
            text.to_string()
        };
        islands.push((content_span, text));
    }
    // Authored source order: Clean file state (namespaces, `open`s, notation,
    // options) evolves across islands, and this is the same sort
    // `trust_check_clean_islands` and the resolve-time decision both apply.
    islands.sort_by_key(|(span, _)| (span.lo(), span.hi()));
    Some(islands.into_iter().map(|(_, text)| text).collect())
}

pub(crate) fn clean_crate_environment(
    tcx: TyCtxt<'_>,
) -> Option<trust_certify::clean_island::CleanIslandSession> {
    let sources = collect_island_sources(tcx)?;
    let sources: Vec<&str> = sources.iter().map(String::as_str).collect();
    let mut session = trust_certify::clean_island::CleanIslandSession::new();
    let batch = session.check_all(&sources);
    if batch.is_rejected() || session.is_tainted() {
        return None;
    }
    Some(session)
}

/// **The sole constructor of a Clean-origin `Body`.**
///
/// `None` means "this def did not come from a Clean island" — the ordinary
/// answer for every Rust item, and the signal to the provider arms to carry on
/// with the normal pipeline. It NEVER means "the gate declined": a gate refusal
/// is fatal and does not return.
///
/// Called at the very TOP of `inner_optimized_mir` and `inner_mir_for_ctfe`,
/// before `is_constructor` and before `hir_body_const_context` — the latter
/// matters because a Clean-origin def has no HIR and
/// `hir_body_const_context`'s `None` arm in the CTFE provider is a hard
/// `bug!`.
pub(crate) fn clean_origin_mir<'tcx>(tcx: TyCtxt<'tcx>, def: LocalDefId) -> Option<Body<'tcx>> {
    let (name, span) = clean_origin_registry_entry(tcx, def)?;

    // From here on there is no `None`. The def IS Clean-origin, so either a
    // gated body comes back or the compilation stops: there is no other body
    // to fall back to, and inventing one is the wrong-binary outcome.
    let Some(session) = clean_crate_environment(tcx) else {
        tcx.dcx().span_fatal(
            span,
            format!(
                "internal: refusing to emit code for Clean declaration `{name}` — a `DefId` \
                 was minted for it, which requires the CIC kernel to have re-checked it, but \
                 re-checking this crate's Clean islands at code-generation time did not \
                 produce a usable environment. The compiler will not emit a body it cannot \
                 put back to the kernel. Please report it."
            ),
        );
    };
    let env = session.environment().expect("an untainted session has an environment");
    let decl = CleanOriginDecl { name: &name, env, span };
    Some(build_gated_body(tcx, def, &decl))
}

/// Plan, emit, and GATE. Returns only a body the kernel identified with the
/// Clean declaration; every other outcome is a fatal diagnostic.
///
/// Split out from [`clean_origin_mir`] so it is a total function of an explicit
/// `CleanOriginDecl` rather than of the registry lookup — the emission and the
/// gate can then be reasoned about (and, once the mint lands, driven from a
/// test) without depending on how a def came to be Clean-origin.
fn build_gated_body<'tcx>(
    tcx: TyCtxt<'tcx>,
    def: LocalDefId,
    decl: &CleanOriginDecl<'_>,
) -> Body<'tcx> {
    // ── side A: what the kernel says this declaration IS ───────────────────
    //
    // Read from the Clean environment, never from anything downstream of the
    // emitter. `plan_clean_origin_body` re-checks the declaration's provenance
    // (`FullKernelCheck`) and its total carrier signature, so the emitted
    // SIGNATURE rests on a kernel verdict, not only the emitted body.
    let plan = match trust_clean_origin::plan_clean_origin_body(decl.env, decl.name) {
        Ok(plan) => plan,
        Err(refusal) => refuse(tcx, decl, &refusal),
    };

    // ── the signature cross-check ──────────────────────────────────────────
    //
    // `fn_sig` was FED at the mint site, in `rustc_resolve`, from the same I4
    // carrier decision this plan carries — but through a second, independent
    // spelling of the carrier -> rustc-type mapping (`trust_clean_mint::rustc_ty`
    // there, `carrier_to_rustc_ty` here), because the two live in crates that
    // cannot share one.
    //
    // A divergence between those two spellings is a WRONG BINARY of exactly the
    // kind the kernel gate cannot see: typeck would have checked every call
    // against one signature while the emitted body computes at the other, and
    // side B's reflection would agree with the body it was given. So the
    // agreement is CHECKED here, not reviewed, and a disagreement is fatal.
    check_signature_agrees(tcx, def, &plan, decl);

    // ── the emission ───────────────────────────────────────────────────────
//
    // One arm per `CleanOriginShape` variant, exhaustively — the enum is
    // deliberately NOT `#[non_exhaustive]` so a new shape is a compile error
    // here, never a fall-through into the wrong emitter.
    let mut body = match plan.shape() {
        CleanOriginShape::Projection { projected } => {
            build_projection_body(tcx, def, &plan, *projected, decl.span)
        }
        CleanOriginShape::WrappingBinOp { op, left, right } => {
            build_wrapping_binop_body(tcx, def, &plan, *op, *left, *right, decl.span)
        }
        CleanOriginShape::Composed { expr } => {
            build_composed_body(tcx, def, &plan, expr, decl.span)
        }
        // Trust (R2/C5a): the parameter select.
        CleanOriginShape::Select { cmp, cmp_left, cmp_right, then_param, else_param } => {
            build_select_body(
                tcx, def, &plan, *cmp, *cmp_left, *cmp_right, *then_param, *else_param,
                decl.span,
            )
        }
    };

    // Trust (#65, C3): the TEST-ONLY divergence knob. Perturbs SIDE A's output —
    // the emitted body, after the plan, before side B reads it — so the gate's
    // fatal refusal is exercisable end-to-end from a ui fixture
    // (`clean_origin_divergence_fails_build.rs`). The standing prohibition holds:
    // the recognizer, the admitters and the extractor (side B) are untouched, so
    // the gate still compares two independent readings; this knob only makes the
    // emission WRONG, exactly like a real emitter bug would. It can only make a
    // build FAIL that would have passed, never the reverse — the mutated body
    // either trips the gate (fatal) or, if this knob ever rotted into a no-op,
    // the fixture's expected error goes unmatched and the FIXTURE fails.
    if tcx.sess.opts.unstable_opts.trust_clean_origin_mutate_emitter {
        mutate_emitted_body_for_gate_test(&mut body);
    }

    // ── side B + the gate ──────────────────────────────────────────────────
    //
    // The EMITTED body is read back out of MIR by the extractor — the same
    // entry point the verifier uses for ordinary Rust functions — and reflected
    // into Clean by the E6 producers. Nothing here shortcuts to the plan: the
    // plan is derived from side A, so comparing against it would check that the
    // compiler read the Clean term correctly and say nothing about what it
    // emitted.
    // MEASURED PRECONDITION THE PLAN DID NOT NAME (2026-08-19): the extractor
    // reaches HIR for a LOCAL def, twice and unconditionally —
    // `extract_contracts` and `extract_trust_annotations` both call
    // `tcx.local_def_id_to_hir_id(..)` and then `tcx.hir_attrs(..)`. So a
    // Clean-origin def cannot have *no* HIR at all; the mint site must call
    // `TyCtxtFeed::feed_hir()`, which feeds exactly those two —
    // `hir_owner` (making `local_def_id_to_hir_id` return `HirId::make_owner`)
    // and `hir_attr_map` (`AttributeMap::EMPTY`). The third reach,
    // `first_synthetic_contract_parameter`, goes through
    // `hir_maybe_body_owned_by`, which is `Option`-returning and takes the
    // `None` path.
    //
    // This is NOT worked around by writing a narrower extractor. Doing that
    // would make side B's producer a thing this lane authored, and the gate
    // would stop comparing two independent readings of the body. The extractor
    // stays the one the verifier uses for ordinary Rust functions; the mint
    // site pays the `feed_hir()` cost.
    //
    // UNVERIFIED, and flagged as such: it cannot be exercised until a def is
    // minted, so this is a reading of the call chain, not a measurement of a
    // run.
    let extracted = trust_mir_extract::extract_function(tcx, &body);
    match trust_clean_origin::admit_lowering(decl.env, &plan, &extracted) {
        // The `Faithful` token is the permission. It is deliberately dropped
        // here rather than stored: its whole job is to make this line
        // unreachable without the gate having run.
        Ok(_faithful) => body,
        Err(refusal) => refuse(tcx, decl, &refusal),
    }
}

/// Require `tcx.fn_sig(def)` — fed at the mint site — to be exactly the
/// signature this plan's carriers denote. Fatal on any disagreement.
///
/// This is the guard on the one duplication I5 could not avoid: the carrier ->
/// rustc-type mapping exists once in `rustc_resolve` (where the signature is
/// fed) and once in this file (where the body's locals are built), because
/// those two crates cannot share a function that needs a `TyCtxt`. Arity,
/// argument types and result type are all compared; a mismatch means the
/// signature every call site was checked against is not the signature the
/// emitted body has.
fn check_signature_agrees<'tcx>(
    tcx: TyCtxt<'tcx>,
    def: LocalDefId,
    plan: &CleanOriginPlan,
    decl: &CleanOriginDecl<'_>,
) {
    let fed = tcx.fn_sig(def.to_def_id()).instantiate_identity().skip_binder();
    let expected_inputs: Vec<Ty<'tcx>> = plan
        .param_tys()
        .iter()
        .map(|ty| carrier_to_rustc_ty(tcx, ty, decl.span))
        .collect();
    let expected_output = carrier_to_rustc_ty(tcx, plan.return_ty(), decl.span);

    if fed.inputs() != expected_inputs.as_slice() || fed.output() != expected_output {
        tcx.dcx().span_fatal(
            decl.span,
            format!(
                "internal: refusing to emit code for Clean declaration `{}` — the Rust \
                 signature this declaration was given at name-resolution time \
                 (`fn({:?}) -> {:?}`) is not the one its discharged carriers denote here \
                 (`fn({:?}) -> {:?}`). Every call was type-checked against the first and the \
                 body would compute at the second, which no kernel check can catch. This is \
                 a compiler defect and nothing you write will change it. Please report it.",
                decl.name,
                fed.inputs(),
                fed.output(),
                expected_inputs,
                expected_output,
            ),
        );
    }
}

/// Report a refusal and stop. Never returns.
///
/// FATAL, not an error-and-continue: continuing would mean some later phase
/// demanding this body again and either re-running the gate (and re-reporting)
/// or, worse, finding a cached one. A Clean-origin body that failed the gate
/// must not exist in this compilation at all.
///
/// Ruling v7/D3 governs the wording: a capability refusal names the fragment
/// boundary and the ways around it, and a correctness refusal says plainly that
/// the compiler mistranslated its own declaration and that nothing the user
/// writes will change it. Telling a user to add an annotation because the
/// compiler emitted the wrong body would send them to fix something they did
/// not break.
fn refuse(tcx: TyCtxt<'_>, decl: &CleanOriginDecl<'_>, refusal: &EmitRefusal) -> ! {
    let headline = if refusal.is_compiler_defect() {
        format!(
            "internal: refusing to emit code for Clean declaration `{}` — the emitted body \
             does not agree with the declaration",
            decl.name
        )
    } else {
        format!("Clean declaration `{}` cannot be called from Rust", decl.name)
    };
    tcx.dcx().struct_span_fatal(decl.span, headline).with_note(refusal.note()).emit()
}

/// Trust (#65, C3; extended R2/C5a): the test-only mutation behind
/// `-Ztrust-clean-origin-mutate-emitter` — make the emission WRONG, per shape:
///
/// * projection (arity >= 2): swap the moved argument in the return
///   assignment to a DIFFERENT argument, so the emission denotes the wrong
///   projection. On an arity-1 body there is no other argument to swap to;
///   the fixture pins an arity-2 declaration.
/// * select (R2/C5a): swap the `SwitchInt` targets — the exact
///   polarity-inversion bug `SwitchTargets::static_if`'s argument order
///   invites, which silently emits max where the island wrote min. The gate,
///   not this comment, is what makes that bug impossible to ship.
fn mutate_emitted_body_for_gate_test(body: &mut Body<'_>) {
    let arg_count = body.arg_count;
    for block in body.basic_blocks_mut() {
        if let Some(terminator) = &mut block.terminator
            && let TerminatorKind::SwitchInt { targets, .. } = &mut terminator.kind
            && targets.all_targets().len() == 2
        {
            let zero_target = targets.target_for_value(0);
            let otherwise = targets.otherwise();
            *targets = SwitchTargets::static_if(0, otherwise, zero_target);
        }
        if arg_count < 2 {
            continue;
        }
        for stmt in &mut block.statements {
            if let StatementKind::Assign(assign) = &mut stmt.kind
                && let (place, Rvalue::Use(Operand::Move(src), _)) = &mut **assign
                && place.local == Local::from_usize(0)
                && src.projection.is_empty()
            {
                let cur = src.local.as_usize();
                let swapped = if cur == 1 { 2 } else { 1 };
                *src = Place::from(Local::from_usize(swapped));
            }
        }
    }
}

/// Emit the d01 Projection shape: one block, `_0 = move _{i+1}`, `return`.
///
/// It is the shape `tests/e6-fragment-probe/probes/d01_projection_u64.rs`
/// measures — no external `DefId`, no call terminator, no lang item, no
/// promoted — chosen because it is what the kernel demonstrably admits under
/// definitional equality against its reflected lowering. See
/// `trust_clean_origin::emit` for the fragment statement.
///
/// `projected` is passed explicitly rather than re-destructured from the plan
/// so that calling this from any arm but `Projection`'s is structurally
/// impossible to do by accident.
///
/// The types come from the plan's `CarrierSignature`, which cannot exist unless
/// EVERY position — arguments and result — has a discharged total carrier. So
/// the local types here are I4's decision, not a convenience mapping.
fn build_projection_body<'tcx>(
    tcx: TyCtxt<'tcx>,
    def: LocalDefId,
    plan: &CleanOriginPlan,
    projected: usize,
    span: Span,
) -> Body<'tcx> {
    let return_ty = carrier_to_rustc_ty(tcx, plan.return_ty(), span);
    let param_tys: Vec<_> =
        plan.param_tys().iter().map(|ty| carrier_to_rustc_ty(tcx, ty, span)).collect();
    let arg_count = param_tys.len();

    // `_0` is the return place; `_1 ..= _n` are the parameters, immutable
    // exactly as `local_decls_for_sig` makes them for a shim.
    let local_decls: IndexVec<Local, LocalDecl<'tcx>> =
        std::iter::once(LocalDecl::new(return_ty, span))
            .chain(param_tys.into_iter().map(|ty| LocalDecl::new(ty, span).immutable()))
            .collect();

    let source_info = SourceInfo::outermost(span);

    // `_0 = move _{projected+1}`.
    //
    // The `+1` is the return place occupying local 0. `projected` is the
    // 0-based SOURCE parameter, already inverted out of its de Bruijn index by
    // `plan_clean_origin_body` — and an inversion mistake here is exactly the
    // one-construct mistranslation `control_3`'s `half_2` injects and requires
    // the gate to catch.
    let statement = Statement::new(
        source_info,
        StatementKind::Assign(Box::new((
            Place::return_place(),
            // `WithRetag::Yes` is what `rustc_mir_build` emits for every
            // ordinary `Rvalue::Use`, so the body is spelled the way a
            // hand-written `fn fst(x, y) -> u64 { x }` is spelled. This is not
            // cosmetic: side B is produced by reading this MIR back, and the
            // fewer respects in which a Clean-origin body differs from an
            // ordinary one, the fewer places a reader can behave differently on
            // it than on the bodies it was written for.
            Rvalue::Use(Operand::Move(Place::from(Local::arg(projected))), WithRetag::Yes),
        ))),
    );

    let start_block = BasicBlockData::new_stmts(
        vec![statement],
        Some(Terminator {
            source_info,
            kind: TerminatorKind::Return,
            attributes: ThinVec::new(),
        }),
        false,
    );

    let mut body = Body::new(
        MirSource::item(def.to_def_id()),
        IndexVec::from_elem_n(start_block, 1),
        IndexVec::from_elem_n(
            SourceScopeData {
                span,
                parent_scope: None,
                inlined: None,
                inlined_parent_scope: None,
                local_data: ClearCrossCrate::Clear,
            },
            1,
        ),
        local_decls,
        IndexVec::new(),
        arg_count,
        vec![],
        span,
        None,
        None,
    );
    // A projection mentions no other item and reads no constant. Both tables
    // are filled explicitly because the optimization passes that would
    // otherwise populate them do not run on this body: running them would let
    // a pass rewrite the very thing the gate is about to check.
    body.set_mentioned_items(Vec::new());
    body.set_required_consts(Vec::new());
    // MEASURED (2026-08-19): `Body::new` starts at `MirPhase::Built`, and
    // `TyCtxt::instance_mir` asserts the phase is `Runtime(_)` — the assertion
    // fires the moment a Clean-origin function is actually CALLED at runtime
    // (the const fixture missed it because a `const` goes through
    // `mir_for_ctfe` and is never a mono item).
    //
    // `Optimized` is the honest phase, not a label chosen to satisfy the
    // assertion: this body is emitted in its final form and no pass will ever
    // run on it — `optimized_mir` returns it directly, deliberately skipping
    // `run_optimization_passes`, because a pass that rewrote it after the gate
    // ran would put un-gated code in the binary. There is no earlier phase this
    // body is ever in.
    body.phase = MirPhase::Runtime(RuntimePhase::Optimized);
    body
}

/// The `DefId` of core's inherent `u{width}::wrapping_{op}`, resolved from
/// `TyCtxt` facts and REQUIRED UNIQUE. Fatal on zero or multiple candidates.
///
/// Resolution route: `incoherent_impls(Uint(w))` — how rustc itself finds
/// primitive inherent methods — then per-impl name lookup, filtered through
/// `trust_mir_extract::tcx_is_authenticated_core_integer_wrapping_method`
/// (the `Sized`-lang-item-crate identity + inherent-primitive-impl + exact-sig
/// authentication the EXTRACTOR also applies at read-back) and an exact
/// self-type match. Multiple survivors are possible in principle because
/// `#[rustc_allow_incoherent_impl]` lets another crate add a lookalike
/// inherent impl that `incoherent_impls` will return.
///
/// Why a resolution mistake still cannot emit a wrong binary: the emitter
/// never writes the recognizer's marker string. `extract_function` re-derives
/// it at read-back from the same `TyCtxt` facts, independently of this
/// resolution; a wrong `DefId` here fails that authentication, the recognizer
/// refuses the unmarked callee, `admit_lowering` returns
/// `LoweringUnrecognised`, and `refuse` is fatal. This function's uniqueness
/// check only upgrades that failure's diagnostics from an internal refusal to
/// a named resolution error.
fn resolve_core_wrapping_method<'tcx>(
    tcx: TyCtxt<'tcx>,
    op: ArithBinOp,
    width_bits: u32,
    span: Span,
) -> DefId {
    let (uint, self_ty) = match width_bits {
        8 => (UintTy::U8, tcx.types.u8),
        16 => (UintTy::U16, tcx.types.u16),
        32 => (UintTy::U32, tcx.types.u32),
        64 => (UintTy::U64, tcx.types.u64),
        other => tcx.dcx().span_fatal(
            span,
            format!(
                "internal: a WrappingBinOp plan reached the emitter at width {other}, \
                 which `plan_clean_origin_body` is required to refuse. This is a \
                 compiler defect. Please report it."
            ),
        ),
    };
    let method = match op {
        ArithBinOp::Add => sym::wrapping_add,
        ArithBinOp::Sub => sym::wrapping_sub,
        ArithBinOp::Mul => sym::wrapping_mul,
    };

    let candidates: Vec<DefId> = tcx
        .incoherent_impls(SimplifiedType::Uint(uint))
        .iter()
        .filter(|&&impl_did| tcx.type_of(impl_did).instantiate_identity().skip_norm_wip() == self_ty)
        .flat_map(|&impl_did| {
            tcx.associated_items(impl_did)
                .filter_by_name_unhygienic(method)
                .map(|item| item.def_id)
        })
        .filter(|&did| trust_mir_extract::tcx_is_authenticated_core_integer_wrapping_method(tcx, did))
        .collect();

    match candidates[..] {
        [callee] => callee,
        ref found => tcx.dcx().span_fatal(
            span,
            format!(
                "internal: resolution of the core primitive `u{width_bits}::{method}` was \
                 {} ({} authenticated candidate(s): {found:?}); the compiler will not \
                 guess which function to emit a call to. This is a compiler defect — \
                 please report it. Meanwhile: restate the `def` as a parameter \
                 projection, or cite it from proof position, which needs no emitted \
                 body.",
                if found.is_empty() { "absent" } else { "ambiguous" },
                found.len(),
            ),
        ),
    }
}

/// Emit the WrappingBinOp shape:
/// `bb0: _0 = Call(u{w}::wrapping_{op}, [l, r]) -> bb1; bb1: Return` — the
/// exact two-block form `recognize_arithmetic` was written for, and the form
/// the fast-lane probes hand-build (`fragment_widening_probes::emitted_binop`).
///
/// Locals exactly as the projection emitter: `_0` at the result carrier,
/// `_1..=_n` immutable at the argument carriers, all through the one
/// `carrier_to_rustc_ty` mapping — deliberately no second mapping, so
/// `check_signature_agrees` still guards the only carrier→rustc duplication.
fn build_wrapping_binop_body<'tcx>(
    tcx: TyCtxt<'tcx>,
    def: LocalDefId,
    plan: &CleanOriginPlan,
    op: ArithBinOp,
    left: ArithOperand,
    right: ArithOperand,
    span: Span,
) -> Body<'tcx> {
    let return_ty = carrier_to_rustc_ty(tcx, plan.return_ty(), span);
    let param_tys: Vec<_> =
        plan.param_tys().iter().map(|ty| carrier_to_rustc_ty(tcx, ty, span)).collect();
    let arg_count = param_tys.len();

    // The width comes from the plan's RESULT carrier; plan-time checks
    // guarantee every argument position shares it.
    let trust_types::Ty::Int { width: width_bits, signed: false } = *plan.return_ty() else {
        tcx.dcx().span_fatal(
            span,
            format!(
                "internal: a WrappingBinOp plan carries result carrier `{:?}`, which \
                 `plan_clean_origin_body` is required to refuse. This is a compiler \
                 defect. Please report it.",
                plan.return_ty()
            ),
        );
    };
    let callee = resolve_core_wrapping_method(tcx, op, width_bits, span);

    // `Copy`, not `Move`: `a + a` names one local twice. A numeral is an
    // inline `Const::Val` scalar — nothing needs evaluation, so
    // `required_consts` below stays honestly empty, and nothing can promote.
    let operand = |o: ArithOperand| -> Operand<'tcx> {
        match o {
            ArithOperand::Param(i) => Operand::Copy(Place::from(Local::arg(i))),
            ArithOperand::Const(value) => Operand::const_from_scalar(
                tcx,
                return_ty,
                Scalar::from_uint(value, Size::from_bits(u64::from(width_bits))),
                span,
            ),
        }
    };

    let local_decls: IndexVec<Local, LocalDecl<'tcx>> =
        std::iter::once(LocalDecl::new(return_ty, span))
            .chain(param_tys.into_iter().map(|ty| LocalDecl::new(ty, span).immutable()))
            .collect();

    let source_info = SourceInfo::outermost(span);

    let call_block = BasicBlockData::new_stmts(
        Vec::new(),
        Some(Terminator {
            source_info,
            kind: TerminatorKind::Call {
                // No generics on an inherent uint method.
                func: Operand::function_handle(
                    tcx,
                    callee,
                    std::iter::empty::<GenericArg<'tcx>>(),
                    span,
                ),
                args: Box::new([
                    Spanned { node: operand(left), span },
                    Spanned { node: operand(right), span },
                ]),
                destination: Place::return_place(),
                target: Some(BasicBlock::from_u32(1)),
                // The primitive cannot unwind; this extracts to the
                // `UnwindEdge::Unreachable` the probes' recognized shape
                // carries.
                unwind: UnwindAction::Unreachable,
                call_source: CallSource::Misc,
                fn_span: span,
            },
            attributes: ThinVec::new(),
        }),
        false,
    );
    let return_block = BasicBlockData::new_stmts(
        Vec::new(),
        Some(Terminator {
            source_info,
            kind: TerminatorKind::Return,
            attributes: ThinVec::new(),
        }),
        false,
    );

    let mut body = Body::new(
        MirSource::item(def.to_def_id()),
        IndexVec::from_raw(vec![call_block, return_block]),
        IndexVec::from_elem_n(
            SourceScopeData {
                span,
                parent_scope: None,
                inlined: None,
                inlined_parent_scope: None,
                local_data: ClearCrossCrate::Clear,
            },
            1,
        ),
        local_decls,
        IndexVec::new(),
        arg_count,
        vec![],
        span,
        None,
        None,
    );
    // `mentioned_items` stays empty SOUNDLY: the mono collector collects the
    // callee as a **used** item by walking this very body (used and mentioned
    // are collected independently; there is no used ⊆ mentioned assertion),
    // and no optimization ever runs on this body to delete the call —
    // `optimized_mir` returns it directly. `required_consts` is honestly
    // empty: the only constant is an inline evaluated scalar.
    body.set_mentioned_items(Vec::new());
    body.set_required_consts(Vec::new());
    // Same phase argument as the projection emitter: this body is emitted in
    // its final form, no pass ever runs on it, and `instance_mir` asserts
    // `Runtime(_)` the moment the function is called at runtime.
    body.phase = MirPhase::Runtime(RuntimePhase::Optimized);
    body
}

/// Emit the Composed shape: the linear wrapping-call chain
/// `recognize_call_chain` was written for — one `Call` per tree node in
/// POST-ORDER (left subtree, right subtree, then the node), each non-root
/// node writing a fresh temporary, the root writing `_0`, then `Return`.
/// For `fun a b => (a + b) * a`:
///
/// ```text
/// bb0: _3 = Call(u64::wrapping_add, [copy _1, copy _2]) -> bb1
/// bb1: _0 = Call(u64::wrapping_mul, [copy _3, copy _1]) -> bb2
/// bb2: Return
/// ```
///
/// This is EXACTLY the shape the recognizer's chain arm accepts — strictly
/// consecutive call blocks, each targeting the next, each destination a bare
/// fresh temporary except the last, which is the bare return place — and the
/// shape the fast-lane probes hand-build (`fragment_widening_probes::
/// emitted_nested`, and the e6 corpus's f21, which discharges it end-to-end).
/// Post-order also makes the read-back exact: each temporary is written once
/// and consumed once, so the recognizer's substitution through its
/// environment reconstructs precisely the tree that was flattened here, and
/// the structural comparison in `admit_lowering` is then direct equality.
///
/// Locals exactly as the other emitters: `_0` at the result carrier,
/// `_1..=_n` immutable at the argument carriers, then one temporary per
/// NON-ROOT node at the result carrier (the plan's checks guarantee every
/// position shares the one width) — all through the one `carrier_to_rustc_ty`
/// mapping, so `check_signature_agrees` still guards the only carrier→rustc
/// duplication. Every callee is resolved per node through
/// `resolve_core_wrapping_method`; operands are `Copy` (a parameter or a
/// temporary may be named more than once in principle, and the probes'
/// recognized shape carries `Copy`) or inline `Const::Val` scalars at the
/// carrier width, so `required_consts` stays honestly empty.
fn build_composed_body<'tcx>(
    tcx: TyCtxt<'tcx>,
    def: LocalDefId,
    plan: &CleanOriginPlan,
    expr: &ArithExpr,
    span: Span,
) -> Body<'tcx> {
    let return_ty = carrier_to_rustc_ty(tcx, plan.return_ty(), span);
    let param_tys: Vec<_> =
        plan.param_tys().iter().map(|ty| carrier_to_rustc_ty(tcx, ty, span)).collect();
    let arg_count = param_tys.len();

    // The width comes from the plan's RESULT carrier; plan-time checks
    // guarantee every argument position shares it.
    let trust_types::Ty::Int { width: width_bits, signed: false } = *plan.return_ty() else {
        tcx.dcx().span_fatal(
            span,
            format!(
                "internal: a Composed plan carries result carrier `{:?}`, which \
                 `plan_clean_origin_body` is required to refuse. This is a compiler \
                 defect. Please report it.",
                plan.return_ty()
            ),
        );
    };

    // ── flatten the tree, post-order ───────────────────────────────────────
    //
    // One step per binop node; a step's operand is a source parameter, an
    // in-range literal, or the RESULT OF AN EARLIER STEP — the `Step` index —
    // which is what makes a dangling intermediate unrepresentable here too.
    enum StepOperand {
        Param(usize),
        Const(u128),
        Step(usize),
    }
    struct Step {
        op: ArithBinOp,
        left: StepOperand,
        right: StepOperand,
    }
    fn flatten(expr: &ArithExpr, steps: &mut Vec<Step>) -> StepOperand {
        match expr {
            ArithExpr::Operand(ArithOperand::Param(i)) => StepOperand::Param(*i),
            ArithExpr::Operand(ArithOperand::Const(v)) => StepOperand::Const(*v),
            ArithExpr::Bin { op, left, right } => {
                let left = flatten(left, steps);
                let right = flatten(right, steps);
                steps.push(Step { op: *op, left, right });
                StepOperand::Step(steps.len() - 1)
            }
        }
    }
    let mut steps = Vec::new();
    let root = flatten(expr, &mut steps);
    let n_steps = steps.len();
    // The plan is required to carry 2..=COMPOSED_MAX_OPS nodes; a degenerate
    // tree reaching the emitter is a defect, and emitting a fallback body for
    // it is the wrong-binary outcome. (The root being the LAST step is
    // post-order by construction; it is asserted anyway because `_0`'s writer
    // depends on it.)
    if n_steps < 2 || !matches!(root, StepOperand::Step(index) if index == n_steps - 1) {
        tcx.dcx().span_fatal(
            span,
            format!(
                "internal: a Composed plan flattened to {n_steps} call step(s), which \
                 `plan_clean_origin_body` is required to refuse. This is a compiler \
                 defect. Please report it."
            ),
        );
    }

    // Temporary for NON-ROOT step `k`: local `arg_count + 1 + k`. The root
    // (step `n_steps - 1`) writes the return place and gets no temporary.
    let temp_local = |step: usize| Local::from_usize(arg_count + 1 + step);

    let local_decls: IndexVec<Local, LocalDecl<'tcx>> =
        std::iter::once(LocalDecl::new(return_ty, span))
            .chain(param_tys.into_iter().map(|ty| LocalDecl::new(ty, span).immutable()))
            .chain((0..n_steps - 1).map(|_| LocalDecl::new(return_ty, span)))
            .collect();

    let source_info = SourceInfo::outermost(span);

    let operand = |o: &StepOperand| -> Operand<'tcx> {
        match o {
            StepOperand::Param(i) => Operand::Copy(Place::from(Local::arg(*i))),
            StepOperand::Const(value) => Operand::const_from_scalar(
                tcx,
                return_ty,
                Scalar::from_uint(*value, Size::from_bits(u64::from(width_bits))),
                span,
            ),
            StepOperand::Step(k) => Operand::Copy(Place::from(temp_local(*k))),
        }
    };

    let mut blocks: Vec<BasicBlockData<'tcx>> = Vec::with_capacity(n_steps + 1);
    for (k, step) in steps.iter().enumerate() {
        let is_root = k == n_steps - 1;
        let callee = resolve_core_wrapping_method(tcx, step.op, width_bits, span);
        blocks.push(BasicBlockData::new_stmts(
            Vec::new(),
            Some(Terminator {
                source_info,
                kind: TerminatorKind::Call {
                    // No generics on an inherent uint method.
                    func: Operand::function_handle(
                        tcx,
                        callee,
                        std::iter::empty::<GenericArg<'tcx>>(),
                        span,
                    ),
                    args: Box::new([
                        Spanned { node: operand(&step.left), span },
                        Spanned { node: operand(&step.right), span },
                    ]),
                    destination: if is_root {
                        Place::return_place()
                    } else {
                        Place::from(temp_local(k))
                    },
                    target: Some(BasicBlock::from_usize(k + 1)),
                    // The primitive cannot unwind; this extracts to the
                    // `UnwindEdge::Unreachable` the probes' recognized shape
                    // carries.
                    unwind: UnwindAction::Unreachable,
                    call_source: CallSource::Misc,
                    fn_span: span,
                },
                attributes: ThinVec::new(),
            }),
            false,
        ));
    }
    blocks.push(BasicBlockData::new_stmts(
        Vec::new(),
        Some(Terminator {
            source_info,
            kind: TerminatorKind::Return,
            attributes: ThinVec::new(),
        }),
        false,
    ));

    let mut body = Body::new(
        MirSource::item(def.to_def_id()),
        IndexVec::from_raw(blocks),
        IndexVec::from_elem_n(
            SourceScopeData {
                span,
                parent_scope: None,
                inlined: None,
                inlined_parent_scope: None,
                local_data: ClearCrossCrate::Clear,
            },
            1,
        ),
        local_decls,
        IndexVec::new(),
        arg_count,
        vec![],
        span,
        None,
        None,
    );
    // Same table and phase arguments as the WrappingBinOp emitter: the mono
    // collector collects every callee as a **used** item by walking this very
    // body, no optimization ever runs on it (`optimized_mir` returns it
    // directly), and the only constants are inline evaluated scalars.
    body.set_mentioned_items(Vec::new());
    body.set_required_consts(Vec::new());
    body.phase = MirPhase::Runtime(RuntimePhase::Optimized);
    body
}

/// Emit the R2/C5a Select shape: the four-block O0 diamond `recognize_select`
/// was written for, years before this lane —
///
/// ```text
/// bb0: _{n+2} = Cmp(copy _{cl+1}, copy _{cr+1}); switchInt(_{n+2}) -> [0: bb2, otherwise: bb1]
/// bb1: _{n+1} = copy _{then+1}; goto bb3        // otherwise == the TRUE arm
/// bb2: _{n+1} = copy _{else+1}; goto bb3        // 0 == the FALSE arm
/// bb3: _0 = copy _{n+1}; return
/// ```
///
/// THE POLARITY TRAP, named where the code is: `SwitchTargets::static_if(v,
/// then_, else_)` puts `v`'s target FIRST and `otherwise` LAST — so the call
/// below is `static_if(0, bb_ELSE, bb_THEN)`: the `0` (comparison FALSE)
/// value routes to the else arm, `otherwise` to the then arm. Getting the
/// argument order wrong silently emits max where the island wrote min — it
/// is the exact mutation the divergence knob injects, and the faithfulness
/// gate is what makes it unshippable rather than this comment.
#[allow(clippy::too_many_arguments)]
fn build_select_body<'tcx>(
    tcx: TyCtxt<'tcx>,
    def: LocalDefId,
    plan: &CleanOriginPlan,
    cmp: SelectCmp,
    cmp_left: usize,
    cmp_right: usize,
    then_param: usize,
    else_param: usize,
    span: Span,
) -> Body<'tcx> {
    let return_ty = carrier_to_rustc_ty(tcx, plan.return_ty(), span);
    let param_tys: Vec<_> =
        plan.param_tys().iter().map(|ty| carrier_to_rustc_ty(tcx, ty, span)).collect();
    let arg_count = param_tys.len();

    // `_0` ret, `_1..=_n` params, `_{n+1}` the select temp at the result
    // carrier, `_{n+2}` the bool the comparison writes.
    let select_temp = Local::from_usize(arg_count + 1);
    let cmp_local = Local::from_usize(arg_count + 2);
    let local_decls: IndexVec<Local, LocalDecl<'tcx>> =
        std::iter::once(LocalDecl::new(return_ty, span))
            .chain(param_tys.into_iter().map(|ty| LocalDecl::new(ty, span).immutable()))
            .chain([LocalDecl::new(return_ty, span), LocalDecl::new(tcx.types.bool, span)])
            .collect();

    let source_info = SourceInfo::outermost(span);
    let bin_op = match cmp {
        SelectCmp::Lt => BinOp::Lt,
        SelectCmp::Le => BinOp::Le,
        SelectCmp::Eq => BinOp::Eq,
    };
    let assign = |place: Place<'tcx>, rvalue: Rvalue<'tcx>| {
        Statement::new(source_info, StatementKind::Assign(Box::new((place, rvalue))))
    };
    let copy_param = |i: usize| Operand::Copy(Place::from(Local::arg(i)));
    let goto_join = Some(Terminator {
        source_info,
        kind: TerminatorKind::Goto { target: BasicBlock::from_u32(3) },
        attributes: ThinVec::new(),
    });

    let entry = BasicBlockData::new_stmts(
        vec![assign(
            Place::from(cmp_local),
            Rvalue::BinaryOp(bin_op, Box::new((copy_param(cmp_left), copy_param(cmp_right)))),
        )],
        Some(Terminator {
            source_info,
            kind: TerminatorKind::SwitchInt {
                discr: Operand::Copy(Place::from(cmp_local)),
                // See the header: 0 (FALSE) -> bb2 (else), otherwise -> bb1 (then).
                targets: SwitchTargets::static_if(
                    0,
                    BasicBlock::from_u32(2),
                    BasicBlock::from_u32(1),
                ),
            },
            attributes: ThinVec::new(),
        }),
        false,
    );
    let then_arm = BasicBlockData::new_stmts(
        vec![assign(
            Place::from(select_temp),
            Rvalue::Use(copy_param(then_param), WithRetag::Yes),
        )],
        goto_join.clone(),
        false,
    );
    let else_arm = BasicBlockData::new_stmts(
        vec![assign(
            Place::from(select_temp),
            Rvalue::Use(copy_param(else_param), WithRetag::Yes),
        )],
        goto_join,
        false,
    );
    let join = BasicBlockData::new_stmts(
        vec![assign(
            Place::return_place(),
            Rvalue::Use(Operand::Copy(Place::from(select_temp)), WithRetag::Yes),
        )],
        Some(Terminator {
            source_info,
            kind: TerminatorKind::Return,
            attributes: ThinVec::new(),
        }),
        false,
    );

    let mut body = Body::new(
        MirSource::item(def.to_def_id()),
        IndexVec::from_raw(vec![entry, then_arm, else_arm, join]),
        IndexVec::from_elem_n(
            SourceScopeData {
                span,
                parent_scope: None,
                inlined: None,
                inlined_parent_scope: None,
                local_data: ClearCrossCrate::Clear,
            },
            1,
        ),
        local_decls,
        IndexVec::new(),
        arg_count,
        vec![],
        span,
        None,
        None,
    );
    // A select mentions no other item and its only rvalues are comparisons
    // and copies of locals — both tables are honestly empty, same argument as
    // the sibling emitters.
    body.set_mentioned_items(Vec::new());
    body.set_required_consts(Vec::new());
    body.phase = MirPhase::Runtime(RuntimePhase::Optimized);
    body
}

/// The rustc type a discharged I4 carrier denotes.
///
/// Deliberately TOTAL over nothing: the match is exhaustive over the carriers
/// I4 can currently grant, and anything else is a hard internal error rather
/// than a fallback type. A guessed type here is a wrong binary — it would
/// change what the emitted body computes while the kernel comparison, which
/// runs over the trust-types view, might still agree.
/// Trust: (I7) — `pub(crate)` for the import re-gate (`clean_origin_import`), which
/// must cross-check the exporter's ENCODED signature against the plan's carriers
/// with the SAME carrier -> rustc-type mapping the local emitter uses.
pub(crate) fn carrier_to_rustc_ty<'tcx>(
    tcx: TyCtxt<'tcx>,
    carrier: &trust_types::Ty,
    span: Span,
) -> Ty<'tcx> {
    match carrier {
        trust_types::Ty::Bool => tcx.types.bool,
        trust_types::Ty::Int { width: 8, signed: false } => tcx.types.u8,
        trust_types::Ty::Int { width: 16, signed: false } => tcx.types.u16,
        trust_types::Ty::Int { width: 32, signed: false } => tcx.types.u32,
        trust_types::Ty::Int { width: 64, signed: false } => tcx.types.u64,
        trust_types::Ty::BignumNat => {
            // Trust (I6): the bignum carrier. Resolved through the ONE DefId
            // of record — loaded and sanity-checked by the creader
            // (`CStore::trust_load_bignum_carrier`) at the mint seam, recorded
            // into `ResolverGlobalCtxt::trust_bignum_nat`, and used to feed
            // this def's `fn_sig`; `check_signature_agrees` already makes any
            // divergence between the two readings fatal. Absence here is a
            // post-mint impossibility: a Nat grant that survived demotion has
            // the DefId on record.
            let Some(nat) = tcx.resolutions(()).trust_bignum_nat else {
                tcx.dcx().span_fatal(
                    span,
                    "internal: Clean-origin carrier `trust_bignum::Nat` was granted but no \
                     `Nat` DefId is on record from the resolve-time carrier load. This is a \
                     compiler defect and nothing you write will change it. Please report it.",
                );
            };
            Ty::new_adt(tcx, tcx.adt_def(nat), rustc_middle::ty::List::empty())
        }
        other => tcx.dcx().span_fatal(
            span,
            format!(
                "internal: Clean-origin carrier `{other:?}` was granted by \
                 `trust-clean-carrier` but has no rustc type in this compiler. Refusing to \
                 guess: a wrong carrier type is an emitted value that disagrees with the \
                 declaration, which kernel definitional equality would not catch. Please \
                 report it."
            ),
        ),
    }
}
