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
    BasicBlock, BasicBlockData, BinOp, Body, BorrowKind, CallSource, ClearCrossCrate, Local,
    LocalDecl, MirPhase, MirSource, Operand, Place, RuntimePhase, Rvalue, SourceInfo,
    SourceScopeData, Statement, StatementKind, SwitchTargets, Terminator, TerminatorKind,
    UnwindAction, WithRetag,
};
use rustc_middle::ty::fast_reject::SimplifiedType;
use rustc_middle::ty::{GenericArg, Ty, TyCtxt, UintTy};
// Trust (§6f landing 1): `sym` is gone from this import because the callee
// method name now comes from the ONE authenticated identity
// (`PrimitiveCallee::rust_method_name`) rather than from a preinterned symbol
// chosen here. That also keeps this file off `symbols!`, which the frozen-std
// symbol-index ABI note (`docs/FROZEN_STD_SYMBOL_INDEX_ABI.md`) makes a
// measurement hazard.
use rustc_span::{Span, Spanned, Symbol};
// Trust (§6f landing 4): the shape vocabulary is GONE from this import.
// `ArithBinOp`/`ArithExpr`/`ArithOperand`/`RecBodyExpr`/`CleanOriginShape` were
// here because nine hand-written builders destructured a planned shape; the one
// materializer below destructures no shape at all, and reading a plan is
// `trust_clean_origin::materialize`'s job. What remains is the ONE authenticated
// callee identity, the comparison vocabulary the diamond's `BinaryOp` needs, and
// the template types the emitter interprets.
use trust_clean_origin::materialize::{
    BodyTemplate, TemplateCallee, TemplateOperand, TemplateRvalue, TemplateTerminator, TemplateTy,
    TemplateUnwind,
};
use trust_clean_origin::{CleanOriginPlan, EmitRefusal};
use trust_types::admissible_body::{PrimitiveCallee, RawBinOpKind, SelectCmp};

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
/// Called at the very TOP of `inner_optimized_mir`, `inner_mir_for_ctfe` and
/// `mir_drops_elaborated_and_const_checked`, before `is_constructor` and before
/// `hir_body_const_context` — the latter matters because a Clean-origin def has
/// no HIR and `hir_body_const_context`'s `None` arm in the CTFE provider is a
/// hard `bug!`.
///
/// The third of those is the ANALYSIS-PHASE arm, added 2026-08-19 after both
/// island fixtures were measured ICEing at `rustc_hir_typeck/src/lib.rs:191`.
/// A def in `mir_keys` obliges every provider on the analysis chain
/// (`mir_drops_elaborated_and_const_checked` -> `mir_borrowck` ->
/// `mir_promoted` -> `mir_built` -> `check_match` -> `typeck_root`) to answer,
/// not only the codegen and CTFE arms; the Trust verification lane's own
/// `mir_keys` loops ask for the elaborated body directly.
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
/// `CleanOriginDecl` rather than of the registry lookup — the live emission and
/// gate can be driven directly by unit controls without depending on how the
/// production mint registered a def as Clean-origin.
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

    // ── side C: the TRUSTIR spelling of the same plan ──────────────────────
    //
    // Trust: the two authoritative languages are supposed to meet in TrustIR,
    // and until `trust-clean-ir` existed only Rust produced it -- Clean stopped
    // at the MIR below. This derives the TrustIR function for the SAME sealed
    // plan, at the same point, so there is no second planning step and
    // therefore no second place a signature or a width can disagree.
    //
    // It is used here for a THIRD, independent spelling of the signature. The
    // MIR arity comes from `carrier_to_rustc_ty` via the template; the fed
    // `fn_sig` came from `trust_clean_mint::rustc_ty`; this one comes from
    // `trust_clean_ir::trust_ir_func_ty` reading the carriers directly. Three
    // spellings that must agree is the same discipline
    // `check_signature_agrees` already applies to the first two, extended to
    // the third rather than left as an unchecked parallel lane.
    //
    // A REFUSAL IS NOT FATAL, deliberately. `trust-clean-ir` does not spell
    // every shape the MIR lane emits -- the two recursion shapes compute at the
    // unbounded bignum `Nat`, which TrustIR has no type for -- and a
    // capability gap in a lane that produces no binary must never fail a
    // compilation the MIR lane can complete. What IS fatal is a TrustIR
    // signature that disagrees with the plan's arity: that is the two lanes
    // reading one carrier signature differently, which is the wrong-binary
    // shape this whole file exists to prevent.
    if let Ok(func_ty) = trust_clean_ir::trust_ir_func_ty(plan.signature())
        && (func_ty.params.len() != plan.signature().arity() || func_ty.returns.len() != 1)
    {
        tcx.dcx().span_fatal(
            decl.span,
            format!(
                "internal: the TrustIR and MIR spellings of Clean declaration `{}` disagree \
                 about its signature — TrustIR derived {} parameter(s) and {} result(s) from \
                 the same sealed carrier signature the MIR lane reads as arity {}. These are \
                 two independent readings of ONE plan, so a disagreement means one of them is \
                 building against a signature the other does not have. Please report it.",
                decl.name,
                func_ty.params.len(),
                func_ty.returns.len(),
                plan.signature().arity(),
            ),
        );
    }

    // ── the ROW PREFLIGHT and the TEMPLATE (Trust, §6f landings 1 and 4) ───
    //
    // The ladder is an OPTIMIZATION LADDER, never a capability boundary: every
    // `CleanOriginShape` rung selects a row of the instruction-selection table,
    // and the row DECLARES the MIR realization to build. Landing 1 put the row
    // preflight here and left six hand-written builders behind it; landing 4
    // deleted the builders. What replaces them is ONE description —
    // `trust_clean_origin::materialize::body_template` — which decides every
    // block, local, operand, `Copy`-vs-`Move` and unwind edge on the FAST LANE,
    // and one `materialize` below that translates a description into
    // `mir::Body` with no shape knowledge at all.
    //
    // Three fail-closed properties come out of that, and all three are the
    // landing's point rather than decoration:
    //
    //   * a realization nobody wrote a skeleton for is a COMPILE ERROR, in
    //     `body_template`'s wildcard-free match over `MirShape` — which is
    //     `cargo check -p trust-clean-origin`, two seconds into the edit,
    //     rather than an hour into a bootstrap. The emitter keeps its own
    //     exhaustiveness at the layer it still owns: `TemplateTerminator`,
    //     `TemplateRvalue`, `TemplateOperand`, `TemplateTy` and
    //     `TemplateCallee` are equally closed, and `materialize` matches each
    //     with no `_ =>` arm, so a new realization PRIMITIVE is a compile error
    //     here.
    //
    //   * a row whose declared realization DISAGREES with the planned shape is
    //     fatal, before anything is emitted. That is the emitter-side half of
    //     the shape-drift hazard a general emitter opens: the fast lane's
    //     `h_c_shared_mir_realizations_are_declared_and_separated` proves no
    //     two rows are realized indistinguishably, and this proves the row a
    //     plan selected is the one that gets built.
    //
    //   * the emitted UNWIND EDGE is taken FROM the row, not hand-written
    //     alongside it. H-G's hazard is an emitted edge nobody declared, and
    //     until this landing the fact lived in two places.
    //
    // BYTE IDENTITY, and where it is established: every template is compared
    // against the body the SHIPPED builder was measured to emit, in
    // `crates/trust-clean-origin/tests/control_11_materializer_byte_identity.rs`
    // — block order, local numbering including the two dead arm temps R1/R2
    // leave declared, `Copy`-vs-`Move`, `SwitchInt` polarity, the per-call
    // unwind edge, `WithRetag`, `LocalDecl::immutable()` and the callee paths
    // the extractor renders — and then put through the real `admit_lowering`.
    let Some(row) = trust_clean_origin::table::ladder_row(plan.shape()) else {
        tcx.dcx().span_fatal(
            decl.span,
            format!(
                "internal: the plan for Clean declaration `{}` has a shape that selects no \
                 row of the instruction-selection table, so there is no declared MIR \
                 realization to emit and NOTHING WAS EMITTED. This is a compiler defect — a \
                 ladder rung was added without its row. Please report it.",
                decl.name,
            ),
        );
    };
    let template = match trust_clean_origin::materialize::body_template(row, &plan) {
        Ok(template) => template,
        Err(refusal) => tcx.dcx().span_fatal(decl.span, refusal.note(decl.name, row, plan.shape())),
    };

    // ── the emission ───────────────────────────────────────────────────────
    //
    // ONE materializer, driven by the description above. It branches on no
    // shape, resolves no vocabulary and makes no choice a wrong binary could
    // hide in — see its own doc comment for the three `TyCtxt` facts that are
    // genuinely its to decide.
    let mut body = materialize(tcx, def, &plan, &template, decl.span);

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
    // This is exercised by the live mint/provider UI lane and its cross-crate
    // recursive-Nat control; the synthetic unit controls keep the same
    // extractor boundary independently measurable.
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
    let expected_inputs: Vec<Ty<'tcx>> =
        plan.param_tys().iter().map(|ty| carrier_to_rustc_ty(tcx, ty, decl.span)).collect();
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
/// boundary and the ways around it. A correctness refusal says the compiler
/// could not establish that its own emitted body agrees; it does not overclaim
/// a semantic counter-proof when bounded proof search merely found no proof.
/// Telling a user to add an annotation here would send them to fix something
/// they did not break.
fn refuse(tcx: TyCtxt<'_>, decl: &CleanOriginDecl<'_>, refusal: &EmitRefusal) -> ! {
    let headline = if refusal.is_compiler_defect() {
        format!(
            "internal: refusing to emit code for Clean declaration `{}` — the emitted body \
             could not be established to agree with the declaration",
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
/// * select (R2/C5a) AND select-vs-literal (R2/C9 — both shapes emit the
///   same diamond, so one mutation covers both): swap the `SwitchInt`
///   targets — the exact polarity-inversion bug `SwitchTargets::static_if`'s
///   argument order invites, which silently emits max where the island wrote
///   min. The gate, not this comment, is what makes that bug impossible to
///   ship.
/// * constant (§6f landing 2): **NOT COVERED, stated rather than implied.**
///   The constant body has no `SwitchInt` and its return assignment is an
///   `Operand::Constant`, not a `Move`, so both mutations below fall through
///   and this knob is a NO-OP on it — a ui divergence fixture pointed at a
///   constant declaration would therefore pass for the wrong reason. Mutating
///   a scalar here would mean rebuilding a `ConstOperand` without a `TyCtxt`,
///   which this function does not have. The constant shape's emitter
///   mutations are covered instead on the FAST lane, by
///   `tests/control_9_constant_emitter_mutation.rs`, which injects the wrong
///   value, the wrong arity (both directions), a width-skewed scalar, a
///   non-constant body and the wrong POSITION of the numeral row directly into
///   the extracted body — strictly more direct than this knob, which exists
///   only because the projection and select fixtures needed an end-to-end
///   route through a real compilation.
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

/// **THE ONE MATERIALIZER** (Trust, §6f landing 4): turn a
/// [`BodyTemplate`] into the `mir::Body` this crate emits.
///
/// It replaces `build_projection_body`, `build_constant_body`,
/// `build_wrapping_binop_body`, `build_composed_body`, `build_select_body`,
/// `build_select_literal_body`, `build_select_operands_body`,
/// `build_structural_rec_body` and `build_nat_zero_test_rec_body`. §6f's
/// ruling: `CleanOriginShape` is an optimization ladder, never a capability
/// boundary — so adding a row adds a TABLE ENTRY plus, at most, a skeleton in
/// `trust_clean_origin::materialize`, and never an emitter.
///
/// # It decides NOTHING about the shape, deliberately
///
/// Every choice a wrong binary could hide in — which block, which local, which
/// operand, `Copy` versus `Move`, the `SwitchInt` polarity, the unwind edge —
/// was made in `body_template`, which `cargo test -p trust-clean-origin` runs
/// in two seconds and which `control_11` compares BYTE FOR BYTE against the
/// bodies the deleted builders were measured to emit. This function branches on
/// no shape and no ladder rung. What is left to it is exactly three `TyCtxt`
/// facts, each of which is genuinely a compiler question:
///
///  1. **the carrier types.** [`TemplateTy`] names a POSITION (the result
///     carrier, parameter `i`, `bool`, `&result`); `carrier_to_rustc_ty` is
///     I4's decision and stays the only carrier -> rustc mapping in this file,
///     so `check_signature_agrees` still guards the one duplication I5 could
///     not avoid.
///  2. **the callee `DefId`s.** The template carries the ONE authenticated
///     identity and never a path — see [`resolve_template_callee`].
///  3. **`Body::new` and the phase/table discipline**, once instead of nine
///     times.
///
/// # WHY BOTH SIDE TABLES ARE EMPTY, and why the phase is `Optimized`
///
/// `mentioned_items` stays empty SOUNDLY: the mono collector collects every
/// callee (the core primitives, the bignum runtime AND the self-call) as a
/// **used** item by walking this very body — used and mentioned are collected
/// independently and there is no `used ⊆ mentioned` assertion — and no
/// optimization ever runs on this body to delete a call.
/// `required_consts` is honestly empty: every constant here is an inline
/// evaluated scalar, so nothing needs evaluation and nothing can promote.
/// Both are filled EXPLICITLY because the passes that would otherwise populate
/// them do not run: `optimized_mir`/`mir_for_ctfe` return this body directly,
/// deliberately skipping `run_optimization_passes`, because a pass that rewrote
/// it after the gate ran would put un-gated code in the binary.
///
/// `MirPhase::Runtime(RuntimePhase::Optimized)` is the honest phase and not a
/// label chosen to satisfy an assertion. MEASURED 2026-08-19: `Body::new`
/// starts at `MirPhase::Built` and `TyCtxt::instance_mir` asserts
/// `Runtime(_)` — the assertion fires the moment a Clean-origin function is
/// actually CALLED at runtime (the const fixture missed it, because a `const`
/// goes through `mir_for_ctfe` and is never a mono item). This body is emitted
/// in its final form and no pass will ever run on it, so there is no earlier
/// phase it is ever in, and `docs/TCB.md`'s trusted-after-gate surface stays
/// caller-side inlining, codegen and the backend.
///
/// A self-recursive body at `Runtime(Optimized)` is ordinary MIR for codegen;
/// the INLINER's cycle machinery (`mir_callgraph_cyclic`) on a HIR-less def is
/// UNMEASURED until the run-pass fixture compiles — if it bites, the fallback
/// is excluding Clean-origin defs from inlining candidacy, a performance cost
/// and never a correctness one. Recorded in
/// `tests/ui/trust/clean_origin_structural_rec.rs`.
#[allow(rustc::usage_of_qualified_ty)]
fn materialize<'tcx>(
    tcx: TyCtxt<'tcx>,
    def: LocalDefId,
    plan: &CleanOriginPlan,
    template: &BodyTemplate,
    span: Span,
) -> Body<'tcx> {
    let return_ty = carrier_to_rustc_ty(tcx, plan.return_ty(), span);
    let param_tys: Vec<Ty<'tcx>> =
        plan.param_tys().iter().map(|ty| carrier_to_rustc_ty(tcx, ty, span)).collect();
    let source_info = SourceInfo::outermost(span);

    // `LocalDecl::immutable()` on parameters only, exactly as
    // `local_decls_for_sig` makes them for a shim — carried by the template
    // because the extractor cannot see it, so `control_11`'s half_8 is what
    // pins it rather than a round trip.
    let local_decls: IndexVec<Local, LocalDecl<'tcx>> = template
        .locals
        .iter()
        .map(|local| {
            let ty = match local.ty {
                TemplateTy::Result => return_ty,
                TemplateTy::Param { index } => param_tys[index],
                TemplateTy::Bool => tcx.types.bool,
                TemplateTy::ResultRef => Ty::new_imm_ref(tcx, tcx.lifetimes.re_erased, return_ty),
            };
            let decl = LocalDecl::new(ty, span);
            if local.immutable { decl.immutable() } else { decl }
        })
        .collect();

    let operand = |source: TemplateOperand| -> Operand<'tcx> {
        match source {
            TemplateOperand::Copy(local) => Operand::Copy(Place::from(Local::from_usize(local))),
            TemplateOperand::Move(local) => Operand::Move(Place::from(Local::from_usize(local))),
            TemplateOperand::ResultScalar { value, width } => Operand::const_from_scalar(
                tcx,
                return_ty,
                Scalar::from_uint(value, Size::from_bits(u64::from(width))),
                span,
            ),
            TemplateOperand::U64Scalar(value) => Operand::const_from_scalar(
                tcx,
                tcx.types.u64,
                Scalar::from_uint(value, Size::from_bits(64)),
                span,
            ),
            // Trust (§6f landing 6): the `bool` constant. It is a NEW
            // realization primitive, and landing 4 made a new primitive a
            // compile error in this wildcard-free match DELIBERATELY — landing
            // 5 measured the demand for it and declined to add it, because a
            // lane that cannot run x.py must not break the compiler's closed
            // match mid-type-check. This is that cost paid, with the constraint
            // lifted.
            //
            // It is a `TyCtxt` question in exactly the way `carrier_to_rustc_ty`
            // is: neither existing scalar could spell it, because
            // `ResultScalar` is at the result carrier and `U64Scalar` at `u64`,
            // and comparing a `bool` local against either is ill-typed MIR.
            // `Scalar::from_bool` rather than a hand-rolled `from_uint(1, 8)`:
            // the encoding of `bool` is rustc's to state, not this file's, and
            // the extractor reads it back through `try_to_bool` into
            // `trust_types::ConstValue::Bool` — so side B sees a boolean, never
            // a one-byte integer it would have to interpret.
            TemplateOperand::BoolScalar(value) => {
                Operand::const_from_scalar(tcx, tcx.types.bool, Scalar::from_bool(value), span)
            }
        }
    };

    let blocks: Vec<BasicBlockData<'tcx>> = template
        .blocks
        .iter()
        .map(|block| {
            let stmts: Vec<Statement<'tcx>> = block
                .stmts
                .iter()
                .map(|stmt| {
                    let rvalue = match stmt.rvalue {
                        TemplateRvalue::Use(value) => Rvalue::Use(operand(value), WithRetag::Yes),
                        TemplateRvalue::Compare { cmp, left, right } => Rvalue::BinaryOp(
                            match cmp {
                                SelectCmp::Lt => BinOp::Lt,
                                SelectCmp::Le => BinOp::Le,
                                SelectCmp::Eq => BinOp::Eq,
                            },
                            Box::new((operand(left), operand(right))),
                        ),
                        // Trust (§6f landing 7): the RAW BINARY OPERATOR at the
                        // result carrier — `&`, `|`, `/`, `%`. A NEW
                        // realization primitive, and landing 4 made a new
                        // primitive a compile error in this wildcard-free match
                        // DELIBERATELY; this is that cost paid, exactly as
                        // `TemplateOperand::BoolScalar` paid it in landing 6.
                        //
                        // NO `Assert`, and that is the load-bearing line in
                        // this arm. `BinOp::Div`'s own documentation in
                        // `rustc_middle::mir::syntax` states the obligation:
                        // *"For integer types, division by zero is UB, as is
                        // `MIN / -1` for signed. The compiler should have
                        // inserted checks prior to this."* Both halves are
                        // discharged, and neither by a check:
                        //
                        //  * DIVISION BY ZERO — `trust_clean_origin`'s planner
                        //    refuses a `Div`/`Rem` plan whose right operand is
                        //    not a STRICTLY POSITIVE numeral, so the divisor is
                        //    a nonzero constant here by construction. That rule
                        //    exists for a semantic reason and not for this one:
                        //    Clean's `UInt{N}.div`/`.mod` are TOTAL
                        //    (`x / 0 = 0`, `x % 0 = x`) while Rust's `/`/`%`
                        //    panic, so a variable or zero divisor would emit a
                        //    body computing a DIFFERENT function from the
                        //    declaration — a wrong binary, which is the failure
                        //    this whole lane is organised around. The UB is
                        //    excluded as a corollary.
                        //  * `MIN / -1` — the carrier is an UNSIGNED machine
                        //    width in every position (`CarrierSignature` cannot
                        //    exist otherwise), so the signed case is
                        //    unrepresentable.
                        //
                        // Source-level `/` and `%` acquire a div-by-zero
                        // `Assert` during MIR BUILDING; a Clean-origin body is
                        // not built from source, so there is no assertion to
                        // emit and `TemplateTerminator` has no `Assert` variant
                        // to add.
                        //
                        // The match is over `RawBinOpKind` and is CLOSED with
                        // no wildcard, exactly as the `SelectCmp` arm above is,
                        // and for the same reason: a fifth operator must be a
                        // compile error here rather than a fall-through into
                        // the wrong instruction. Side B reads the emitted body
                        // back through `RawBinOpKind::from_mir_binop`, whose
                        // match is closed over the same four values — so a new
                        // variant breaks BOTH directions at once, which is the
                        // property that keeps them from drifting.
                        TemplateRvalue::RawBin { op, left, right } => Rvalue::BinaryOp(
                            match op {
                                RawBinOpKind::BitAnd => BinOp::BitAnd,
                                RawBinOpKind::BitOr => BinOp::BitOr,
                                RawBinOpKind::Div => BinOp::Div,
                                RawBinOpKind::Rem => BinOp::Rem,
                            },
                            Box::new((operand(left), operand(right))),
                        ),
                        TemplateRvalue::SharedRef(of) => Rvalue::Ref(
                            tcx.lifetimes.re_erased,
                            BorrowKind::Shared,
                            Place::from(Local::from_usize(of)),
                        ),
                    };
                    Statement::new(
                        source_info,
                        StatementKind::Assign(Box::new((
                            Place::from(Local::from_usize(stmt.place)),
                            rvalue,
                        ))),
                    )
                })
                .collect();
            let kind = match &block.terminator {
                TemplateTerminator::Return => TerminatorKind::Return,
                TemplateTerminator::Goto(target) => {
                    TerminatorKind::Goto { target: BasicBlock::from_usize(*target) }
                }
                // `SwitchTargets::static_if(v, v_target, otherwise)` puts `v`'s
                // target FIRST — the polarity trap the template's own
                // `SwitchIntZero` names, and the exact mutation the divergence
                // knob below injects.
                TemplateTerminator::SwitchIntZero { discr, zero, otherwise } => {
                    TerminatorKind::SwitchInt {
                        discr: operand(*discr),
                        targets: SwitchTargets::static_if(
                            0,
                            BasicBlock::from_usize(*zero),
                            BasicBlock::from_usize(*otherwise),
                        ),
                    }
                }
                TemplateTerminator::Call { callee, args, dest, target, unwind } => {
                    TerminatorKind::Call {
                        func: Operand::function_handle(
                            tcx,
                            resolve_template_callee(tcx, def, *callee, span),
                            // No generics on an inherent uint or `Nat` method,
                            // and none on the self-call.
                            std::iter::empty::<GenericArg<'tcx>>(),
                            span,
                        ),
                        args: args
                            .iter()
                            .map(|arg| Spanned { node: operand(*arg), span })
                            .collect::<Vec<_>>()
                            .into_boxed_slice(),
                        destination: Place::from(Local::from_usize(*dest)),
                        target: Some(BasicBlock::from_usize(*target)),
                        unwind: match unwind {
                            TemplateUnwind::Unreachable => UnwindAction::Unreachable,
                            TemplateUnwind::Continue => UnwindAction::Continue,
                        },
                        call_source: CallSource::Misc,
                        fn_span: span,
                    }
                }
            };
            BasicBlockData::new_stmts(
                stmts,
                Some(Terminator { source_info, kind, attributes: ThinVec::new() }),
                false,
            )
        })
        .collect();

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
        template.arg_count,
        vec![],
        span,
        None,
        None,
    );
    body.set_mentioned_items(Vec::new());
    body.set_required_consts(Vec::new());
    body.phase = MirPhase::Runtime(RuntimePhase::Optimized);
    body
}

/// The `DefId` a template callee denotes.
///
/// THE SELF-CALL is `def.to_def_id()` ITSELF — the def being built; resolution
/// against its own `DefId`, no lookup. It is not a primitive and has no
/// authenticated identity: the recognizer matches it against `func.def_path`
/// and the kernel re-decides the argument.
///
/// A primitive splits on `machine_width()`, which is the identity's own
/// classification and not a second table: the three wrapping ops carry a width
/// and resolve on `core`'s inherent uint impls; the four bignum methods carry
/// none and resolve on the ONE `trust_bignum::Nat` `DefId` of record. Both
/// resolvers AUTHENTICATE their candidate from `TyCtxt` facts and both are
/// fatal on a non-unique result — see their own docs for why a resolution
/// mistake still cannot emit a wrong binary.
fn resolve_template_callee<'tcx>(
    tcx: TyCtxt<'tcx>,
    def: LocalDefId,
    callee: TemplateCallee,
    span: Span,
) -> DefId {
    match callee {
        TemplateCallee::SelfDef => def.to_def_id(),
        TemplateCallee::Primitive(identity) if identity.machine_width().is_some() => {
            resolve_core_wrapping_method(tcx, identity, span)
        }
        TemplateCallee::Primitive(identity) => resolve_bignum_method(tcx, identity, span),
    }
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
///
/// Trust (§6f landing 1): the callee is named by the ONE authenticated identity
/// [`PrimitiveCallee`], which is also what `trust_types::admissible_body`'s
/// reader classifies the extracted path through. A selection row carries one of
/// these, not an `emit:` field and a separate `side_b:` field — two adjacent
/// independently-authored fields are one edit, not two authorships, and the
/// review of the general-reflector design named exactly that as the way a table
/// manufactures a wrong binary. Note what is still NOT shared: this function
/// resolves by METHOD NAME and authenticates the candidate from `TyCtxt` facts,
/// while side B classifies a path the extractor re-renders independently. The
/// identity fixes WHICH primitive; neither side is told what the other will
/// see.
fn resolve_core_wrapping_method<'tcx>(
    tcx: TyCtxt<'tcx>,
    callee_identity: PrimitiveCallee,
    span: Span,
) -> DefId {
    let width_bits = match callee_identity.machine_width() {
        Some(width) => width,
        None => tcx.dcx().span_fatal(
            span,
            "internal: a WrappingBinOp plan reached the emitter with a callee identity that \
             is not a machine-width core primitive. This is a compiler defect. Please \
             report it.",
        ),
    };
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
    let method = Symbol::intern(callee_identity.rust_method_name());

    let candidates: Vec<DefId> = tcx
        .incoherent_impls(SimplifiedType::Uint(uint))
        .iter()
        .filter(|&&impl_did| {
            tcx.type_of(impl_did).instantiate_identity().skip_norm_wip() == self_ty
        })
        .flat_map(|&impl_did| {
            tcx.associated_items(impl_did).filter_by_name_unhygienic(method).map(|item| item.def_id)
        })
        .filter(|&did| {
            trust_mir_extract::tcx_is_authenticated_core_integer_wrapping_method(tcx, did)
        })
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

/// The `DefId` of `trust_bignum::Nat`'s inherent method `method_name`,
/// resolved from the ONE `Nat` DefId of record
/// (`ResolverGlobalCtxt::trust_bignum_nat` — loaded and
/// sysroot-residency-checked by the creader at the mint seam) and REQUIRED
/// UNIQUE. Fatal on zero or multiple candidates.
///
/// Mirrors `resolve_core_wrapping_method`'s discipline for the same reason:
/// the emitter never writes the recognizer's callee string — the extractor
/// re-renders it at read-back from `TyCtxt` facts (`safe_def_path_str`),
/// independently of this resolution — so a wrong `DefId` here yields a callee
/// path the recognizer refuses, `admit_lowering` returns
/// `LoweringUnrecognised`, and `refuse` is fatal. The RUNTIME-SEMANTICS claim
/// (that the resolved methods realise kernel `Nat`'s constructor analysis and
/// arithmetic) is the `trust_bignum` TCB row (differential-tested), never a
/// kernel statement — see the Clean-origin recursive-body row in
/// `docs/TCB.md`.
///
/// MEASURED 2026-08-21, and the reason the first R1 fixture run refused at the
/// gate: the path the extractor re-renders for a resolved method depends on
/// WHICH MODULE THE `impl` BLOCK IS TYPED IN, not on the method. rustc's
/// inherent-impl printer emits `Type::method` when the `impl` sits in the
/// type's own module and `module::<impl Type>::method` when it does not, so
/// this resolution yields `trust_bignum::Nat::is_zero` (root impl) but
/// `trust_bignum::arith::<impl trust_bignum::Nat>::sub` (`mod arith`). This
/// emitter can neither see nor influence that — it hands over a `DefId` — so
/// side B's `bignum_callee` is where the fact is recorded, and moving a
/// trust-bignum `impl` block between modules refuses this lane fail-closed
/// until that table is re-measured. Do NOT mirror side B's table here: side A
/// asserting what side B will accept is exactly the independence the gate
/// exists to have.
///
/// Trust (§6f landing 1): the method is named by the ONE authenticated identity
/// [`PrimitiveCallee`] — the same value a selection row carries and the same
/// value side B's classifier returns — so there is no second spelling for an
/// emit/read disagreement to live in. The paragraph above is UNCHANGED by that
/// and is the reason the identity hands over a METHOD NAME rather than a path:
/// the path is the extractor's to render and side B's to classify, and side A
/// must not assert what side B will accept.
fn resolve_bignum_method<'tcx>(
    tcx: TyCtxt<'tcx>,
    callee_identity: PrimitiveCallee,
    span: Span,
) -> DefId {
    let Some(nat) = tcx.resolutions(()).trust_bignum_nat else {
        tcx.dcx().span_fatal(
            span,
            "internal: a StructuralNatRec plan reached the emitter but no \
             `trust_bignum::Nat` DefId is on record from the resolve-time carrier load. \
             This is a compiler defect. Please report it.",
        );
    };
    let method_name = callee_identity.rust_method_name();
    let method = Symbol::intern(method_name);
    let candidates: Vec<DefId> = tcx
        .inherent_impls(nat)
        .iter()
        .flat_map(|&impl_did| {
            tcx.associated_items(impl_did).filter_by_name_unhygienic(method).map(|item| item.def_id)
        })
        .collect();
    match candidates[..] {
        [callee] => callee,
        ref found => tcx.dcx().span_fatal(
            span,
            format!(
                "internal: resolution of `trust_bignum::Nat::{method_name}` was {} \
                 ({} candidate(s): {found:?}); the compiler will not guess which \
                 function to emit a call to. This is a compiler defect — please report \
                 it.",
                if found.is_empty() { "absent" } else { "ambiguous" },
                found.len(),
            ),
        ),
    }
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
            // divergence between the two readings fatal.
            //
            // MEASURED, and the reason the claim that used to stand here is
            // gone: "absence is a post-mint impossibility" was true of the
            // LOCAL lane only. The IMPORT lane reaches this function for a
            // grant minted in another crate, and the resolve-time load used to
            // fire only for a crate's own grants — so an import-only crate hit
            // this fatal on a well-formed program (fixture
            // `clean_origin_recursive_nat_cross_crate.rs`). The import trigger
            // (`Resolver::trust_resolve_imported_carrier_crates`) closes that
            // case. The fatal STAYS: it is now the honest report of a carrier
            // that is genuinely absent — a `trust_bignum` the loader refused
            // (no sysroot copy, `-Zbuild-std`), or an imported Nat carrier
            // reached by a route the resolver could not see. Refusing to guess
            // a carrier type is the only safe answer either way.
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
