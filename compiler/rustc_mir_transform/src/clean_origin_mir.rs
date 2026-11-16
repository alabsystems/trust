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
use rustc_middle::mir::trust_purity::TrustPurityFact;
use rustc_middle::mir::visit::{PlaceContext, Visitor};
use rustc_middle::mir::{
    BasicBlock, BasicBlockData, BinOp, Body, BorrowKind, CallSource, ClearCrossCrate, Local,
    LocalDecl, Location, MirPhase, MirSource, Operand, Place, ProjectionElem, RuntimePhase, Rvalue,
    SourceInfo, SourceScopeData, Statement, StatementKind, SwitchTargets, Terminator,
    TerminatorKind, UnOp, UnwindAction, WithRetag,
};
use rustc_middle::ty::fast_reject::SimplifiedType;
use rustc_middle::ty::{GenericArg, TrustCleanCarrier, Ty, TyCtxt, UintTy};
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
    let defs = &tcx.resolutions(()).clean_origin_defs;
    match defs.len() {
        0 => false,
        1..=8 => defs.iter().any(|&(candidate, _, _)| candidate == def),
        _ => {
            #[derive(Default)]
            struct CleanOriginDefSet(Option<rustc_data_structures::fx::FxHashSet<LocalDefId>>);
            tcx.sess.with_trust_compiler_state::<CleanOriginDefSet, _>(|state| {
                state
                    .0
                    .get_or_insert_with(|| defs.iter().map(|&(d, _, _)| d).collect())
                    .contains(&def)
            })
        }
    }
}

/// Trust: decode the parser's canonical source spelling with the actual Clean parser.
/// A registry/AST identity that cannot be decoded is a compiler inconsistency.
pub(crate) fn clean_source_name(tcx: TyCtxt<'_>, name: &str, span: Span) -> clean_kernel::Name {
    trust_certify::clean_island::island_source_name(name).unwrap_or_else(|error| {
        tcx.dcx().span_fatal(span, format!("internal: invalid Clean source identity: {error}"))
    })
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

/// Trust: (I7) — the crate's `clean { … }` island sources in authored order, or
/// `None` when an island's bytes could not be recovered. Factored out of
/// [`clean_crate_environment`] and shared with the `trust_clean_island_sources`
/// query so the transported sources and the environment the gate ran over
/// cannot disagree: the gate's environment is the pre-admission prefix of
/// exactly these sources (see [`clean_crate_environment`]).
pub(crate) fn collect_island_sources(tcx: TyCtxt<'_>) -> Option<Vec<String>> {
    Some(authored_islands(tcx)?.into_iter().map(|island| island.text).collect())
}

/// Trust (CLEAN-GENERAL-DEFERRED-1): one `clean { … }` island, by its HIR owner, with the
/// bytes [`collect_island_sources`] transports for it.
struct AuthoredIsland {
    owner: LocalDefId,
    text: String,
}

/// Trust (CLEAN-GENERAL-DEFERRED-1): the crate's islands in authored order, or `None`
/// when an island's bytes could not be recovered. The one walk behind
/// [`collect_island_sources`] and [`deferred_suffix_islands`], so the sources
/// the environment is checked over and the partition the general trust-ir lane
/// reads are computed from the same bytes in the same order.
fn authored_islands(tcx: TyCtxt<'_>) -> Option<Vec<AuthoredIsland>> {
    let mut islands: Vec<(rustc_span::Span, AuthoredIsland)> = Vec::new();
    for item_id in tcx.hir_crate_items(()).free_items() {
        if tcx.def_kind(item_id.owner_id) != rustc_hir::def::DefKind::GlobalAsm {
            continue;
        }
        let item = tcx.hir_item(item_id);
        let rustc_hir::ItemKind::CleanIsland { content_span, text, .. } = item.kind else {
            continue;
        };
        let text = if text.is_empty() {
            tcx.sess.source_map().span_to_snippet(content_span).ok()?
        } else {
            text.to_string()
        };
        islands.push((content_span, AuthoredIsland { owner: item_id.owner_id.def_id, text }));
    }
    // Authored source order: Clean file state (namespaces, `open`s, notation,
    // options) evolves across islands, and this is the same sort
    // `trust_check_clean_islands` and the resolve-time decision both apply.
    islands.sort_by_key(|(span, _)| (span.lo(), span.hi()));
    Some(islands.into_iter().map(|(_, island)| island).collect())
}

/// Trust (CLEAN-GENERAL-DEFERRED-1): the islands of the DEFERRED suffix, by HIR owner:
/// the first island that names `trust_import_*` and every island authored after
/// it (`trust_certify::clean_island::pre_admission_island_count`). These are
/// exactly the islands [`clean_crate_environment`] leaves out, so a declaration
/// in one of them is never in the environment that function returns. `None`
/// exactly when [`collect_island_sources`] is `None`, and then
/// [`clean_crate_environment`] is `None` too.
pub(crate) fn deferred_suffix_islands(
    tcx: TyCtxt<'_>,
) -> Option<rustc_data_structures::fx::FxHashSet<LocalDefId>> {
    let islands = authored_islands(tcx)?;
    let texts: Vec<&str> = islands.iter().map(|island| island.text.as_str()).collect();
    let prefix = trust_certify::clean_island::pre_admission_island_count(texts.as_slice());
    Some(islands[prefix..].iter().map(|island| island.owner).collect())
}

/// Trust (TG4): reuse this Session's immutable resolver environment only for
/// the exact complete ordered source/callee inventory. Extra macro islands
/// miss and use the existing fresh ordinary batch check.
/// Subsequent MIR/export users share that same checked snapshot. HIR model
/// checks, program admissions and per-body faithfulness checks remain separate.
/// A rejected or incomplete environment is `None`, never a partial success.
///
/// Trust (E9-DEFERRED-SUFFIX-ENV-1): the inventory is the PRE-ADMISSION prefix,
/// every island before the first that names `trust_import_*`
/// (`trust_certify::clean_island::pre_admission_island_count`): the islands
/// `trust_clean_mint::decide` mints from and `trust_check_clean_islands`
/// checks before the body walk. The deferred suffix names E6 program
/// admissions, which exist only in the session that minted them (the
/// verification walk's, or TG3's kernel-only lane's). A fresh session cannot
/// check it, so including it here rejected the environment of every crate with
/// a minted def and a deferred island, and `clean_origin_mir` stopped with its
/// internal error. Every minted declaration is in the prefix (the mint refuses
/// the suffix's), and the suffix only extends that environment, so the prefix
/// holds the same declaration terms. The suffix is still checked in every
/// build, by `trust_check_deferred_island_suffix`; nothing here accepts it.
pub(crate) fn clean_crate_environment(
    tcx: TyCtxt<'_>,
) -> Option<std::sync::Arc<trust_certify::clean_island::KernelEnvironment>> {
    use trust_certify::clean_island_environment::CheckedIslandEnvironment;
    let mut sources = collect_island_sources(tcx)?;
    sources.truncate(trust_certify::clean_island::pre_admission_island_count(sources.as_slice()));
    let callees = rust_callee_declarations(tcx);
    if let Some(hit) = tcx.sess.with_trust_compiler_state::<CheckedIslandEnvironment, _>(|state| {
        state.lookup(&sources, &callees)
    }) {
        return tcx.sess.time("trust_clean_environment_cache_hit", || hit);
    }
    // Trust (W5, Lean-calls-Rust): the SAME Rust callees the mint declared,
    // declared here the same way BEFORE `check_all` — read from the set the
    // mint carried through `ResolverGlobalCtxt`, never re-derived. A refusal
    // is a self-disagreement (the mint declared these on the same prelude)
    // and is reported as one rather than surfacing as a rejected batch.
    let (checked, _, _) = tcx
        .sess
        .time("trust_clean_environment_recheck", || {
            CheckedIslandEnvironment::check(&sources, &callees, false, clean_facts(tcx.sess))
        })
        .unwrap_or_else(|refusal| {
            tcx.dcx().fatal(format!(
                "internal: the Clean environment refused a Rust callee the mint declared for this \
             crate's islands ({refusal}). The mint and this session declare one set on one \
             prelude, so this is a compiler defect. Please report it."
            ));
        });
    let env = checked.lookup(&sources, &callees).expect("producer recorded its exact inputs");
    tcx.sess.with_trust_compiler_state::<CheckedIslandEnvironment, _>(|state| {
        *state = checked;
    });
    env
}

/// Trust (W5, Lean-calls-Rust): the `trust_types` carrier a transported
/// callee position denotes. `Nat` is unreachable for a callee — the mint
/// admits only the five machine carriers — and is refused rather than mapped.
fn trust_ty_of_carrier(tcx: TyCtxt<'_>, carrier: TrustCleanCarrier, span: Span) -> trust_types::Ty {
    match carrier {
        TrustCleanCarrier::Bool => trust_types::Ty::Bool,
        TrustCleanCarrier::U8 => trust_types::Ty::u8(),
        TrustCleanCarrier::U16 => trust_types::Ty::u16(),
        TrustCleanCarrier::U32 => trust_types::Ty::u32(),
        TrustCleanCarrier::U64 => trust_types::Ty::u64(),
        TrustCleanCarrier::Nat => tcx.dcx().span_fatal(
            span,
            "internal: a Rust callee admitted for Clean islands carries `Nat`, which the mint \
             is required to refuse. Please report it.",
        ),
    }
}

/// Trust (W5): the crate's admitted Rust callees in the environment helper's
/// spelling — THE ONE SET, from `ResolverGlobalCtxt::clean_rust_callees`.
pub(crate) fn rust_callee_declarations(
    tcx: TyCtxt<'_>,
) -> Vec<trust_certify::clean_island::RustCallee> {
    tcx.resolutions(())
        .clean_rust_callees
        .iter()
        .map(|callee| trust_certify::clean_island::RustCallee {
            clean_name: callee.clean_name.to_string(),
            params: callee
                .params
                .iter()
                .map(|&c| trust_ty_of_carrier(tcx, c, callee.span))
                .collect(),
            result: trust_ty_of_carrier(tcx, callee.result, callee.span),
        })
        .collect()
}

/// Trust (W5): the extractor's rendering of a callee `DefId` — EXACTLY the
/// string `trust_mir_extract` puts in `Terminator::Call::func` when it reads
/// the emitted call back, computed by the extractor's own renderer over the
/// same `Operand::function_handle` the materializer emits. Side B's identity
/// check compares this against what it read: two renderings of ONE `DefId`.
fn rust_callee_rendering<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId, span: Span) -> String {
    let handle = Operand::function_handle(tcx, def_id, &[], span);
    // Trust (GCKA-SELF-CALL-2, 2026-10-10): no caller. The handle carries no
    // generic argument, so the caller-dependent self-call reading never applies.
    trust_mir_extract::func_operand_name(tcx, None, &handle)
}

/// Trust (W5): the plan-side callee table for THIS session — the same set,
/// with each callee's `DefId` rendering filled in so a plan built over it can
/// be admitted. Order is the transported order, which is the mint's.
pub(crate) fn rust_callee_table(tcx: TyCtxt<'_>) -> Vec<trust_clean_origin::RustCalleeRef> {
    tcx.resolutions(())
        .clean_rust_callees
        .iter()
        .map(|callee| trust_clean_origin::RustCalleeRef {
            clean_name: callee.clean_name.to_string(),
            def_path: rust_callee_rendering(tcx, callee.def_id.to_def_id(), callee.span),
            params: callee
                .params
                .iter()
                .map(|&c| trust_ty_of_carrier(tcx, c, callee.span))
                .collect(),
            result: trust_ty_of_carrier(tcx, callee.result, callee.span),
        })
        .collect()
}

/// Trust (2026-09-14, PURITY GUARD) — is `def_id` a provably PURE Rust callee?
///
/// A Clean `def` treats every Rust callee it names as a PURE kernel value: the
/// faithfulness gate ([`trust_clean_origin::check_faithful`]) decides kernel
/// definitional equality against the declaration term, and the kernel is a PURE
/// calculus — `tick x` denotes ONE value however many times it is written. It
/// therefore CANNOT see that the emitted Rust callee is effectful (reads/writes
/// a `static`, an atomic, aliased memory). The lane is faithful ONLY when the
/// callee is a pure function of its arguments: for an effectful callee the
/// emitted binary's call COUNT / ORDER / SIDE EFFECTS diverge from the single
/// pure value the kernel checked — the confirmed `dup_let` / `dup_let2` /
/// `order_let` false verifies, all of which call an effectful `tick`. Per-shape
/// single-evaluation cannot close this: the unsoundness is the effectful callee,
/// not any one `let` shape.
///
/// This is a CONSERVATIVE, FAIL-CLOSED, transitive walk of the callee's MIR (and
/// every callee it reaches) — a body of this crate as its pre-steal elaborated MIR
/// (`trust_rust_purity_fact`), another crate's as its metadata MIR. A callee is
/// IMPURE (`false`) if its MIR — or any it
/// reaches — is unavailable/unanalyzable, or contains ANY of: a thread-local
/// reference; a raw-pointer creation (`&raw` — a `static mut` read,
/// `UnsafeCell::get`, an interior-mutability cell); a write through a
/// reference / pointer / `static` (an INDIRECT destination place); a memory-copy
/// intrinsic; inline asm; a `Drop` (destructor glue); an INDIRECT call (function
/// pointer / dyn dispatch); or a call to a callee that is not itself pure. Only a
/// body computing from its parameters/locals with arithmetic, moves and pure
/// calls is admitted. An atomic/volatile operation is a call to a `core`
/// intrinsic whose MIR is unavailable, so the transitive-call arm catches it.
///
/// Trust: an indirect read also needs a frame-local referent. Looking only for
/// `RawPtr` creation misses reads through compiler-created constant pointers to
/// a mutable static. This memory check does not establish panic freedom or
/// termination; verification-on charges those separate callee obligations.
///
/// A cycle's back-edge is assumed pure — any real impurity in the cycle is caught
/// when that body's own statements are walked, before the edge is taken — and the
/// depth cap fails closed on anything deeper than the walk analyzes.
thread_local! {
    /// Clean-origin defs whose faithfulness gate is CURRENTLY RUNNING on this thread.
    ///
    /// Trust (cross-language cycle, 2026-09-25): [`rust_callee_is_pure`] reads each
    /// callee's MIR and RECURSES through the callee's own calls; a Clean-origin
    /// callee's MIR is its gated emission. For `fn inc` -> `def twice_inc` -> `inc`,
    /// that recursion reaches `twice_inc` and demands its body while the very same
    /// query is in flight, so the query system reports a raw cycle (measured when the
    /// walk read `optimized_mir`):
    ///
    /// ```text
    /// error[E0391]: cycle detected when optimizing MIR for `twice_inc`
    /// note: ...which requires optimizing MIR for `inc`...
    /// note: ...which again requires optimizing MIR for `twice_inc`, completing the cycle
    /// ```
    ///
    /// Measured at BOTH `-Ztrust-verify=off` and `=on` before this guard existed. That
    /// diagnostic names no cross-language cause and offers the author no option, while
    /// every other unemittable shape in this lane gets a designed refusal.
    ///
    /// THE CHECK IS AT THE DEMAND SITE, and that is the whole reason it works. A
    /// re-entry guard at the top of [`clean_origin_mir`] was measured and never fires:
    /// the query system raises E0391 BEFORE control reaches the function body. Refusing
    /// before the demand needs no such re-entry.
    ///
    /// The set is keyed on the def being GATED, so it fires only on a genuine cycle
    /// back into that def. Acyclic nesting — `def a := f x` where `fn f` calls a
    /// DIFFERENT `def b` — never re-enters one def and is untouched.
    ///
    /// Membership alone is only half the test; see
    /// [`callee_reaches_a_gate_on_this_stack`] for the referenced-gate edge, which is
    /// the one the `-Ztrust-verify=on` demand order needs.
    static CLEAN_ORIGIN_GATE_IN_PROGRESS: std::cell::RefCell<
        rustc_data_structures::fx::FxHashSet<LocalDefId>,
    > = std::cell::RefCell::new(rustc_data_structures::fx::FxHashSet::default());

    /// Set when [`rust_callee_is_pure`] declined because of a cross-language cycle
    /// rather than an effect, so the caller can say which. The purity refusal text
    /// blames global or aliased mutable state, which is false of a cycle and would
    /// send the author hunting an effect that does not exist.
    static CLEAN_ORIGIN_CYCLE_SEEN: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Removes `def` from the in-progress set however the gate leaves, including the
/// diverging `refuse` path.
struct CleanOriginGateFrame(LocalDefId);

impl Drop for CleanOriginGateFrame {
    fn drop(&mut self) {
        CLEAN_ORIGIN_GATE_IN_PROGRESS.with(|set| set.borrow_mut().remove(&self.0));
    }
}

/// Would demanding this callee's MIR close a cross-language cycle — i.e. does the
/// callee REACH a Clean-origin gate that is on this thread's stack right now?
///
/// The question has to be answered TRANSITIVELY, and before the demand. Three
/// measured facts force that shape; each was a shipped guard that did not hold.
///
///  * **The direct edge is not enough.** The purity walk steps `def twice_inc` ->
///    `fn inc`, and `inc` is not itself gated — the cycle is `inc`'s own call back
///    to `twice_inc`. So the callee's REFERENCES must be consulted, not just its
///    identity.
///  * **One hop is not enough either, and only one lane shows it.** With
///    `fn hop -> fn deep -> def twice_h -> hop`, the reference lives two hops out.
///    At `-Ztrust-verify=off` the purity walk's own recursion reaches `deep` and a
///    one-hop test fires there in time. At `-Ztrust-verify=on` it never gets the
///    chance: demanding `optimized_mir(hop)` runs hop's verification, which bundles
///    its callees and demands `optimized_mir(twice_h)` — the query already on the
///    stack — so E0391 lands inside the FIRST demand. Measured 2026-09-25, both
///    lanes, which is why a guard tested in one lane is not a guard.
///  * **The walk may not use `optimized_mir`.** That is the demand being guarded;
///    using it to decide would be the cycle. The two queries below are the cheap
///    pre-steal levels: `trust_clean_origin_references` reads `mir_built`, and
///    `trust_mir_direct_local_callees` reads elaborated MIR. Both are disk-cached,
///    and the purity walk that follows reads `trust_rust_purity_fact`, the same
///    pre-steal level, over this very subgraph, so nothing here is a new class of
///    cost.
///
/// TWO EXCLUSIONS ARE LOAD-BEARING, not tidiness. Neither node is expanded:
///
///  * **A Clean-origin def.** It is a synthetic HIR owner; forcing its `mir_built`
///    dead-ends in `typeck`'s `can't type-check body of DefId(..)` `span_bug!`. An
///    earlier attempt asked unconditionally and ICEd legal acyclic nesting
///    (`def a := f x` with a second `def b` calling `a`) — the measurement that
///    reverted it. Reaching such a node still ANSWERS the question (`gates` is
///    consulted first), so nothing is lost by not expanding it.
///  * **A body with no `optimized_mir`** — a `#[rustc_comptime]` fn or any body
///    whose `hir_body_const_context` is outside `None | Some(ConstFn)`.
///    `inner_mir_for_ctfe` STEALS such a body's elaborated MIR, so
///    `trust_mir_direct_local_callees` would borrow a consumed `Steal`. Its own
///    doc comment states this precondition and forbids "hardening" it with
///    `is_stolen()`; the caller applies the filter, exactly as the SCC builder in
///    `trust_verify` does.
///
/// A node that fails a filter is not expanded, so a cycle closing ONLY through a
/// const-context body is not caught here and still surfaces as E0391. That is a
/// bounded, disclosed hole, not a claim of completeness.
///
/// The empty-set short circuit keeps all of this free outside a gate: no gate on
/// the stack, no query, no walk.
fn callee_reaches_a_gate_on_this_stack(tcx: TyCtxt<'_>, callee: LocalDefId) -> bool {
    let gates: rustc_data_structures::fx::FxHashSet<LocalDefId> =
        CLEAN_ORIGIN_GATE_IN_PROGRESS.with(|gates| gates.borrow().clone());
    if gates.is_empty() {
        return false;
    }
    callee_reaches_any(tcx, callee, &gates)
}

/// The walk of [`callee_reaches_a_gate_on_this_stack`] for an explicit set of Clean-origin
/// `gates` (plan step 3.5: F1's backstop asks it about the one def whose callee it judges, with
/// no gate on the stack). Same queries, same two load-bearing exclusions.
fn callee_reaches_any(
    tcx: TyCtxt<'_>,
    callee: LocalDefId,
    gates: &rustc_data_structures::fx::FxHashSet<LocalDefId>,
) -> bool {
    let mut seen = rustc_data_structures::fx::FxHashSet::default();
    let mut worklist = vec![callee];
    while let Some(node) = worklist.pop() {
        if !seen.insert(node) {
            continue;
        }
        // Reaching a live gate answers the question whatever kind of body it is —
        // asked BEFORE either filter, so an unexpandable node still decides.
        if gates.contains(&node) {
            return true;
        }
        if !node_is_safe_to_expand(tcx, node) {
            continue;
        }
        if tcx
            .trust_clean_origin_references(node)
            .iter()
            .any(|referenced| gates.contains(referenced))
        {
            return true;
        }
        worklist.extend(tcx.trust_mir_direct_local_callees(node).iter().copied());
    }
    false
}

/// The node filter [`callee_reaches_a_gate_on_this_stack`] applies before reading a
/// body's pre-steal MIR. See the two exclusions documented there — this mirrors the
/// filter `trust_verify`'s SCC builder applies to the same adjacency query.
fn node_is_safe_to_expand(tcx: TyCtxt<'_>, node: LocalDefId) -> bool {
    use rustc_hir::def::DefKind;
    matches!(tcx.def_kind(node), DefKind::Fn | DefKind::AssocFn | DefKind::Closure)
        && matches!(tcx.hir_body_const_context(node), None | Some(rustc_hir::ConstContext::ConstFn))
        && !is_clean_origin(tcx, node)
}

fn rust_callee_is_pure(
    tcx: TyCtxt<'_>,
    def_id: DefId,
    visited: &mut std::collections::HashSet<DefId>,
    depth: usize,
) -> bool {
    rust_callee_is_pure_walk(tcx, def_id, visited, depth, None)
}

/// Trust (plan step 3.5): what F1's backstop walk knows that the MIR lane's walk learns from its
/// gate stack. On the MIR lane a Clean-origin def the walk reaches is read by building its
/// `clean_origin_mir` body, whose own gate walks that def's Rust callees with the outer gate
/// still on the stack, which is how a cycle through several defs is seen. F1 builds no such body
/// (design §5.7), so the backstop is told each `RustCallChain` def's resolved Rust callees (the
/// F1 recorder's plans) and the def it judges for.
pub(crate) struct CleanOriginBackstop<'a> {
    /// The Clean-origin def whose Rust callee is judged: reaching it again is a
    /// cross-language cycle.
    pub origin: LocalDefId,
    /// Each `RustCallChain` def's resolved Rust callees, by def.
    pub rust_callees: &'a rustc_data_structures::fx::FxHashMap<LocalDefId, Vec<DefId>>,
    /// Set when the walk refused because of a cross-language cycle, not an effect.
    pub cycle: std::cell::Cell<bool>,
}

/// Trust (plan step 3.5; docs/DECISION_QUEUE.md STEP3.5-PURITY-UNDECIDED): the MIR walk as F1's
/// REFUSAL-ONLY backstop, for a Rust callee whose conserved trust-ir effect census cannot decide
/// its purity (`clean_origin_ir::check_rust_callees_on_f1`). It is [`rust_callee_is_pure`] with
/// two differences, both from the absence of a `clean_origin_mir` body on F1 (design §5.7): a
/// Clean-origin def it reaches is NOT read but walked through its plan's Rust callees
/// ([`CleanOriginBackstop`]), and the cross-language cycle is asked about `backstop.origin`
/// (the MIR lane asks about the gates on its stack, of which there are none here). A cycle sets
/// `backstop.cycle`. `false` refuses; `true` decides nothing (the census's UNDECIDED stands).
pub(crate) fn rust_callee_is_pure_backstop(
    tcx: TyCtxt<'_>,
    def_id: DefId,
    visited: &mut std::collections::HashSet<DefId>,
    backstop: &CleanOriginBackstop<'_>,
) -> bool {
    rust_callee_is_pure_walk(tcx, def_id, visited, 0, Some(backstop))
}

fn rust_callee_is_pure_walk(
    tcx: TyCtxt<'_>,
    def_id: DefId,
    visited: &mut std::collections::HashSet<DefId>,
    depth: usize,
    backstop: Option<&CleanOriginBackstop<'_>>,
) -> bool {
    const MAX_PURITY_DEPTH: usize = 64;
    if depth > MAX_PURITY_DEPTH {
        return false;
    }
    if !visited.insert(def_id) {
        // Already on THIS walk — a cycle back-edge. Sound to assume pure: the
        // body's own statements are (or were) walked before this edge is taken.
        return true;
    }
    if let Some(backstop) = backstop
        && let Some(local) = def_id.as_local()
        && is_clean_origin(tcx, local)
    {
        if local == backstop.origin {
            backstop.cycle.set(true);
            return false;
        }
        // Another Clean-origin def: its body is never read; its Rust callees are walked, as its
        // own gate would walk them on the MIR lane. A def with none (every other shape) calls
        // no Rust code.
        let callees = backstop.rust_callees.get(&local).map(Vec::as_slice).unwrap_or(&[]);
        return callees.iter().all(|&callee| {
            rust_callee_is_pure_walk(tcx, callee, visited, depth + 1, Some(backstop))
        });
    }
    // Trust: `trust_local_def_has_mir` for a local def — `is_mir_available` reads
    // `mir_keys`, which demands every async closure's by-move body, i.e. `mir_built` of
    // bodies this walk may be running inside of.
    let has_mir = match def_id.as_local() {
        Some(local) => tcx.trust_local_def_has_mir(local),
        None => tcx.is_mir_available(def_id),
    };
    if !has_mir {
        // No body to inspect: a foreign fn, an intrinsic (atomics land here), a
        // fn with no exported MIR. Fail closed.
        return false;
    }
    // Trust (cross-language cycle): refuse BEFORE reading the callee, because a callee
    // that leads back to a def whose own gate is on this stack has no value the kernel
    // could have checked, and reading it would re-enter that gate.
    if def_id.as_local().is_some_and(|local| callee_reaches_a_gate_on_this_stack(tcx, local)) {
        CLEAN_ORIGIN_CYCLE_SEEN.with(|flag| flag.set(true));
        return false;
    }
    // Trust (plan step 3.5): F1's backstop has no gate on the stack; it asks the same question
    // about the def it judges for, before reading the callee, as the MIR lane does.
    if let Some(backstop) = backstop
        && let Some(local) = def_id.as_local()
        && callee_reaches_any(
            tcx,
            local,
            &std::iter::once(backstop.origin).collect::<rustc_data_structures::fx::FxHashSet<_>>(),
        )
    {
        backstop.cycle.set(true);
        return false;
    }
    // Trust: a local body is read through `trust_rust_purity_fact`, a fact of its
    // PRE-STEAL elaborated MIR, never through `optimized_mir`: this walk runs inside
    // `mir_for_ctfe` (const evaluation, which the type system reaches), and a local
    // `optimized_mir` runs that body's whole pipeline — verification, its callee
    // bundling and the crate call-graph oracles, which read every fn's MIR — from inside
    // type computation (E0391). A foreign body's MIR is decoded from metadata.
    let foreign;
    let fact = match def_id.as_local() {
        Some(local) => tcx.trust_rust_purity_fact(local),
        None => {
            foreign = purity_fact_of_body(tcx, tcx.optimized_mir(def_id));
            &foreign
        }
    };
    for &callee in &fact.callees {
        if !rust_callee_is_pure_walk(tcx, callee, visited, depth + 1, backstop) {
            return false;
        }
    }
    !fact.impure
}

/// Provider of `trust_rust_purity_fact`: [`purity_fact_of_body`] over the def's
/// pre-steal elaborated MIR. A Clean-origin def's elaborated MIR is its gated emission
/// (`mir_drops_elaborated_and_const_checked`), read here as `optimized_mir` itself
/// returns it, unoptimized; a constructor has no elaborated MIR, only its shim.
pub(crate) fn rust_purity_fact(tcx: TyCtxt<'_>, def: LocalDefId) -> TrustPurityFact {
    if is_clean_origin(tcx, def) {
        return purity_fact_of_body(tcx, tcx.optimized_mir(def));
    }
    if tcx.is_constructor(def.to_def_id()) {
        return purity_fact_of_body(tcx, tcx.mir_for_ctfe(def));
    }
    purity_fact_of_body(tcx, &tcx.mir_drops_elaborated_and_const_checked(def).borrow())
}

/// Whether `inner_optimized_mir` must produce `trust_rust_purity_fact` before it steals
/// a body: only a crate with a Clean-origin def runs the purity guard, and the guard
/// walks only this crate's bodies (another crate's are decoded from metadata).
pub(crate) fn crate_needs_purity_facts(tcx: TyCtxt<'_>) -> bool {
    !tcx.resolutions(()).clean_origin_defs.is_empty()
}

/// The purity guard's reading of one body, in the order it walks it: the frame-read
/// check first, then each block's statements and terminator. The first refused element
/// ends the fact with `impure`; the calls before it are the callees the walk recurses
/// into, in order, so a callee met earlier is walked before the refusal is reached.
fn purity_fact_of_body<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> TrustPurityFact {
    let mut fact = TrustPurityFact::default();
    if !rust_callee_reads_frame_only(body) {
        fact.impure = true;
        return fact;
    }
    let def_id = body.source.def_id();
    for bb in body.basic_blocks.iter() {
        for stmt in &bb.statements {
            let refused = match &stmt.kind {
                StatementKind::Assign(boxed) => {
                    let (place, rvalue) = &**boxed;
                    // A write through a reference / raw pointer / `static` reaches
                    // memory outside the callee's own frame; a thread-local read or a
                    // raw-pointer creation (`&raw`: `static mut`, `UnsafeCell::get`,
                    // interior mutability) reaches shared state.
                    place.is_indirect()
                        || matches!(rvalue, Rvalue::ThreadLocalRef(_) | Rvalue::RawPtr(..))
                }
                // `Assume` is pure; a memory copy (`CopyNonOverlapping`) writes
                // through a pointer. Fail closed on anything but `Assume`.
                StatementKind::Intrinsic(boxed) => {
                    !matches!(&**boxed, rustc_middle::mir::NonDivergingIntrinsic::Assume(_))
                }
                _ => false,
            };
            if refused {
                fact.impure = true;
                return fact;
            }
        }
        match &bb.terminator().kind {
            TerminatorKind::Call { func, .. } | TerminatorKind::TailCall { func, .. } => {
                // Trust (purity guard, trait-dispatch hole — 2026-09-15):
                // `const_fn_def` names the TRAIT ITEM for a trait-method call, and the
                // MIR of a trait item is its DEFAULT body — NOT the impl that will
                // actually run. Walking the default laundered an impure impl behind a
                // pure default (measured: `impl Tick for Impure { fn tick(_) { COUNTER
                // .fetch_add(..) } }` reached through a pure default was admitted, and
                // `let y := tick x; sub2 y y` then emitted TWO `tick` calls for a term
                // the kernel denotes with ONE — `sub2 1 2 = u64::MAX` where the
                // denotation is `0`), and it falsely REFUSED a pure impl behind an
                // impure default.
                //
                // Resolve to the concrete instance and walk THAT body. Only
                // `InstanceKind::Item` is a real fn item with inspectable MIR; every
                // other kind (virtual dispatch, reify/clone/drop shims, intrinsics) and
                // every unresolvable — still-generic or ambiguous — edge FAILS CLOSED,
                // because a callee whose body this walk cannot see cannot be shown pure.
                // A function-pointer or dyn call names no static callee at all.
                let resolved = func.const_fn_def().and_then(|(callee, args)| {
                    let typing_env = rustc_middle::ty::TypingEnv::post_analysis(tcx, def_id);
                    match rustc_middle::ty::Instance::try_resolve(tcx, typing_env, callee, args) {
                        Ok(Some(rustc_middle::ty::Instance {
                            def: rustc_middle::ty::InstanceKind::Item(resolved),
                            ..
                        })) => Some(resolved),
                        _ => None,
                    }
                });
                match resolved {
                    Some(resolved) => fact.callees.push(resolved),
                    None => {
                        fact.impure = true;
                        return fact;
                    }
                }
            }
            TerminatorKind::InlineAsm { .. } | TerminatorKind::Drop { .. } => {
                fact.impure = true;
                return fact;
            }
            _ => {}
        }
    }
    fact
}

// Trust: track only references whose complete assignment history proves a
// referent inside this invocation's frame. Arguments, constants, call results,
// casts, projected pointer loads and multiply-assigned locals remain unknown.
// This is an observation used by the conservative purity guard, not an alias,
// lifetime, panic-freedom or source-refinement certificate.
#[derive(Clone, Copy)]
enum FrameReferenceOrigin {
    Unknown,
    Frame,
    Copy(Local),
}

fn rust_callee_reads_frame_only(body: &Body<'_>) -> bool {
    let mut origins = IndexVec::from_elem_n(FrameReferenceOrigin::Unknown, body.local_decls.len());
    let mut assigned = IndexVec::from_elem_n(false, body.local_decls.len());
    for argument in body.args_iter() {
        assigned[argument] = true;
    }
    let mut record = |local, origin| {
        origins[local] = if assigned[local] { FrameReferenceOrigin::Unknown } else { origin };
        assigned[local] = true;
    };
    for block in body.basic_blocks.iter() {
        for statement in &block.statements {
            if let StatementKind::Assign(assignment) = &statement.kind {
                let (destination, value) = &**assignment;
                if destination.projection.is_empty() {
                    let origin = match value {
                        Rvalue::Ref(_, _, place)
                            if place.projection.is_empty()
                                || !place
                                    .projection
                                    .iter()
                                    .any(|elem| matches!(elem, ProjectionElem::Deref)) =>
                        {
                            FrameReferenceOrigin::Frame
                        }
                        Rvalue::Ref(_, _, place)
                            if place
                                .projection
                                .iter()
                                .filter(|elem| matches!(elem, ProjectionElem::Deref))
                                .count()
                                == 1 =>
                        {
                            FrameReferenceOrigin::Copy(place.local)
                        }
                        Rvalue::Use(Operand::Copy(place) | Operand::Move(place), _)
                            if place.projection.is_empty() =>
                        {
                            FrameReferenceOrigin::Copy(place.local)
                        }
                        _ => FrameReferenceOrigin::Unknown,
                    };
                    record(destination.local, origin);
                }
            }
        }
        if let TerminatorKind::Call { destination, .. } = &block.terminator().kind
            && destination.projection.is_empty()
        {
            record(destination.local, FrameReferenceOrigin::Unknown);
        }
    }

    // Resolve single-definition copy chains once. A cycle cannot manufacture a
    // frame origin; cache every visited local even on that refusal path.
    let mut frame = IndexVec::from_elem_n(None, body.local_decls.len());
    for start in body.local_decls.indices() {
        let mut path = Vec::new();
        let mut visited = std::collections::HashSet::new();
        let mut local = start;
        let resolved = loop {
            if let Some(known) = frame[local] {
                break known;
            }
            if !visited.insert(local) {
                break false;
            }
            path.push(local);
            match origins[local] {
                FrameReferenceOrigin::Unknown => break false,
                FrameReferenceOrigin::Frame => break true,
                FrameReferenceOrigin::Copy(source) => local = source,
            }
        };
        for local in path {
            frame[local] = Some(resolved);
        }
    }

    struct FrameReads<'a> {
        frame: &'a IndexVec<Local, Option<bool>>,
        frame_only: bool,
    }
    impl<'tcx> Visitor<'tcx> for FrameReads<'_> {
        fn visit_place(&mut self, place: &Place<'tcx>, context: PlaceContext, location: Location) {
            if context.is_use() {
                let dereferences = place
                    .projection
                    .iter()
                    .filter(|elem| matches!(elem, ProjectionElem::Deref))
                    .count();
                // A Call destination (or another indirect mutation) could
                // overwrite a reference through a frame alias without an
                // Assign to the reference local. Borrowing is not a write;
                // every actual indirect mutation remains refused.
                let writes_through_reference = context.is_mutating_use() && !context.is_borrow();
                if dereferences != 0
                    && (writes_through_reference
                        || dereferences != 1
                        || self.frame[place.local] != Some(true))
                {
                    self.frame_only = false;
                }
            }
            self.super_place(place, context, location);
        }
    }
    let mut reads = FrameReads { frame: &frame, frame_only: true };
    reads.visit_body(body);
    reads.frame_only
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
    let Some(env) = clean_crate_environment(tcx) else {
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
    let env = &*env;
    let decl = CleanOriginDecl { name: &name, env, span };
    // Trust (cross-language cycle): mark this def as being gated for the duration, so
    // the purity walk below refuses a callee that leads back here instead of demanding
    // its `optimized_mir` and tripping the query system's own cycle detector.
    CLEAN_ORIGIN_GATE_IN_PROGRESS.with(|set| set.borrow_mut().insert(def));
    let _gate_frame = CleanOriginGateFrame(def);
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
    // Trust (W5): planned over the SAME callee table the mint planned over
    // (plus the `DefId` renderings only this session can supply).
    let declaration = clean_source_name(tcx, decl.name, decl.span);
    let plan = match trust_clean_origin::plan_clean_origin_body_with_rust_callees_for_name(
        decl.env,
        &declaration,
        &rust_callee_table(tcx),
    ) {
        Ok(plan) => plan,
        Err(refusal) => refuse(tcx, decl, &refusal),
    };

    // ── the PURITY GUARD (Trust, 2026-09-14) ───────────────────────────────
    //
    // The faithfulness gate below is kernel definitional equality against the
    // declaration term, and the kernel is a PURE calculus — it treats a Rust
    // callee as a pure value, so it cannot see that the emitted callee is
    // effectful. A `RustCallChain` over an IMPURE callee is therefore a WRONG
    // BINARY the gate cannot catch: the emitted call count / order / side effects
    // diverge from the single pure value the kernel checked (the `dup_let` /
    // `dup_let2` / `order_let` false verifies, all calling an effectful `tick`).
    // This is the ROOT closure — per-shape single-evaluation cannot cover every
    // effectful shape, so it is refused here, at the one point that has the
    // callee's MIR. A PURE (arithmetic-only) callee is admitted unchanged, so a
    // pure duplicated call is still faithful and r18/r21/r22/r23 stay green.
    //
    // Trust (W5 increment 7, 2026-09-16): a `let`-bound Rust call is now
    // emitted as ONE value temporary (one `RustCallChain` node read any number
    // of times), so the emitted count and order match Lean's strict `let`. That
    // does not retire this guard — it is what makes the kernel's extensional
    // callee model TRUE OF THE BINARY: for an effectful `tick`, the once-body
    // and `sub2 (tick x) (tick x)` are still def-eq while this lane emits one
    // call for the first and two for the second. The guard walks EVERY node of
    // the plan, so a let-bound effectful callee is refused whether its binder is
    // used 0, 1 or n times (`clean_origin_let_rust_call_unused_effectful_refused.rs`).
    if let trust_clean_origin::CleanOriginShape::RustCallChain { nodes } = plan.shape() {
        let callee_defs: std::collections::BTreeMap<String, DefId> = tcx
            .resolutions(())
            .clean_rust_callees
            .iter()
            .map(|c| {
                (rust_callee_rendering(tcx, c.def_id.to_def_id(), c.span), c.def_id.to_def_id())
            })
            .collect();
        for node in nodes {
            let callee = &plan.callees()[node.callee];
            let Some(&callee_def) = callee_defs.get(&callee.def_path) else {
                refuse(
                    tcx,
                    decl,
                    &EmitRefusal::NotEmittable {
                        name: decl.name.to_owned(),
                        reason: format!(
                            "internal: its Rust callee `{}` has no resolvable `DefId` for the \
                             purity check; the plan's callee table and the resolver disagree. \
                             Please report it.",
                            callee.clean_name
                        ),
                    },
                )
            };
            let mut visited = std::collections::HashSet::new();
            CLEAN_ORIGIN_CYCLE_SEEN.with(|flag| flag.set(false));
            let callee_pure = rust_callee_is_pure(tcx, callee_def, &mut visited, 0);
            if !callee_pure && CLEAN_ORIGIN_CYCLE_SEEN.with(|flag| flag.get()) {
                // A CYCLE, not an effect. The purity text below blames global or
                // aliased mutable state, which is false here and would send the author
                // hunting something that does not exist.
                refuse(
                    tcx,
                    decl,
                    &EmitRefusal::NotEmittable {
                        name: decl.name.to_owned(),
                        reason: format!(
                            "a Clean `def` may not take part in a CROSS-LANGUAGE CYCLE, but \
                             `{}` calls Rust `fn {}`, which leads back to `{}`. The \
                             faithfulness gate models a Rust callee as a pure value the \
                             kernel already checked; a callee whose own body depends on this \
                             declaration has no such value, and the emitted body would have \
                             to be gated against itself. options: give the Rust side a base \
                             case that does not call back into `{}`; or move the recursion \
                             wholly into Clean, where it is checked as a well-founded \
                             definition; or compute the recursive part in Rust and pass its \
                             result into the `def` as an argument.",
                            decl.name, callee.clean_name, decl.name, decl.name
                        ),
                    },
                );
            }
            if !callee_pure {
                refuse(
                    tcx,
                    decl,
                    &EmitRefusal::NotEmittable {
                        name: decl.name.to_owned(),
                        reason: format!(
                            "a Clean `def` may only call a PURE Rust fn, but `{}` is not \
                             provably pure — it (or something it calls) accesses global or \
                             aliased mutable state (a `static`, an atomic, a raw pointer, \
                             interior mutability) or is otherwise unanalyzable. The \
                             faithfulness gate treats a Rust callee as a pure value the kernel \
                             checked, so it cannot model those effects, and duplicating or \
                             reordering the call would change behaviour. options: make `{}` a \
                             pure function of its arguments; or compute the effectful value in \
                             Rust and pass it into the Clean `def` as an argument.",
                            callee.clean_name, callee.clean_name
                        ),
                    },
                );
            }
        }
    }

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

/// Trust (plan step 3.5): [`check_signature_agrees`] for the F1 recorder, which builds no MIR
/// body and so never reaches [`build_gated_body`]: the fed `fn_sig` every Rust call was
/// type-checked against must be the one the plan's carriers denote. Fatal on any disagreement.
pub(crate) fn check_fed_signature(
    tcx: TyCtxt<'_>,
    def: LocalDefId,
    plan: &CleanOriginPlan,
    name: &str,
    env: &clean_kernel::Environment,
    span: Span,
) {
    check_signature_agrees(tcx, def, plan, &CleanOriginDecl { name, env, span });
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
    tcx.dcx().struct_span_fatal(decl.span, headline).with_note(refusal.note()).emit_fatal()
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
    // Trust (W5 increment 7): the let-temp mutation — DUPLICATE the evaluation
    // of a let-bound Rust call. A `let y := dbl x; sub2 y y` body is emitted as
    // ONE `Call(dbl)` into a temporary read twice; the divergence this lane
    // exists to refuse is the same call emitted TWICE (what zeta-substitution
    // would have produced). The kernel cannot see it (`sub2 (dbl x) (dbl x)` and
    // the once-body are def-eq), so the refusal must come from the structural
    // node-for-node comparison — `clean_origin_let_rust_call_divergence_fails_build.rs`
    // observes it from the driver. Fires only when a temporary is read twice by
    // one `Call`; the arms below are untouched for every other body, and this
    // arm returns early so the fixture pins the duplication alone. The
    // duplicate is INSERTED right after the writer (index order stays
    // execution order): appended at the end, side B's "last block is `Return`"
    // rule would refuse it as unrecognised before the node COUNT was ever
    // compared, and the fixture would be green for the wrong reason. Generic
    // over any `Call` reading one bare non-parameter local twice; no other
    // Clean-origin template emits such a `Call` today.
    let twice_read = body.basic_blocks.iter_enumerated().find_map(|(bb, data)| {
        let term = data.terminator.as_ref()?;
        let TerminatorKind::Call { args, .. } = &term.kind else { return None };
        let mut seen: Vec<Local> = Vec::new();
        for (i, arg) in args.iter().enumerate() {
            if let Operand::Copy(place) | Operand::Move(place) = &arg.node
                && place.projection.is_empty()
                && place.local.as_usize() > arg_count
            {
                if seen.contains(&place.local) {
                    return Some((bb, i, place.local));
                }
                seen.push(place.local);
            }
        }
        None
    });
    if let Some((reader_bb, second_arg, temp)) = twice_read {
        let writer_bb = body.basic_blocks.iter_enumerated().find_map(|(bb, data)| {
            let term = data.terminator.as_ref()?;
            match &term.kind {
                TerminatorKind::Call { destination, target: Some(_), .. }
                    if destination.local == temp && destination.projection.is_empty() =>
                {
                    Some(bb)
                }
                _ => None,
            }
        });
        if let Some(writer_bb) = writer_bb {
            let decl = &body.local_decls[temp];
            let fresh = body
                .local_decls
                .push(rustc_middle::mir::LocalDecl::new(decl.ty, decl.source_info.span));
            let mut duplicate = body.basic_blocks[writer_bb].terminator().clone();
            let TerminatorKind::Call { destination, target, .. } = &mut duplicate.kind else {
                unreachable!("found above as a Call")
            };
            *destination = Place::from(fresh);
            // The duplicate goes at writer+1 and keeps the writer's old
            // successor (renumbered below); every successor at or past that
            // index shifts by one; then the writer flows into the duplicate.
            // Evaluation order: original, duplicate, reader.
            let dup_bb = rustc_middle::mir::BasicBlock::from_usize(writer_bb.as_usize() + 1);
            let shift = |s: &mut rustc_middle::mir::BasicBlock| {
                if *s >= dup_bb {
                    *s = rustc_middle::mir::BasicBlock::from_usize(s.as_usize() + 1);
                }
            };
            duplicate.successors_mut(shift);
            for data in body.basic_blocks_mut().iter_mut() {
                if let Some(term) = &mut data.terminator {
                    term.successors_mut(shift);
                }
            }
            body.basic_blocks_mut().raw.insert(
                dup_bb.as_usize(),
                rustc_middle::mir::BasicBlockData::new(Some(duplicate), false),
            );
            let reader_bb = if reader_bb >= dup_bb {
                rustc_middle::mir::BasicBlock::from_usize(reader_bb.as_usize() + 1)
            } else {
                reader_bb
            };
            if let TerminatorKind::Call { target, .. } =
                &mut body.basic_blocks_mut()[writer_bb].terminator_mut().kind
            {
                *target = Some(dup_bb);
            }
            if let TerminatorKind::Call { args, .. } =
                &mut body.basic_blocks_mut()[reader_bb].terminator_mut().kind
            {
                args[second_arg].node = Operand::Copy(Place::from(fresh));
            }
            return;
        }
    }
    for block in body.basic_blocks_mut() {
        // Trust (W5): the Rust-call chain mutation — swap the two arguments of
        // a two-argument `Call`, so `sub2 a b` is emitted as `sub2 b a`. The
        // kernel separates the two applications by congruence on the stuck
        // callee (`control_23::half_2` measures it), and
        // `clean_origin_rust_call_divergence_fails_build.rs` observes the
        // refusal from the driver. Stated rather than hidden: this arm also
        // perturbs a two-argument wrapping-binop body, which no fixture points
        // the knob at.
        if let Some(terminator) = &mut block.terminator
            && let TerminatorKind::Call { args, .. } = &mut terminator.kind
            && args.len() == 2
        {
            args.swap(0, 1);
        }
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
                // Trust (W5): a Rust-call chain temporary, at ITS callee's
                // result carrier — the plan's table is the decision, and the
                // same `carrier_to_rustc_ty` mapping every other position uses.
                TemplateTy::RustCalleeResult { index } => match plan.callees().get(index) {
                    Some(callee) => carrier_to_rustc_ty(tcx, &callee.result, span),
                    None => tcx.dcx().span_fatal(
                        span,
                        "internal: a Rust-call chain template names a callee outside the plan's \
                         table. Please report it.",
                    ),
                },
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
            // Trust (W5): a numeral argument to a Rust callee, at the width of
            // the callee PARAMETER's carrier (re-checked on the sealed plan).
            // Side B reads the encoded width back and the kernel decides
            // whether the callee accepts a literal there.
            TemplateOperand::UIntScalar { value, width } => {
                let ty = match width {
                    8 => tcx.types.u8,
                    16 => tcx.types.u16,
                    32 => tcx.types.u32,
                    64 => tcx.types.u64,
                    other => tcx.dcx().span_fatal(
                        span,
                        format!(
                            "internal: a Rust-call chain literal reached the emitter at width \
                             {other}, which the sealed plan is required to refuse. Please \
                             report it."
                        ),
                    ),
                };
                Operand::const_from_scalar(
                    tcx,
                    ty,
                    Scalar::from_uint(value, Size::from_bits(u64::from(width))),
                    span,
                )
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
                        // result carrier — `&`, `|`, `/`, `%`, and since
                        // 2026-09-23 `^` and `>>` (no `<<`: see the `HShiftLeft`
                        // demand in `trust_clean_origin::table`). A NEW
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
                        // and for the same reason: a new operator must be a
                        // compile error here rather than a fall-through into
                        // the wrong instruction (`^` and `>>` paid it on
                        // 2026-09-23). Side B reads the emitted body back
                        // through `RawBinOpKind::from_mir_binop`, whose match
                        // is closed over the same values — so a new
                        // variant breaks BOTH directions at once, which is the
                        // property that keeps them from drifting.
                        TemplateRvalue::RawBin { op, left, right } => Rvalue::BinaryOp(
                            match op {
                                RawBinOpKind::BitAnd => BinOp::BitAnd,
                                RawBinOpKind::BitOr => BinOp::BitOr,
                                RawBinOpKind::BitXor => BinOp::BitXor,
                                RawBinOpKind::Div => BinOp::Div,
                                RawBinOpKind::Rem => BinOp::Rem,
                                // `Shr`, never `ShrUnchecked`: MIR's `Shr`
                                // takes the amount as `RHS.rem_euclid(LHS::BITS)`
                                // — Lean's own modulo-the-width reduction — so
                                // it has no overflow case and needs no
                                // `Assert`. The planner only emits a numeral
                                // amount below the width anyway, because that
                                // is all side B can reflect.
                                RawBinOpKind::Shr => BinOp::Shr,
                            },
                            Box::new((operand(left), operand(right))),
                        ),
                        TemplateRvalue::SharedRef(of) => Rvalue::Ref(
                            tcx.lifetimes.re_erased,
                            BorrowKind::Shared,
                            Place::from(Local::from_usize(of)),
                        ),
                        // W6 (Rust-calls-Clean): boolean negation. `UnOp::Not`
                        // on a `bool` operand is logical negation, exactly what
                        // `rustc_mir_build` emits for `!b`.
                        TemplateRvalue::BoolNot(value) => {
                            Rvalue::UnaryOp(UnOp::Not, operand(value))
                        }
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
                TemplateTerminator::Goto(target) => TerminatorKind::Goto {
                    target: BasicBlock::from_usize(*target),
                    loop_hint_attrs: Default::default(),
                },
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
                            resolve_template_callee(tcx, def, plan, *callee, span),
                            // No generics on an inherent uint or `Nat` method,
                            // and none on the self-call.
                            &[],
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
            BasicBlockData::new_stmts(stmts, Some(Terminator { source_info, kind }), false)
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
    plan: &CleanOriginPlan,
    callee: TemplateCallee,
    span: Span,
) -> DefId {
    match callee {
        TemplateCallee::SelfDef => def.to_def_id(),
        TemplateCallee::Primitive(identity) if identity.machine_width().is_some() => {
            resolve_core_wrapping_method(tcx, identity, span)
        }
        TemplateCallee::Primitive(identity) => resolve_bignum_method(tcx, identity, span),
        TemplateCallee::RustFn { index } => resolve_rust_callee(tcx, plan, index, span),
    }
}

/// Trust (W5, Lean-calls-Rust): the REGISTERED `DefId` a plan's Rust callee
/// denotes, cross-checked against everything the compiler knows about it
/// before a call is emitted. Fatal, with the design's texts, on any skew.
///
/// Resolution is by IDENTITY, never by name: the plan's table row carries the
/// rendering of a registered `DefId` (`rust_callee_table`), and the row is
/// matched back to the `ResolverGlobalCtxt` entry whose `DefId` renders the
/// same — so the `DefId` the mint linked the bare name to is the one called.
/// Three cross-checks then bind that `DefId` to what typeck and the kernel
/// saw:
///
/// * `tcx.fn_sig` must be exactly the carriers the plan calls it at (a
///   `type u64 = …` shadow passes the AST-level admission and reaches here);
/// * `tcx.item_name` must be the Clean name the kernel applied — a `NodeId`
///   mix-up at the mint would otherwise call one function under another's
///   name, which the kernel gate is BLIND to (it sees only the constant);
/// * the `DefId` must be a local `fn`.
// Trust: the recording collector reuses this exact identity/signature check.
pub(crate) fn resolve_rust_callee<'tcx>(
    tcx: TyCtxt<'tcx>,
    plan: &CleanOriginPlan,
    index: usize,
    span: Span,
) -> DefId {
    let Some(row) = plan.callees().get(index) else {
        tcx.dcx().span_fatal(
            span,
            "internal: a Rust-call chain template names a callee outside the plan's table. \
             Please report it.",
        );
    };
    let candidates: Vec<&rustc_middle::ty::CleanRustCallee> = tcx
        .resolutions(())
        .clean_rust_callees
        .iter()
        .filter(|callee| {
            callee.clean_name.as_str() == row.clean_name
                && rust_callee_rendering(tcx, callee.def_id.to_def_id(), callee.span)
                    == row.def_path
        })
        .collect();
    let callee = match candidates[..] {
        [callee] => callee,
        ref found => tcx.dcx().span_fatal(
            span,
            format!(
                "internal: resolution of Rust callee `{}` (`{}`) for Clean declaration `{}` was \
                 {} ({} registered candidate(s)); the compiler will not guess which function \
                 to emit a call to. Please report it.",
                row.clean_name,
                row.def_path,
                plan.name(),
                if found.is_empty() { "absent" } else { "ambiguous" },
                found.len(),
            ),
        ),
    };
    let def_id = callee.def_id.to_def_id();

    // The signature typeck checked `inc` against, versus the carriers the
    // island applies it at.
    let fed = tcx.fn_sig(def_id).instantiate_identity().skip_binder();
    let expected_inputs: Vec<Ty<'tcx>> =
        row.params.iter().map(|ty| carrier_to_rustc_ty(tcx, ty, span)).collect();
    let expected_output = carrier_to_rustc_ty(tcx, &row.result, span);
    if fed.inputs() != expected_inputs.as_slice() || fed.output() != expected_output {
        tcx.dcx().span_fatal(
            span,
            format!(
                "internal: the signature typeck checked `{}` against (`fn({:?}) -> {:?}`) differs \
                 from the carriers `{}` calls it at (`fn({:?}) -> {:?}`). The mint admitted the \
                 callee from its AST spelling and the kernel typed the island at those \
                 carriers, so a divergence here means a type alias or shadow reached the \
                 callee's signature after admission. Please report it.",
                row.clean_name,
                fed.inputs(),
                fed.output(),
                plan.name(),
                expected_inputs,
                expected_output,
            ),
        );
    }
    if tcx.item_name(def_id).as_str() != row.clean_name {
        tcx.dcx().span_fatal(
            span,
            format!(
                "internal: the Rust item registered for Clean callee `{}` is named `{}`; the \
                 kernel applied `{}`, so the mint's identity link is wrong and a call would go \
                 to another function under this name. Please report it.",
                row.clean_name,
                tcx.item_name(def_id),
                row.clean_name,
            ),
        );
    }
    if !matches!(tcx.def_kind(def_id), rustc_hir::def::DefKind::Fn) {
        tcx.dcx().span_fatal(
            span,
            format!(
                "internal: the Rust item registered for Clean callee `{}` is not a free `fn` \
                 ({:?}). Please report it.",
                row.clean_name,
                tcx.def_kind(def_id),
            ),
        );
    }
    def_id
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
            Ty::new_adt(tcx, tcx.adt_def(nat), rustc_middle::ty::GenericArgs::empty())
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

/// Trust (TG6, `COMPILE-TIME-FACTS-1`): this compiler's LOCAL KERNEL FACTS, so
/// an elaboration it already performed on the same content imports its fact
/// instead of elaborating and checking again. No option turns it off
/// (STORE-1); without a private store under the cargo home, or without the
/// driver image this process runs to name the compiler by (its path must still
/// name the file the kernel reports its code mapped from), it is `None` and
/// every session checks afresh. The resolver's mint opens the same context
/// (`rustc_resolve::trust_clean_mint`).
pub(crate) fn clean_facts(
    sess: &rustc_session::Session,
) -> Option<std::sync::Arc<trust_certify::clean_fact::FactContext>> {
    let image = rustc_session::filesearch::current_dll_mapping().ok();
    trust_certify::clean_fact::FactContext::for_compiler(
        u32::from(sess.target.pointer_width),
        option_env!("CFG_VER_HASH").unwrap_or("unknown"),
        image.as_ref().map(|(path, file)| {
            let mapped =
                trust_certify::clean_fact::MappedImage { device: file.device, inode: file.inode };
            (path.as_path(), mapped)
        }),
    )
}

/// Trust (TG6): read and write [`clean_facts`] in `session`.
pub(crate) fn enable_clean_facts(
    sess: &rustc_session::Session,
    session: &mut trust_certify::clean_island::CleanIslandSession,
) {
    if let Some(facts) = clean_facts(sess) {
        session.enable_facts(facts);
    }
}
