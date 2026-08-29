// Trust (I5, `docs/design/2026-08-04-two-language-compiler-architecture.md` §7):
// THE RESOLVE-TIME HALF OF THE CLEAN-ORIGIN CALL LANE — the mint decision.
//
// This whole file is Trust-owned; it has no upstream counterpart.
//
// ════════════════════════════════════════════════════════════════════════════
// WHY THE DECISION HAS TO HAPPEN HERE, AND NOWHERE LATER
//
// `def_collector` mints `DefId`s during expansion. The design's invariant is
// that a Clean declaration acquires one *only* when it is `KernelChecked`, with
// an audited-empty axiom closure, and a total Rust carrier. Every one of those
// is a fact about the crate's Clean ENVIRONMENT, which before this file existed
// was built hundreds of phases later — from HIR, inside the `TrustVerify` MIR
// pass. So the three preconditions were unevaluable at the only point where the
// answer changes anything, and the lane could not be reached at all.
//
// The seam is the ROOT `AstFragment::Crate`, taken in
// `Resolver::visit_ast_fragment_with_placeholders` — which is
// `MacroExpander::collect_invocations`'s call into the resolver, i.e. after the
// fragment has been walked by `InvocationCollector` (so every
// `CleanIslandDecl::node_id` has been renumbered off `DUMMY_NODE_ID`) and
// immediately before `collect_definitions` runs. Putting it in the resolver
// rather than in `rustc_expand` is deliberate: `collect_invocations` is the
// *caller* of this exact point, so the sequencing is identical, and
// `rustc_expand` keeps its zero Trust dependencies.
//
// ════════════════════════════════════════════════════════════════════════════
// ISLANDS FROM LATER MACRO EXPANSION FAIL CLOSED
//
// Only the root fragment is examined. A `clean { … }` island produced by a
// macro arrives in a LATER, non-`Crate` fragment; nothing in [`CleanOriginMints`]
// will hold its declarations' `NodeId`s, so `def_collector` mints nothing for
// it and its names never enter the value namespace. A call therefore gets the
// ordinary `E0425`, which is the pre-I5 behaviour and is the fail-closed
// answer: the whole-crate Clean environment this file checks is built from the
// islands that exist BEFORE expansion, and a macro-introduced island is not in
// it, so nothing here can honestly say its declarations are kernel-checked.
//
// Widening this to later fragments is not a matter of relaxing the filter. It
// requires deciding what the crate environment MEANS when islands appear
// incrementally — an earlier island's declarations are already registered by
// the time a later one arrives, so the batch is no longer header-first over the
// whole crate and a declaration's meaning could depend on expansion order. That
// is a design question, not an implementation gap.
//
// ════════════════════════════════════════════════════════════════════════════
// THE COST, STATED RATHER THAN HIDDEN
//
// §8 of the design doc budgeted `trust-symbols` under the resolver. This brings
// the whole Clean closure — `trust-certify` pulls `clean-kernel`, `clean-elab`,
// `clean-parser`, `clean-auto`, `clean-verify`, `trust-spec-elab`, `trust-ir`
// and `trust-cert-meter` — into `rustc_resolve`'s dependency graph. None of
// them names a rustc crate, so there is no cycle, but the compiler's build now
// links the elaborator and the kernel one crate earlier than it used to.
//
// The RUNTIME cost is gated: [`decide`] returns immediately, having allocated
// nothing, for a crate with no `clean { … }` island — which is every crate in
// the standard library and every crate of ordinary Rust. The kernel only runs
// when the user wrote an island.

use rustc_ast::visit::{self, Visitor};
use rustc_ast::{CleanDeclKind, Item, ItemKind, NodeId};
use rustc_expand::expand::AstFragment;
use rustc_span::{Span, Symbol};

/// The Rust carrier type of one signature position of a Clean declaration.
///
/// A deliberate re-spelling of the fragment of `trust_types::Ty` that I4 can
/// currently grant a TOTAL carrier for, so that the resolver names a closed set
/// rather than a general type. Anything outside it never reaches here:
/// `trust_clean_carrier::carrier_signature_for` refuses, the mint is refused,
/// and no `DefId` exists to need a signature.
///
/// **This enum and `rustc_mir_transform`'s `carrier_to_rustc_ty` are two
/// readings of the same I4 decision, in two crates that cannot share a
/// mapping** (one needs `TyCtxt` at resolve time, the other at MIR time). A
/// divergence between them would be a body whose locals disagree with the
/// signature typeck checked the call against — a wrong binary. It is not left
/// to review: `clean_origin_mir` re-derives the signature from the plan and
/// compares it against `tcx.fn_sig` before returning a body, and a mismatch is
/// fatal. See the cross-check there.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum CleanCarrierTy {
    Bool,
    U8,
    U16,
    U32,
    U64,
    /// Trust (I6): the `trust_bignum::Nat` carrier — unbounded, exact, NOT
    /// `Copy`. Unlike every other variant it denotes a type from a crate,
    /// not a primitive, so [`rustc_ty`] resolves it through the one `DefId`
    /// of record the carrier-crate load step stored in `CStore`. A grant
    /// carrying this variant survives only if that load succeeded —
    /// [`crate::Resolver::trust_resolve_carrier_crates`] demotes it to a
    /// refusal otherwise — which is what makes the `rustc_ty` lookup
    /// infallible-by-construction.
    Nat,
}

impl CleanCarrierTy {
    /// The I4 carrier this position was granted, or `None` if I4 granted a
    /// carrier this compiler has no rustc type for.
    ///
    /// `None` REFUSES the mint. It never falls back to a default type: a
    /// guessed carrier is an emitted value that disagrees with the declaration,
    /// and kernel definitional equality does not catch that (I4's
    /// `control_b_defeq_insufficiency`).
    fn from_trust_ty(ty: &trust_types::Ty) -> Option<Self> {
        match ty {
            trust_types::Ty::Bool => Some(Self::Bool),
            trust_types::Ty::Int { width: 8, signed: false } => Some(Self::U8),
            trust_types::Ty::Int { width: 16, signed: false } => Some(Self::U16),
            trust_types::Ty::Int { width: 32, signed: false } => Some(Self::U32),
            trust_types::Ty::Int { width: 64, signed: false } => Some(Self::U64),
            // Trust (I6): the bignum carrier. Mapping it here is what lets a
            // `Nat`-signed declaration mint at all; whether the grant SURVIVES
            // depends on the carrier crate actually loading, which
            // `trust_resolve_carrier_crates` settles immediately after
            // `decide` — a load failure demotes the grant to a refusal, so
            // this arm never produces a callable def whose carrier type
            // cannot be named.
            trust_types::Ty::BignumNat => Some(Self::Nat),
            _ => None,
        }
    }
}

/// The rustc type a discharged I4 carrier denotes.
///
/// TOTAL over [`CleanCarrierTy`] and nothing else — the enum exists so that
/// this match has no fallback arm. A guessed type here is an emitted value that
/// disagrees with the declaration, which kernel definitional equality does not
/// catch.
pub(crate) fn rustc_ty<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    carrier: CleanCarrierTy,
) -> rustc_middle::ty::Ty<'tcx> {
    match carrier {
        CleanCarrierTy::Bool => tcx.types.bool,
        CleanCarrierTy::U8 => tcx.types.u8,
        CleanCarrierTy::U16 => tcx.types.u16,
        CleanCarrierTy::U32 => tcx.types.u32,
        CleanCarrierTy::U64 => tcx.types.u64,
        // Trust (I6): UNREACHABLE at resolve time, by design. Building the
        // `Nat` type demands `adt_def(trust_bignum::Nat)`, and an extern
        // `adt_def` decode walks `lang_items` -> `resolver_for_lowering` —
        // a query CYCLE from inside resolution (measured: E0391 on the first
        // `Nat` fixture). A `Nat`-carrying grant therefore never reaches this
        // function: its `fn_sig` feed is SKIPPED and the signature travels to
        // the `fn_sig` provider arm (`rustc_hir_analysis`) through
        // `ResolverGlobalCtxt::clean_origin_deferred_sigs`, where the decode
        // is legal. See `trust_feed_clean_origin_def`.
        CleanCarrierTy::Nat => tcx.dcx().fatal(
            "internal: the `Nat` carrier's rustc type was demanded during \
             resolution, which deadlocks on `adt_def`. `Nat` signatures are \
             deferred to the `fn_sig` provider arm; this call is a compiler \
             defect. Please report it.",
        ),
    }
}

impl CleanCarrierTy {
    /// Trust (I6): the `rustc_middle` spelling, for the deferred-`fn_sig`
    /// transport (`ResolverGlobalCtxt::clean_origin_deferred_sigs`).
    pub(crate) fn to_middle(self) -> rustc_middle::ty::TrustCleanCarrier {
        use rustc_middle::ty::TrustCleanCarrier as M;
        match self {
            CleanCarrierTy::Bool => M::Bool,
            CleanCarrierTy::U8 => M::U8,
            CleanCarrierTy::U16 => M::U16,
            CleanCarrierTy::U32 => M::U32,
            CleanCarrierTy::U64 => M::U64,
            CleanCarrierTy::Nat => M::Nat,
        }
    }
}

/// A Clean island declaration that earned a `DefId`, and everything
/// `def_collector` needs to mint and feed one.
#[derive(Clone, Debug)]
pub(crate) struct CleanOriginMint {
    /// The declaration name, which is also the Rust name planted in the
    /// enclosing module's value namespace.
    pub(crate) name: Symbol,
    /// The declaration's extent inside its island, in rustc coordinates.
    pub(crate) span: Span,
    /// Argument carriers, in order. Fed as `fn_sig`'s inputs.
    pub(crate) params: Vec<CleanCarrierTy>,
    /// Result carrier. Fed as `fn_sig`'s output.
    pub(crate) result: CleanCarrierTy,
}

/// Why a declaration the user can see in an island did not become callable.
///
/// Ruling v7/D3: a refusal must carry the fix, with options. Bare, the `E0425`
/// a refused declaration produces is a lie by omission — the declaration is
/// right there in the source. The note is recorded here at the point the
/// decision is made so the diagnostic can quote the real reason rather than
/// reconstruct one.
#[derive(Clone, Debug)]
pub(crate) struct CleanOriginRefusal {
    pub(crate) name: Symbol,
    pub(crate) span: Span,
    pub(crate) note: String,
}

/// The crate's mint decisions, keyed by declaration `NodeId`.
///
/// Empty — and cheap — for every crate with no `clean { … }` island. A `Vec`
/// rather than a map on purpose: [`Resolver`](crate::Resolver) initialises this
/// field through the default-field-value syntax, which demands a `const`
/// constructor, and the list has one entry per callable Clean declaration in
/// the crate — a scale where a linear scan is not worth a hash.
#[derive(Default)]
pub(crate) struct CleanOriginMints {
    granted: Vec<(NodeId, CleanOriginMint)>,
    refused: Vec<CleanOriginRefusal>,
}

impl CleanOriginMints {
    /// The empty decision: nothing minted, nothing refused. This is what every
    /// crate without a `clean { … }` island holds for the whole compilation.
    pub(crate) const fn new() -> Self {
        Self { granted: Vec::new(), refused: Vec::new() }
    }

    /// The grant for one declaration, or `None` — which means "no `DefId`", and
    /// is the answer for a declaration that failed a precondition, for a
    /// declaration in a macro-introduced island, and for every crate that never
    /// ran the decision at all.
    pub(crate) fn grant(&self, node_id: NodeId) -> Option<&CleanOriginMint> {
        self.granted.iter().find(|(id, _)| *id == node_id).map(|(_, grant)| grant)
    }

    /// Every refusal, for the v7/D3 diagnostics.
    pub(crate) fn refusals(&self) -> &[CleanOriginRefusal] {
        &self.refused
    }
}

/// The `rust_carrier` spelling every `Nat` position is admitted at.
///
/// Not a heuristic string: `trust_symbols`' `TRUSTED_RUNTIME_CARRIERS` pins the
/// single row `("Nat", "trust_bignum::Nat")`, so this is the ONE wire spelling a
/// [`CleanCarrierTy::Nat`] position can be encoded under, both in a local grant
/// and in an imported verdict digest.
const NAT_RUST_CARRIER: &str = "trust_bignum::Nat";

/// Does this grant name `Nat` anywhere in its signature?
fn carries_nat(mint: &CleanOriginMint) -> bool {
    mint.result == CleanCarrierTy::Nat || mint.params.contains(&CleanCarrierTy::Nat)
}

/// Does one position of an IMPORTED verdict digest claim the `Nat` carrier?
///
/// A read of wire data, and nothing more: it decides only whether the carrier
/// crate is worth loading. The import lane re-derives the carrier locally and
/// refuses on any disagreement with what the digest claimed.
fn position_claims_nat(position: &trust_clean_origin::CarrierPosition) -> bool {
    position.rust_carrier() == NAT_RUST_CARRIER
}

/// One island as the checker needs to see it.
struct IslandSource {
    content_span: Span,
    text: String,
    decls: Vec<(NodeId, Symbol, Span)>,
}

/// Collects `clean { … }` islands out of the unexpanded crate.
struct IslandCollector {
    islands: Vec<IslandSource>,
}

impl<'ast> Visitor<'ast> for IslandCollector {
    fn visit_item(&mut self, item: &'ast Item) {
        if let ItemKind::CleanIsland(island) = &item.kind {
            self.islands.push(IslandSource {
                content_span: island.content_span,
                text: island.text.to_string(),
                decls: island
                    .decls
                    .iter()
                    // ONLY `def`. A `theorem` is proof-irrelevant, an `axiom`
                    // exhibits no value, an `opaque` is deliberately withheld
                    // from reduction, and an `inductive` is a type — none of
                    // them is something emitted code could be faithful to, and
                    // `plan_clean_origin_body` refuses each of them anyway.
                    // Filtering here keeps the refusal list about declarations
                    // the user could plausibly have meant to call.
                    .filter(|decl| decl.kind == CleanDeclKind::Def)
                    .filter(|decl| decl.name != rustc_span::sym::empty)
                    .filter(|decl| decl.node_id != rustc_ast::DUMMY_NODE_ID)
                    .map(|decl| (decl.node_id, decl.name, decl.span))
                    .collect(),
            });
        }
        visit::walk_item(self, item);
    }
}

/// Decide, for the whole crate at once, which Clean island declarations may
/// acquire a `DefId`.
///
/// `fragment` must be the ROOT `AstFragment::Crate`; anything else returns the
/// empty decision (see the fail-closed note in the module docs).
///
/// # This function is the only place the three preconditions are evaluated
///
/// It does not approximate them and it does not carry a verdict forward from
/// somewhere else:
///
/// 1. **`KernelChecked`** — `trust_certify::clean_island::admit_certified_island_definition`
///    is the compiler's sealed "kernel re-checked THIS declaration" seam. It
///    runs the canonical certification meter over the declaration's own
///    obligation and mints a `KernelStatus` through
///    `trust_symbols::CicKernelRecheck`. A `Trusted` grade (a non-empty
///    provenance closure) is an `Err` there, so nothing resting on `sorry`
///    reaches the grant.
/// 2. **An audited-empty axiom closure** — read out of that same status by
///    `decide_mint`, never supplied alongside it.
/// 3. **A total carrier** — `carrier_signature_for` over the declaration's
///    Clean type, which cannot succeed with a partial position anywhere in the
///    signature.
///
/// A fourth condition is added, and it is NOT a precondition of the design's
/// invariant: the body must be one `plan_clean_origin_body` can originate MIR
/// for. Without it, a kernel-checked
/// `def f (a b : UInt64) : UInt64 := (a + b) * a` would mint a `DefId`,
/// resolve, typeck — and then hit a FATAL refusal in `clean_origin_mir` at
/// codegen, because nested operations are outside the emittable fragment
/// (parameter projections and single wrapping binops). Deciding it here
/// converts a fatal into an `E0425` carrying a v7/D3 note, which is strictly
/// the better refusal and is still fail-closed (it only ever mints FEWER
/// defs).
pub(crate) fn decide(fragment: &AstFragment) -> CleanOriginMints {
    let AstFragment::Crate(krate) = fragment else {
        return CleanOriginMints::default();
    };

    let mut collector = IslandCollector { islands: Vec::new() };
    visit::walk_crate(&mut collector, krate);
    let mut islands = collector.islands;
    if islands.is_empty() {
        // The overwhelmingly common case: no island, no kernel, no allocation.
        return CleanOriginMints::default();
    }

    // Clean file state (namespaces, `open`s, notation, options) evolves in
    // AUTHORED source order across islands, so the batch must be ordered the
    // way the user wrote it, not the way the AST walk happened to reach it.
    // This mirrors `trust_verify.rs`'s `trust_check_clean_islands`, which is
    // the other consumer of the same environment.
    islands.sort_by_key(|island| (island.content_span.lo(), island.content_span.hi()));

    let mut decision = CleanOriginMints::default();

    let sources: Vec<&str> = islands.iter().map(|island| island.text.as_str()).collect();
    let mut session = trust_certify::clean_island::CleanIslandSession::new();
    let batch = session.check_all(&sources);
    if batch.is_rejected() {
        // A rejected island means the Rust build is already failing, and a
        // partially registered environment must never mint positive evidence.
        // Nothing is granted, and no refusal note is recorded either: the Clean
        // diagnostic the verify pass emits is the true explanation, and a
        // second "not kernel-checked" note would be noise.
        return decision;
    }
    let Some(env) = session.environment() else {
        return decision;
    };

    // The facet table is scratch for `admit_certified_island_definition`, which
    // needs somewhere to record the admission it mints. It is deliberately not
    // carried anywhere: this lane wants the STATUS, and the elaborator lane
    // builds its own table from its own environment.
    let mut facets = trust_spec_elab::FacetTable::new();

    for island in &islands {
        for &(node_id, name, span) in &island.decls {
            let name_str = name.as_str();

            // Precondition 1: the kernel re-checked this declaration.
            let status = match trust_certify::clean_island::admit_certified_island_definition(
                env,
                name_str,
                &mut facets,
            ) {
                Ok(admission) => admission.status().clone(),
                // Fail-closed to the weakest status. `decide_mint` turns that
                // into `NotKernelChecked`, whose note carries the reason and
                // the options.
                Err(_) => trust_symbols::KernelStatus::Parsed,
            };

            // Precondition 3: a TOTAL carrier for every signature position. The
            // whole signature is demanded even though `decide_mint` records one
            // carrier — a declaration whose result carries but whose second
            // argument does not is not callable, and `carrier_signature_for`
            // is the function that says so.
            //
            // A declaration the parser saw but the environment does not hold is
            // refused HERE rather than fed to `decide_mint` with a stand-in
            // carrier. There is no honest `Carrier` to supply for a constant
            // that does not exist, and constructing one would be exactly the
            // fabrication this lane cannot survive.
            let Some(constant) = env.get_const(&clean_kernel::Name::from_string(name_str)) else {
                decision.refused.push(CleanOriginRefusal {
                    name,
                    span,
                    note: format!(
                        "`{name_str}` was parsed as a `def` in this island but is not \
                         registered in the crate's Clean environment, so there is nothing \
                         for the kernel to have checked.\n\
                         options:\n\
                         - check for an elaboration error reported against this island \
                           earlier in the build, and fix that first;\n\
                         - if `{name_str}` is meant to be specification-only, cite it from \
                           a contract instead of calling it."
                    ),
                });
                continue;
            };
            let carrier = trust_clean_carrier::carrier_signature_for(&constant.type_)
                .map(|signature| signature.result().clone());

            // Preconditions 1 + 2 + 3, as the sealed decision of record.
            match trust_clean_origin::decide_mint(name_str, &status, carrier) {
                Ok(_grant) => {}
                Err(refusal) => {
                    decision.refused.push(CleanOriginRefusal { name, span, note: refusal.note() });
                    continue;
                }
            }

            // The emittability condition. Side A only — this is not the gate,
            // and it is not permission to emit; `clean_origin_mir` re-derives
            // the same plan at MIR time and puts the EMITTED body to the
            // kernel. What it buys here is that a declaration which could never
            // produce a body does not become callable.
            let plan = match trust_clean_origin::plan_clean_origin_body(env, name_str) {
                Ok(plan) => plan,
                Err(refusal) => {
                    decision.refused.push(CleanOriginRefusal { name, span, note: refusal.note() });
                    continue;
                }
            };

            // The signature the `DefId` will be typed at, in rustc's closed
            // vocabulary. A position I4 granted but this compiler has no rustc
            // type for refuses the mint rather than picking one.
            let params: Option<Vec<CleanCarrierTy>> = plan
                .signature()
                .arguments()
                .iter()
                .map(|carrier| CleanCarrierTy::from_trust_ty(carrier.rust()))
                .collect();
            let (Some(params), Some(result)) =
                (params, CleanCarrierTy::from_trust_ty(plan.signature().result().rust()))
            else {
                decision.refused.push(CleanOriginRefusal {
                    name,
                    span,
                    note: format!(
                        "`{name_str}` is kernel-checked and carries totally, but one of its \
                         signature positions has no rustc type in this compiler, so no Rust \
                         function signature can be given for it. This is a compiler capability \
                         limit, not something you wrote wrong.\n\
                         options:\n\
                         - restate `{name_str}` at `UInt8`/`UInt16`/`UInt32`/`UInt64`/`Bool` \
                           (or `Nat`, which carries at `trust_bignum::Nat`), which this \
                           compiler can type;\n\
                         - cite `{name_str}` from proof position instead, which needs no Rust \
                           signature;\n\
                         - report the carrier this compiler is missing, so it can be added."
                    ),
                });
                continue;
            };

            decision.granted.push((node_id, CleanOriginMint { name, span, params, result }));
        }
    }

    decision
}

impl crate::Resolver<'_, '_> {
    /// Trust (I6): resolve the carrier CRATES the mint decision depends on —
    /// today exactly one, `trust_bignum` for [`CleanCarrierTy::Nat`] — and
    /// demote every grant whose carrier crate could not be loaded.
    ///
    /// Called once per crate, immediately after [`decide`] at the root-fragment
    /// seam and therefore BEFORE `collect_definitions` feeds any signature: by
    /// the time [`rustc_ty`] needs the `Nat` `DefId`, it is either on record in
    /// `CStore` or every grant that would have asked for it has been demoted.
    ///
    /// # The trigger is exact, not conservative
    ///
    /// The load fires iff at least one GRANTED declaration carries `Nat` in a
    /// signature position. A crate whose islands never touch `Nat` — and every
    /// crate with no island at all — loads nothing and pays nothing. (The plan
    /// named "any island present" as an acceptable conservative fallback; it
    /// was not needed, because the grants are already in hand here.)
    ///
    /// # This is the DECLARE half only
    ///
    /// A crate that merely IMPORTS a `Nat`-carrying Clean-origin def has no
    /// local grant, so nothing here fires — and no extern crate is loaded yet
    /// at this seam anyway (measured: the carrier is `CrateNum` 1, the imported
    /// crate is registered much later, out of `build_reduced_graph`). The
    /// import half is [`Self::trust_resolve_imported_carrier_crates`], run
    /// after late resolution.
    ///
    /// # Demotion, not diagnosis (ruling v7/D3)
    ///
    /// A load failure does not report a loader error about a crate the user
    /// never named. The affected grants become [`CleanOriginRefusal`]s whose
    /// note carries the loader's typed reason
    /// ([`TrustBignumLoadRefusal::reason`]) and the options; the user sees the
    /// ordinary `E0425` at the call site with that note attached — fail-closed
    /// (strictly FEWER defs are minted), and the emitted body can never
    /// reference a crate that is not there.
    ///
    /// # Why the `Nat` lookup happens here and not in the creader
    ///
    /// `CStore::trust_load_bignum_carrier` runs under the `CStore` WRITE guard
    /// and so cannot evaluate `module_children`, whose provider takes the read
    /// guard. This method holds no guard across the query: the load (write
    /// guard, dropped at the statement's end), then the query, then the
    /// recording (write guard again). The `module_children` call on an extern
    /// crate root during expansion is the resolver's ordinary practice — see
    /// `build_reduced_graph_external`.
    pub(crate) fn trust_resolve_carrier_crates(&mut self) {
        if !self.clean_origin_mints.granted.iter().any(|(_, mint)| carries_nat(mint)) {
            return;
        }
        self.trust_load_nat_carrier_of_record();
    }

    /// Trust (I6): the IMPORT half of the same decision — load the carrier for
    /// a crate that never DECLARES a `Nat`-carrying Clean-origin def but does
    /// name a crate that EXPORTS one.
    ///
    /// # Why this cannot be folded into the mint seam
    ///
    /// MEASURED: at the root-fragment seam where
    /// [`Self::trust_resolve_carrier_crates`] runs, no extern crate of the
    /// user's has been registered yet — `extern crate` items are processed out
    /// of `build_reduced_graph`, long after. So "does this crate import a
    /// `Nat`-carrying Clean-origin def" is not a question that can be asked
    /// there, and an import-only crate used to reach MIR time with
    /// `trust_bignum_nat` still `None`, where `carrier_to_rustc_ty`'s internal
    /// span_fatal fired on a program that was in every way well-formed. That
    /// fatal's "post-mint impossibility" reading held for the LOCAL lane only.
    ///
    /// Called from `Resolver::resolve_crate` after late resolution — every path
    /// this crate resolved is on record, the `CStore` is still writable, and
    /// `postprocess` has not run yet, which is the same window the mint seam
    /// records in.
    ///
    /// # The trigger, and why it is a superset of nothing dangerous
    ///
    /// It fires iff some crate this crate resolved a path into lists a
    /// Clean-origin export whose verdict digest claims a
    /// [`NAT_RUST_CARRIER`] position. The digest is WIRE DATA and is treated
    /// only as a hint about what to load: it grants nothing, it admits nothing,
    /// and the import lane (`trust_clean_extern_readmission`) still re-derives
    /// the carrier locally and refuses on any disagreement. A digest that lies
    /// "yes" costs one sysroot rlib nobody calls; a digest that lies "no"
    /// leaves the carrier absent and the MIR-time fatal fires, which is where
    /// it was already.
    ///
    /// Nothing here can widen the local mint decision: no grant is created, and
    /// the demotion arm below only ever REMOVES grants.
    ///
    /// # Cost, stated rather than hidden
    ///
    /// One `trust_clean_origin_exports` decode per distinct extern crate this
    /// crate resolved a path into — an empty root array for every crate of
    /// ordinary Rust — plus one digest decode per Clean-origin export of a
    /// crate that has any. Nothing runs the kernel and nothing decodes a type,
    /// which is what keeps this legal at resolve time: an extern `adt_def`
    /// decode from inside resolution is the measured `lang_items` ->
    /// `resolver_for_lowering` query cycle (see [`rustc_ty`]).
    pub(crate) fn trust_resolve_imported_carrier_crates(&mut self) {
        use rustc_data_structures::unord::UnordSet;
        use rustc_hir::def_id::{CrateNum, DefId};

        // Already settled at the mint seam: either the `DefId` is on record, or
        // the load was attempted, memoized as a failure, and every local `Nat`
        // grant demoted. Re-deciding it here could only reach the same answer.
        if self.cstore().trust_bignum_nat().is_some() {
            return;
        }

        let referenced: UnordSet<CrateNum> = self
            .partial_res_map
            .items()
            // `base_res`, not `full_res`: a path with unresolved segments
            // (`Nat::from_u64`) still names the crate it descends into.
            .filter_map(|(_, res)| res.base_res().opt_def_id())
            .filter(|def_id| !def_id.is_local())
            .map(|def_id| def_id.krate)
            .collect();
        // Iterate in `CrateNum` order rather than hash order, and DO NOT
        // short-circuit: which extern queries get forced must not depend on the
        // iteration order of an unordered map.
        let Some(highest) = referenced.items().copied().max() else {
            return;
        };

        let tcx = self.tcx;
        let mut imports_nat_carrier = false;
        for raw in 1..=highest.as_u32() {
            let krate = CrateNum::from_u32(raw);
            if !referenced.contains(&krate) {
                continue;
            }
            // Empty for every crate of ordinary Rust — this is the fast path.
            for &index in tcx.trust_clean_origin_exports(krate) {
                let def_id = DefId { krate, index };
                // A listed def with no digest row, or one that does not decode,
                // is refused by the import lane BEFORE it ever needs a carrier
                // type. Loading nothing for it is the fail-closed answer, and
                // the refusal the user sees stays the honest one.
                let Some(bytes) = tcx.trust_clean_verdict_digest(def_id) else {
                    continue;
                };
                let Ok(digest) = trust_clean_origin::VerdictDigest::decode(bytes) else {
                    continue;
                };
                let carrier = digest.carrier();
                if position_claims_nat(carrier.result())
                    || carrier.arguments().iter().any(position_claims_nat)
                {
                    imports_nat_carrier = true;
                }
            }
        }

        if !imports_nat_carrier {
            return;
        }
        self.trust_load_nat_carrier_of_record();
    }

    /// The load itself, shared by both triggers: resolve `trust_bignum`, verify
    /// it exports exactly one root `struct Nat`, record that `DefId` — or demote
    /// every local `Nat`-carrying grant to a v7/D3 refusal.
    fn trust_load_nat_carrier_of_record(&mut self) {
        use rustc_hir::def::{DefKind, Res};
        use rustc_metadata::creader::TrustBignumLoadRefusal;

        // The write guard is a temporary of this statement; it is released
        // before the `module_children` query below.
        let loaded = self.cstore_mut().trust_load_bignum_carrier(self.tcx);

        let outcome = loaded.and_then(|cnum| {
            // Sanity check (the `is_panic_runtime` analog): the loaded crate
            // must export exactly one root `struct Nat`. Anything else is not
            // the carrier runtime this compiler shipped.
            let nats: Vec<_> = self
                .tcx
                .module_children(cnum.as_def_id())
                .iter()
                .filter_map(|child| match child.res {
                    Res::Def(DefKind::Struct, def_id)
                        if child.ident.name == rustc_span::sym::Nat =>
                    {
                        Some(def_id)
                    }
                    _ => None,
                })
                .collect();
            match nats.as_slice() {
                [def_id] => Ok(*def_id),
                other => Err(TrustBignumLoadRefusal::NoUniqueNatStruct { found: other.len() }),
            }
        });

        match outcome {
            Ok(def_id) => {
                // THE DefId of record. `rustc_ty` (the signature feed) and
                // `carrier_to_rustc_ty` (the MIR-time emission) both resolve
                // through it, which is what keeps one impersonation from
                // splitting the type typeck checked from the type the body
                // computes at.
                self.cstore_mut().trust_record_bignum_nat(def_id);
            }
            Err(refusal) => {
                let reason = refusal.reason();
                let CleanOriginMints { granted, refused } = &mut self.clean_origin_mints;
                granted.retain(|(_, mint)| {
                    if !carries_nat(mint) {
                        return true;
                    }
                    let name = mint.name;
                    refused.push(CleanOriginRefusal {
                        name,
                        span: mint.span,
                        note: format!(
                            "`{name}` is kernel-checked and its `Nat` positions carry at \
                             `trust_bignum::Nat`, but the carrier runtime could not become \
                             the carrier of record: {reason}.\n\
                             options:\n\
                             - reinstall or rebuild this toolchain so `libtrust_bignum` \
                               ships in the sysroot (it is built as part of the standard \
                               library);\n\
                             - if this build supplies the standard library from outside \
                               the sysroot (`-Zbuild-std`, bootstrap-style graphs), that \
                               configuration is a known limitation of the carrier loader \
                               — restate `{name}` at a fixed-width type \
                               (`UInt8`/`UInt16`/`UInt32`/`UInt64`/`Bool`) for now;\n\
                             - keep `{name}` specification-only and cite it from proof \
                               position, which needs no Rust signature."
                        ),
                    });
                    false
                });
            }
        }
    }

    /// Trust (I5, ruling v7/D3): if an unresolved path names a Clean island
    /// declaration this crate REFUSED to mint, say so, and say what to do.
    ///
    /// Without this the user gets a bare "cannot find function `f`" pointing at
    /// a call whose callee is visibly declared three lines above, in an island
    /// they wrote. That is a lie by omission. The note names the precondition
    /// that was missing and gives at least two courses of action — the refusal
    /// text is the one [`decide`] recorded when it made the decision, never a
    /// reconstruction, so it cannot drift from the reason.
    ///
    /// Silent for every ordinary unresolved name: the loop only fires on a
    /// declaration that really was refused.
    pub(crate) fn trust_note_clean_origin_refusal(
        &self,
        err: &mut rustc_errors::Diag<'_>,
        path: &[crate::Segment],
    ) {
        let Some(last) = path.last() else { return };
        let Some(refusal) =
            self.clean_origin_mints.refusals().iter().find(|r| r.name == last.ident.name)
        else {
            return;
        };
        err.span_note(
            refusal.span,
            format!(
                "`{}` is declared in this `clean {{ … }}` island, but it did not become \
                 callable from Rust",
                refusal.name
            ),
        );
        err.note(refusal.note.clone());
    }
}
