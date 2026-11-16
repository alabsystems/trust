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
use rustc_errors::DiagCtxtHandle;
use rustc_expand::expand::AstFragment;
use rustc_span::{BytePos, Span, Symbol};

// Trust (W5, Lean-calls-Rust): the design of record is
// `docs/design/2026-09-13-lean-calls-rust-lane.md`. This file owns increment
// 1's mint half — which sibling Rust `fn`s an island may call, declared in the
// same kernel session the batch is checked in, BEFORE `check_all`, so the
// island's `inc (inc x)` elaborates against a real constant (ruling v7/D1).

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
    /// Trust (W5): the `trust_types` spelling, for the callee table the
    /// planner and the environment helper read.
    fn to_trust_ty(self) -> trust_types::Ty {
        match self {
            CleanCarrierTy::Bool => trust_types::Ty::Bool,
            CleanCarrierTy::U8 => trust_types::Ty::u8(),
            CleanCarrierTy::U16 => trust_types::Ty::u16(),
            CleanCarrierTy::U32 => trust_types::Ty::u32(),
            CleanCarrierTy::U64 => trust_types::Ty::u64(),
            CleanCarrierTy::Nat => trust_types::Ty::BignumNat,
        }
    }

    /// Trust (W5): the carrier a Rust callee's AST TYPE denotes — a
    /// SINGLE-SEGMENT, argument-free path spelling one of
    /// `bool`/`u8`/`u16`/`u32`/`u64` — or `None`. Deliberately syntactic: at
    /// the mint seam nothing is resolved, so `type u64 = String;` in scope
    /// would pass here; that is why MIR time re-derives the signature from
    /// `tcx.fn_sig` and is fatal on any skew (`clean_origin_mir.rs`,
    /// `resolve_template_callee`).
    fn from_ast_carrier(ty: &rustc_ast::Ty) -> Option<Self> {
        let rustc_ast::TyKind::Path(None, path) = &ty.kind else { return None };
        let [segment] = path.segments.as_slice() else { return None };
        if segment.args.is_some() {
            return None;
        }
        match segment.ident.name {
            rustc_span::sym::bool => Some(Self::Bool),
            rustc_span::sym::u8 => Some(Self::U8),
            rustc_span::sym::u16 => Some(Self::U16),
            rustc_span::sym::u32 => Some(Self::U32),
            rustc_span::sym::u64 => Some(Self::U64),
            _ => None,
        }
    }

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
    /// Trust (W5): whether the def may be `const fn`. `true` unless its body
    /// calls a Rust callee whose AST header is not `const` — fed as
    /// `constness`, so a non-`const` callee reached from a `const` item gets
    /// Rust's ordinary E0015 rather than a CTFE surprise
    /// (`build_reduced_graph.rs`'s feed used to say `Const` unconditionally).
    pub(crate) is_const: bool,
}

/// Trust (W5, Lean-calls-Rust): one sibling Rust `fn` the mint ADMITTED as
/// callable from the islands of its module — the resolve-time half of
/// `rustc_middle::ty::CleanRustCallee`, keyed by the item's `NodeId` until
/// `Resolver::into_outputs` maps it to the `LocalDefId` every later phase
/// links by.
#[derive(Clone, Debug)]
pub(crate) struct RustCalleeCandidate {
    /// The `fn` item's `NodeId`.
    pub(crate) node_id: NodeId,
    /// Its bare name — the Clean constant it is declared as.
    pub(crate) name: Symbol,
    /// Parameter carriers, in order.
    pub(crate) params: Vec<CleanCarrierTy>,
    /// Result carrier.
    pub(crate) result: CleanCarrierTy,
    /// The AST header's `const`.
    pub(crate) is_const: bool,
    /// The ident span.
    pub(crate) span: Span,
}

impl RustCalleeCandidate {
    /// The environment helper's spelling.
    fn to_rust_callee(&self) -> trust_certify::clean_island::RustCallee {
        trust_certify::clean_island::RustCallee {
            clean_name: self.name.to_string(),
            params: self.params.iter().map(|c| c.to_trust_ty()).collect(),
            result: self.result.to_trust_ty(),
        }
    }

    /// The planner's spelling — the MINT-SEAM table, whose `def_path` is
    /// empty because no `DefId` exists yet; a plan built over it plans the
    /// shape and can never be admitted (`admit_lowering` refuses an empty
    /// rendering), which is exactly this seam's contract.
    fn to_callee_ref(&self) -> trust_clean_origin::RustCalleeRef {
        trust_clean_origin::RustCalleeRef {
            clean_name: self.name.to_string(),
            def_path: String::new(),
            params: self.params.iter().map(|c| c.to_trust_ty()).collect(),
            result: self.result.to_trust_ty(),
        }
    }
}

/// Trust (W5): why a sibling `fn` an island could see was NOT admitted, so
/// the `Unknown identifier` the island then gets can say why (ruling v7/D3).
#[derive(Clone, Debug)]
struct RustCalleeRefusal {
    name: Symbol,
    note: String,
    /// Trust (2026-09-16, silent-precedence hazard): set whenever an island
    /// `def` in ANOTHER module, or (2026-09-28) the Clean prelude, bears the
    /// refused `fn`'s bare name — whatever the `fn` was refused for (the
    /// one-namespace rule, its shape, its contract). Such a refusal cannot
    /// surface through `Unknown identifier`, because the name DOES resolve (to
    /// that `def`, or to the prelude constant). Holds what
    /// [`warn_shadowed_callees`] needs to say so; `None` otherwise.
    shadowed: Option<ShadowedCallee>,
}

/// Trust: where a sibling `fn` was refused because an island `def` elsewhere,
/// or the Clean prelude, already bears its bare name. See
/// [`RustCalleeRefusal::shadowed`].
#[derive(Clone, Debug)]
struct ShadowedCallee {
    /// Every refused bearer: its module (an index into
    /// [`IslandCollector::modules`]) and its ident span.
    fns: Vec<(usize, Span)>,
    /// What wins the name instead.
    owner: ShadowOwner,
}

/// Trust: what a sibling island's use of a refused `fn`'s bare name resolves to.
#[derive(Clone, Debug)]
enum ShadowOwner {
    /// The island `def` of that name in these modules.
    IslandDefs(Vec<usize>),
    /// Trust (2026-09-28): a constant of Clean's built-in prelude. Measured:
    /// `fn id(x: u64) -> u64 { x.wrapping_add(1) }` beside
    /// `clean { def call_id (x : UInt64) : UInt64 := id x }` built, ran, and
    /// printed `call_id(5) = 5` against the Rust `id(5) = 6`, with no
    /// diagnostic at all. The one-namespace rule refused the `fn` (the prelude
    /// holds `id`), but that refusal was only ever reported through an
    /// `Unknown identifier`, and `id` does resolve: to the prelude's `id`.
    Prelude,
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

/// Trust (2026-09-16, ruling v7/D3): a `def` the crate's Clean batch REGISTERED
/// from inside a `namespace`/`section`/`mutual` block of an island.
///
/// Not a [`CleanOriginRefusal`], because nothing was refused: the mint decision
/// only ever considers an island's TOP-LEVEL `def`s, so a nested one was never
/// a candidate. It is recorded so the call site can be told that. Measured on
/// probe 24: `namespace Geo def area … end Geo`, called as `m::Geo::area` or
/// `m::area`, produced a bare `E0433`/`E0425` with the declaration in plain
/// sight — and existing Lean libraries are namespaced throughout.
#[derive(Clone, Debug)]
pub(crate) struct CleanOriginNestedDef {
    /// The bare final component — what a Rust call site spells last.
    pub(crate) name: Symbol,
    /// The components of the enclosing Clean namespace (`Geo`), empty for a
    /// `section`/`mutual` block. An `E0433` is annotated only when the failing
    /// path walks through one of these.
    pub(crate) namespace: Vec<Symbol>,
    /// The name the Clean environment holds it under (`Geo.area`).
    pub(crate) clean_name: String,
    /// The enclosing top-level block of the island ([`nested_block_span`]).
    pub(crate) span: Span,
    /// `trust_clean_origin::MintRefusal::NotTopLevel`'s note, verbatim.
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
    /// Trust: registered `def`s that were never mint candidates because they
    /// are not top-level — diagnostics only. See [`CleanOriginNestedDef`].
    nested: Vec<CleanOriginNestedDef>,
    /// Trust (W5): the sibling Rust `fn`s admitted as callable from islands —
    /// THE ONE SET every island-elaborating session declares. Empty for every
    /// crate without an island.
    rust_callees: Vec<RustCalleeCandidate>,
    /// Trust (2026-09-28): `(user, used)` edges, each a top-level island `def`
    /// and a declaration its kernel term names — an admitted Rust callee's `fn`
    /// item, or another top-level island `def` — both by `NodeId`. The one reader
    /// is the `dead_code` lint, which cannot see these calls: they exist only in
    /// the Clean-origin MIR, synthesized after the lint walks HIR. Exported as
    /// `ResolverGlobalCtxt::clean_origin_uses`.
    uses: Vec<(NodeId, NodeId)>,
}

impl CleanOriginMints {
    /// The empty decision: nothing minted, nothing refused. This is what every
    /// crate without a `clean { … }` island holds for the whole compilation.
    pub(crate) const fn new() -> Self {
        Self {
            granted: Vec::new(),
            refused: Vec::new(),
            nested: Vec::new(),
            rust_callees: Vec::new(),
            uses: Vec::new(),
        }
    }

    /// Trust (2026-09-28): the `(user, used)` edges, for `Resolver::into_outputs`.
    pub(crate) fn uses(&self) -> &[(NodeId, NodeId)] {
        &self.uses
    }

    /// Trust (W5): the admitted Rust callees, for `Resolver::into_outputs`.
    pub(crate) fn rust_callees(&self) -> &[RustCalleeCandidate] {
        &self.rust_callees
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

    /// Trust: every registered-but-nested `def`, for the v7/D3 diagnostics.
    pub(crate) fn nested(&self) -> &[CleanOriginNestedDef] {
        &self.nested
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
    /// Trust (W5): the AST module this island sits in (an index into
    /// [`IslandCollector::modules`]), which decides which `fn` items are its
    /// SIBLINGS. An island nested inside a block gets a fresh scope with no
    /// siblings.
    module: usize,
    content_span: Span,
    text: String,
    /// Whether the parser already reported this island. `rustc_parse`'s
    /// `trust_clean_decls_from_text` emits a Clean SYNTAX error at parse time
    /// and returns NO declarations, so an island whose text is not blank and
    /// whose payload holds no declaration at all is one the parser refused
    /// and reported. (An island of nothing but Lean comments also has no
    /// declarations, but it also has nothing the batch could reject.) Used
    /// only to avoid saying the same thing twice in two wordings — mints are
    /// refused either way.
    reported_at_parse: bool,
    /// The `def`s, which are the only declarations that can be minted.
    decls: Vec<(NodeId, Symbol, Span)>,
    /// Trust (2026-09-16): the island's top-level `namespace`/`section`/
    /// `mutual` BLOCKS — kind, name (`sym::empty` when the block has none) and
    /// extent. Never minted and never consulted by the decision: a `def`
    /// nested in one is given no Rust path, and this is where the v7/D3 note
    /// that says so points ([`CleanOriginNestedDef`]).
    blocks: Vec<(CleanDeclKind, Symbol, Span)>,
}

/// Trust (W5, SOUNDNESS 2026-09-13): why a sibling `fn` is not admissible as a
/// Clean callee — split so the v7/D3 refusal can give options matched to the
/// reason. The `Contract` variant closes a CONFIRMED false verify (see
/// [`contract_has_requires_or_ensures`] and `admissibility`).
#[derive(Clone, Debug)]
enum CalleeInadmissible {
    /// The callee's SHAPE is wrong for a Clean call: generic, `self`, a
    /// non-carrier parameter/result, `unsafe`/`async`/`extern`, or a `()`
    /// return. The carried string is the exact reason; the options offered are
    /// about carriers and visibility.
    Shape(String),
    /// The callee bears a `requires`/`ensures` contract. Its own body
    /// obligations are discharged only CONDITIONALLY on that contract (the
    /// precondition row is recorded "skipped; every caller must establish the
    /// requires contract"). The plain-Rust call path charges the precondition
    /// AT the caller; the G5 Clean-`def` call site does NOT (increment 3's
    /// `trust_check_clean_rust_callees` charge is unbuilt), so a conditional
    /// proof would become an unconditional accept. Measured 2026-09-13 on the
    /// stage1 driver: `fn safe_div(x: u64) -> u64 requires x < 10 { 100/(10-x) }`
    /// called from a Clean `def` compiled `3 proved` and then panicked with a
    /// divide-by-zero at run time; the `x - 1`/`requires x >= 1` twin returned
    /// `u64::MAX`. Refused fail-closed until the precondition is charged at the
    /// Clean call site.
    Contract,
}

/// Trust (W5, SOUNDNESS): does this AST `fn` contract carry a `requires` or
/// `ensures` clause in ANY of its storage lanes (typed `Expr`, opaque span,
/// or first-class native signature clause)?
///
/// `decreases` and the shared `declarations` are DELIBERATELY excluded: a
/// termination measure is an obligation the callee proves about ITSELF and adds
/// no caller-established assumption, and a bare declaration carries no
/// obligation at all. Only a `requires`/`ensures` makes the callee's body
/// obligations conditional on a fact the plain-Rust caller must establish and
/// the G5 lane does not, which is the exact mechanism of the false verify.
fn contract_has_requires_or_ensures(contract: &rustc_ast::FnContract) -> bool {
    contract.requires.is_some()
        || contract.ensures.is_some()
        || !contract.requires_clauses.is_empty()
        || !contract.ensures_clauses.is_empty()
        || !contract.trust_opaque_requires.is_empty()
        || !contract.trust_opaque_ensures.is_empty()
        || !contract.trust_native_requires.is_empty()
        || !contract.trust_native_ensures.is_empty()
}

/// Trust (W5): one free `fn` item seen at module level, before admission.
struct SiblingFn {
    module: usize,
    node_id: NodeId,
    name: Symbol,
    span: Span,
    /// The admissibility verdict: the carriers and constness, or the v7/D3
    /// reason it cannot be called from Clean.
    verdict: Result<(Vec<CleanCarrierTy>, CleanCarrierTy, bool), CalleeInadmissible>,
}

/// Collects `clean { … }` islands — and (W5) their sibling `fn` items — out
/// of the unexpanded crate.
struct IslandCollector {
    islands: Vec<IslandSource>,
    /// Trust (W5): one entry per AST module scope, holding its rendered path
    /// (`the crate root`, `m`, `a::b`) for diagnostics.
    modules: Vec<String>,
    /// The module scope currently being walked (an index into `modules`).
    current_module: usize,
    /// How many blocks deep the walk is. A `fn` or an island inside a block is
    /// not at module level: the `fn` is not a candidate, and the island gets
    /// a fresh scope with no siblings.
    block_depth: usize,
    /// Trust (W5): every module-level free `fn`, with its admissibility
    /// verdict.
    fns: Vec<SiblingFn>,
    /// Trust (2026-09-28): module-level names an island can SEE but can never
    /// call, with why: a `use` import, or an associated `fn` of an `impl`. Read
    /// only by the `Unknown identifier` note, which used to call each of these
    /// "not a Rust `fn` next to this island" although it is right there.
    visible_uncallable: Vec<(usize, Symbol, UncallableKind)>,
    /// Trust (2026-09-28): the modules holding a macro invocation at module
    /// level. The mint walks the ROOT fragment before expansion, so each is still
    /// a placeholder: whatever `fn` it expands to is invisible here. Read only by
    /// the `Unknown identifier` note.
    macro_modules: Vec<usize>,
}

/// Trust (2026-09-28): why a name the island can see is not a callee.
#[derive(Clone, Copy, Debug)]
enum UncallableKind {
    UseImport,
    AssociatedFn,
}

impl IslandCollector {
    fn new() -> Self {
        Self {
            islands: Vec::new(),
            modules: vec!["the crate root".to_owned()],
            current_module: 0,
            block_depth: 0,
            fns: Vec::new(),
            visible_uncallable: Vec::new(),
            macro_modules: Vec::new(),
        }
    }

    /// Trust (2026-09-28): every name a `use` tree binds, rename included.
    /// A glob binds nothing that can be named here.
    fn use_tree_names(tree: &rustc_ast::UseTree, out: &mut Vec<Symbol>) {
        match &tree.kind {
            rustc_ast::UseTreeKind::Simple(rename) => {
                if let Some(ident) = rename.or_else(|| tree.prefix.segments.last().map(|s| s.ident))
                {
                    out.push(ident.name);
                }
            }
            rustc_ast::UseTreeKind::Nested { items, .. } => {
                for item in items {
                    Self::use_tree_names(&item.inner, out);
                }
            }
            rustc_ast::UseTreeKind::Glob(..) => {}
        }
    }

    /// Trust (W5): the AST-level admissibility of a free `fn` as a Clean
    /// callee — increment 1's shape rule PLUS the soundness gate on contracts.
    ///
    /// The contract gate runs FIRST and fail-closed: a callee bearing a
    /// `requires`/`ensures` contract discharges its own body obligations only
    /// conditionally on that contract, and the G5 Clean-`def` call site does
    /// not charge the precondition (increment 3's `trust_check_clean_rust_callees`
    /// is unbuilt), so admitting it turns a conditional proof into an
    /// unconditional false accept — a CONFIRMED soundness break. See
    /// [`CalleeInadmissible::Contract`]. A contract-free callee (r18's `inc`/
    /// `dbl`) is unaffected: it has no `requires`/`ensures` clause, and its own
    /// arithmetic/panic obligations are still charged UNCONDITIONALLY when it is
    /// verified as an ordinary Rust `fn` in the whole-crate verify walk (so a
    /// contract-free callee that could panic is already refused there, not here).
    fn admissibility(
        func: &rustc_ast::Fn,
    ) -> Result<(Vec<CleanCarrierTy>, CleanCarrierTy, bool), CalleeInadmissible> {
        if let Some(contract) = &func.contract
            && contract_has_requires_or_ensures(contract)
        {
            return Err(CalleeInadmissible::Contract);
        }
        Self::admissibility_shape(func).map_err(CalleeInadmissible::Shape)
    }

    /// Trust (W5): the SHAPE half of admissibility — increment 1's exact rule.
    /// Everything outside it is refused with the reason, never widened by
    /// guessing: non-generic, no `self`, safe, non-async/gen, non-extern, every
    /// parameter and the result a single-segment `bool`/`u8`/`u16`/`u32`/`u64`.
    fn admissibility_shape(
        func: &rustc_ast::Fn,
    ) -> Result<(Vec<CleanCarrierTy>, CleanCarrierTy, bool), String> {
        if !func.generics.params.is_empty() || !func.generics.where_clause.predicates.is_empty() {
            return Err("it is generic, and a Clean island calls a function at one fixed \
                        signature"
                .to_owned());
        }
        let header = &func.sig.header;
        if matches!(header.safety, rustc_ast::Safety::Unsafe(_)) {
            return Err("it is `unsafe`, and a Clean term has no unsafe context to call it \
                        from"
                .to_owned());
        }
        if header.coroutine_marker.is_some() {
            return Err("it is `async`/`gen`, and a Clean term is a value, not a future or \
                        an iterator"
                .to_owned());
        }
        if !matches!(header.ext, rustc_ast::Extern::None) {
            return Err("it is `extern`, and a foreign ABI is outside what a Clean island \
                        can call"
                .to_owned());
        }
        let mut params = Vec::with_capacity(func.sig.decl.inputs.len());
        for (position, param) in func.sig.decl.inputs.iter().enumerate() {
            if param.is_self() {
                return Err("it takes `self`; a Clean island calls free functions only".to_owned());
            }
            let Some(carrier) = CleanCarrierTy::from_ast_carrier(&param.ty) else {
                return Err(format!(
                    "parameter {position} is not spelled as one of `bool`/`u8`/`u16`/`u32`/\
                     `u64` (a reference, a path through a module, a generic argument or any \
                     other type has no Clean carrier a call can be typed at)"
                ));
            };
            params.push(carrier);
        }
        let result = match &func.sig.decl.output {
            rustc_ast::FnRetTy::Default(_) => {
                return Err("it returns `()`, which no Clean value carries".to_owned());
            }
            rustc_ast::FnRetTy::Ty(ty) => {
                CleanCarrierTy::from_ast_carrier(ty).ok_or_else(|| {
                    "its result is not spelled as one of `bool`/`u8`/`u16`/`u32`/`u64`".to_owned()
                })?
            }
        };
        let is_const = matches!(header.constness, rustc_ast::Const::Yes(_));
        Ok((params, result, is_const))
    }
}

impl<'ast> Visitor<'ast> for IslandCollector {
    fn visit_block(&mut self, block: &'ast rustc_ast::Block) {
        self.block_depth += 1;
        visit::walk_block(self, block);
        self.block_depth -= 1;
    }

    fn visit_item(&mut self, item: &'ast Item) {
        // Trust (W5): a module opens a new sibling scope. Only a LOADED module
        // has items; an unloaded one has nothing to walk.
        if let ItemKind::Mod(_, ident, rustc_ast::ModKind::Loaded(..)) = &item.kind
            && self.block_depth == 0
        {
            let parent = self.current_module;
            let path = match self.modules[parent].as_str() {
                "the crate root" => ident.name.to_string(),
                prefix => format!("{prefix}::{}", ident.name),
            };
            self.modules.push(path);
            self.current_module = self.modules.len() - 1;
            visit::walk_item(self, item);
            self.current_module = parent;
            return;
        }
        if self.block_depth == 0 {
            match &item.kind {
                ItemKind::Use(tree) => {
                    let mut names = Vec::new();
                    Self::use_tree_names(tree, &mut names);
                    for name in names {
                        self.visible_uncallable.push((
                            self.current_module,
                            name,
                            UncallableKind::UseImport,
                        ));
                    }
                }
                ItemKind::Impl(impl_) => {
                    for assoc in &impl_.items {
                        if let rustc_ast::AssocItemKind::Fn(func) = &assoc.kind {
                            self.visible_uncallable.push((
                                self.current_module,
                                func.ident.name,
                                UncallableKind::AssociatedFn,
                            ));
                        }
                    }
                }
                ItemKind::MacCall(..) => self.macro_modules.push(self.current_module),
                _ => {}
            }
        }
        if let ItemKind::Fn(func) = &item.kind
            && self.block_depth == 0
        {
            self.fns.push(SiblingFn {
                module: self.current_module,
                node_id: item.id,
                name: func.ident.name,
                span: func.ident.span,
                verdict: Self::admissibility(func),
            });
        }
        if let ItemKind::CleanIsland(island) = &item.kind {
            // An island inside a block is not at module level: it gets a
            // scope of its own, with no siblings.
            let module = if self.block_depth == 0 {
                self.current_module
            } else {
                self.modules.push("a block".to_owned());
                self.modules.len() - 1
            };
            self.islands.push(IslandSource {
                module,
                content_span: island.content_span,
                text: island.text.to_string(),
                reported_at_parse: island.decls.is_empty()
                    && !island.text.as_str().trim().is_empty(),
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
                blocks: island
                    .decls
                    .iter()
                    .filter(|decl| {
                        matches!(
                            decl.kind,
                            CleanDeclKind::Namespace
                                | CleanDeclKind::Section
                                | CleanDeclKind::Mutual
                        )
                    })
                    .map(|decl| (decl.kind, decl.name, decl.span))
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
///
/// # A rejected batch is REPORTED here, not left to the verify pass
///
/// This seam runs the same kernel batch the verify pass runs
/// (`trust_verify.rs`'s `trust_check_clean_islands`), earlier. It used to
/// stay silent on a rejected batch on the premise that "the Clean diagnostic
/// the verify pass emits is the true explanation" — and that premise is
/// false exactly when it matters. The verify pass runs only on a front-end-
/// clean crate (`rustc_interface::passes::analysis` gates
/// `trust_ensure_whole_crate_verification` on
/// `has_errors_excluding_lint_errors`), and withholding every mint here is
/// what PRODUCES a front-end error: the `E0425` at the call site. Measured
/// on the sealed toolchain (2026-09-13): an island whose theorem failed to
/// elaborate, called from `main`, printed ONLY `E0425: cannot find function
/// min2 in module m` — no Clean diagnostic anywhere, the error naming the
/// wrong thing (ruling v7/D3, violated twice). So the batch's own
/// diagnostics are rendered right here, at the failing declaration's span,
/// with Clean's message verbatim, in the same wording the verify pass uses
/// — and every `def` in the batch gets a refusal note, so the `E0425` that
/// follows says why. The verify pass keeps its rendering for the islands
/// this seam cannot check (the deferred `trust_import_` suffix, and islands
/// a macro introduced); it never sees a batch this seam already rejected,
/// because that rejection is now a front-end error.
///
/// The batch is PARTITIONED the way the verify pass partitions it: an island
/// naming `trust_import_` — and every island after it — is checked only after
/// program admissions are minted, so it is not fed here, its `def`s get a
/// refusal note saying so, and its declarations are never reported here as
/// failures they did not yet have the chance not to be.
pub(crate) fn decide(
    sess: &rustc_session::Session,
    dcx: DiagCtxtHandle<'_>,
    fragment: &AstFragment,
) -> CleanOriginMints {
    let AstFragment::Crate(krate) = fragment else {
        return CleanOriginMints::default();
    };

    let mut collector = IslandCollector::new();
    visit::walk_crate(&mut collector, krate);
    let IslandCollector { mut islands, modules, fns, visible_uncallable, macro_modules, .. } =
        collector;
    if islands.is_empty() {
        rustc_session::trust_lean_census::resolver_inventory(sess, &[], 0);
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

    // The pre-walk batch, partitioned exactly as `trust_check_clean_islands`
    // partitions it: once an island names `trust_import_`, it and the whole
    // authored suffix after it are checked post-walk, where the program
    // admissions they name exist.
    let mut batch_islands: Vec<&IslandSource> = Vec::new();
    let mut defer_island_suffix = false;
    for island in &islands {
        // Trust (TG3): the same lexer-read predicate as the verify pass's
        // partition; a comment or a string that mentions the namespace defers
        // nothing.
        defer_island_suffix |=
            trust_certify::clean_island::island_names_kernel_import(&island.text);
        if defer_island_suffix {
            for &(_, name, span) in &island.decls {
                decision.refused.push(CleanOriginRefusal {
                    name,
                    span,
                    note: format!(
                        "`{name}` is declared in an island that is checked only after this \
                         crate's program admissions are minted (it, or an island before it, \
                         names `trust_import_`), so it is not kernel-checked in time to become \
                         callable from Rust.\n\
                         options:\n\
                         - move `{name}` into an island placed before the first island that \
                           names `trust_import_`;\n\
                         - cite `{name}` from a contract instead of calling it."
                    ),
                });
            }
            continue;
        }
        batch_islands.push(island);
    }
    // Trust: observe source attempts before mint/planner admission. Resolver
    // ordinals never share the later HIR observer's identity or environment.
    if sess.opts.unstable_opts.trust_lean_census.is_some() {
        let observed: Vec<_> = islands
            .iter()
            .map(|island| (island.content_span, island.text.as_str(), island.reported_at_parse))
            .collect();
        rustc_session::trust_lean_census::resolver_inventory(sess, &observed, batch_islands.len());
    }
    if batch_islands.is_empty() {
        return decision;
    }

    // Trust (W5): the sibling Rust callees, admitted over the AST and declared
    // in the SAME session the batch is checked in, BEFORE `check_all`.
    let (rust_callees, callee_refusals) =
        admit_rust_callees(&fns, &islands, &modules, &batch_islands);

    // Trust (TG4): the shared producer checks exactly the inventory it records.
    // The checked environment is immutable and scoped to this compiler Session.
    use trust_certify::clean_island_environment::CheckedIslandEnvironment;
    let sources: Vec<String> = batch_islands.iter().map(|island| island.text.clone()).collect();
    let declared: Vec<_> = rust_callees.iter().map(RustCalleeCandidate::to_rust_callee).collect();
    let callee_refusal = |refusal: trust_certify::clean_island::RustCalleeDeclRefusal| -> ! {
        // Every prelude collision was already filtered by `admit_rust_callees`
        // on a scratch environment, so a refusal here is a self-disagreement.
        dcx.fatal(format!(
            "internal: the Clean environment refused a Rust callee the mint admitted moments \
             earlier on the same prelude ({refusal}). Please report it."
        ));
    };
    decision.rust_callees = rust_callees;
    let callee_table: Vec<trust_clean_origin::RustCalleeRef> =
        decision.rust_callees.iter().map(RustCalleeCandidate::to_callee_ref).collect();
    let (session, batch) = if sess.opts.unstable_opts.trust_lean_census.is_some() {
        // Census has a different checking recipe. Keep its fresh path and do
        // not publish it as an ordinary checked-environment handoff.
        let mut session = trust_certify::clean_island::CleanIslandSession::new();
        session.enable_binding_reads();
        session.declare_rust_callees(&declared).unwrap_or_else(|refusal| callee_refusal(refusal));
        let source_refs: Vec<&str> = sources.iter().map(String::as_str).collect();
        let batch = session.check_all_with_census(&source_refs);
        let observed: Vec<_> = batch_islands
            .iter()
            .map(|island| (island.content_span, island.text.as_str()))
            .collect();
        rustc_session::trust_lean_census::resolver_checked(
            sess,
            &observed,
            batch.is_rejected(),
            &batch.census.as_ref().expect("requested resolver census").report,
        );
        (session, batch)
    } else {
        let (checked, session, batch) = sess
            .time("trust_clean_environment_resolver_check", || {
                // Binding reads supply pre-analysis metadata; no model check
                // or program/body-faithfulness verdict is shared here.
                //
                // Trust (TG6, `COMPILE-TIME-FACTS-1`): local kernel facts — an
                // elaboration this compiler already performed on the same
                // content is imported, not repeated. The context is the one
                // `rustc_mir_transform::clean_origin_mir::clean_facts` opens.
                let image = rustc_session::filesearch::current_dll_mapping().ok();
                let facts = trust_certify::clean_fact::FactContext::for_compiler(
                    u32::from(sess.target.pointer_width),
                    option_env!("CFG_VER_HASH").unwrap_or("unknown"),
                    image.as_ref().map(|(path, file)| {
                        let mapped = trust_certify::clean_fact::MappedImage {
                            device: file.device,
                            inode: file.inode,
                        };
                        (path.as_path(), mapped)
                    }),
                );
                CheckedIslandEnvironment::check(&sources, &declared, true, facts)
            })
            .unwrap_or_else(|refusal| callee_refusal(refusal));
        if !batch.is_rejected() && !session.is_tainted() {
            sess.time("trust_clean_environment_resolver_publish", || {
                sess.with_trust_compiler_state::<CheckedIslandEnvironment, _>(|state| {
                    *state = checked;
                });
            });
        }
        (session, batch)
    };
    if batch.is_rejected() {
        // A rejected batch is a front-end error of the two-language compiler,
        // reported HERE (see the fn docs for why the verify pass cannot be
        // relied on to do it). A partially registered environment must never
        // mint positive evidence, so nothing is granted — and every `def` the
        // user could have meant to call gets a refusal note, so the `E0425`
        // it produces names the real cause.
        report_rejected_batch(
            dcx,
            &batch_islands,
            &batch,
            &CalleeDiagnostics {
                admitted: &decision.rust_callees,
                refused: &callee_refusals,
                modules: &modules,
                visible_uncallable: &visible_uncallable,
                macro_modules: &macro_modules,
            },
        );
        for island in &batch_islands {
            for &(_, name, span) in &island.decls {
                decision.refused.push(CleanOriginRefusal {
                    name,
                    span,
                    note: format!(
                        "`{name}` is declared in this crate's Clean islands, but the crate's \
                         Clean environment — one header-first batch over every island — was \
                         rejected, and nothing from a rejected batch is minted (see the Clean \
                         island error reported above).\n\
                         options:\n\
                         - fix the declaration that error names, so the whole batch is \
                           accepted;\n\
                         - if that declaration is not needed yet, take it out of the island \
                           until it elaborates."
                    ),
                });
            }
        }
        return decision;
    }
    // Trust (temporal P3): a field binding ties a model to this crate's code,
    // and the thread census checks it. The census reads bodies before they
    // are stolen, which every MIR query must know from the start, so the
    // session learns of the bindings here, at resolve time. The census reads
    // them back (and the island text through the query system, so an edit to
    // an island reruns it).
    let bindings: Vec<rustc_session::TrustFieldBinding> = batch
        .outcomes
        .iter()
        .zip(&batch_islands)
        .flat_map(|(outcome, island)| {
            outcome.bindings.iter().map(|binding| {
                let content = island.content_span;
                let start = binding.start.min(island.text.len());
                let end = binding.end.max(start).min(island.text.len());
                let lo = content.lo() + rustc_span::BytePos(start as u32);
                let mut hi = content.lo() + rustc_span::BytePos(end as u32);
                if hi == lo && lo < content.hi() {
                    hi = lo + rustc_span::BytePos(1);
                }
                rustc_session::TrustFieldBinding {
                    name: binding.name.clone(),
                    path: binding.path.clone(),
                    arms: binding.arms.clone(),
                    carried_by: binding.carried_by.clone(),
                    span: content.with_lo(lo).with_hi(hi),
                }
            })
        })
        .collect();
    sess.trust_set_field_bindings(bindings);
    // The seals go the same way: the check that reads every body against
    // them runs before any body is stolen, which the session must know from
    // the start.
    let seals: Vec<rustc_session::TrustSeal> = batch
        .outcomes
        .iter()
        .zip(&batch_islands)
        .flat_map(|(outcome, island)| {
            outcome.seals.iter().map(|seal| {
                let content = island.content_span;
                let start = seal.start.min(island.text.len());
                let end = seal.end.max(start).min(island.text.len());
                let lo = content.lo() + rustc_span::BytePos(start as u32);
                let mut hi = content.lo() + rustc_span::BytePos(end as u32);
                if hi == lo && lo < content.hi() {
                    hi = lo + rustc_span::BytePos(1);
                }
                rustc_session::TrustSeal {
                    name: seal.name.clone(),
                    type_name: seal.type_name.clone(),
                    writers: seal.writers.clone(),
                    makers: seal.makers.clone(),
                    made_by: seal.made_by.clone(),
                    trusts: seal.trusts.clone(),
                    span: content.with_lo(lo).with_hi(hi),
                }
            })
        })
        .collect();
    sess.trust_set_seals(seals);

    let Some(env) = session.environment() else {
        return decision;
    };

    // The facet table is scratch for `admit_certified_island_definition`, which
    // needs somewhere to record the admission it mints. It is deliberately not
    // carried anywhere: this lane wants the STATUS, and the elaborator lane
    // builds its own table from its own environment.
    let mut facets = trust_spec_elab::FacetTable::new();

    // Trust (2026-09-16): the batch was ACCEPTED, so a refused sibling `fn`
    // whose bare name an island `def` elsewhere bears can no longer surface
    // through `Unknown identifier` — say so now, if an island next to it used
    // the name.
    warn_shadowed_callees(dcx, &islands, &batch_islands, &batch, env, &callee_refusals, &modules);

    // Trust (2026-09-28): which admitted Rust callees, and which other top-level
    // island `def`s, each top-level island `def` names, read from the kernel's
    // own terms (`island_declarations_naming`, as the warning above does). The
    // `dead_code` lint walks HIR, and a call that exists only in a Clean-origin
    // body is invisible to it: a Rust `fn` whose only caller is an island `def`
    // was reported "never used", so `#![deny(warnings)]` refused a valid
    // program. These edges let it follow a live island `def` to what it calls.
    // An edge is a naming, not a reachability claim. The lint still starts
    // only from what is live.
    let all_decls: Vec<(NodeId, Symbol)> = batch_islands
        .iter()
        .flat_map(|island| island.decls.iter().map(|&(node_id, name, _)| (node_id, name)))
        .collect();
    for (index, island) in batch_islands.iter().enumerate() {
        let Some(outcome) = batch.outcomes.get(index) else { continue };
        let targets = decision
            .rust_callees
            .iter()
            .map(|callee| (callee.node_id, callee.name))
            .chain(all_decls.iter().copied());
        for (used, name) in targets {
            let users = trust_certify::clean_island::island_declarations_naming(
                env,
                &outcome.registered,
                name.as_str(),
            );
            if std::env::var_os("TRUST_CLEAN_USES_TRACE").is_some() {
                eprintln!("[CLEAN_USES] target={name} users={users:?}");
            }
            for &(user, decl, _) in &island.decls {
                if user != used && users.iter().any(|u| u.as_str() == decl.as_str()) {
                    decision.uses.push((user, used));
                }
            }
        }
    }

    for (index, island) in batch_islands.iter().enumerate() {
        // Trust (2026-09-16, ruling v7/D3): every `def` this island registered
        // from inside a `namespace`/`section`/`mutual` block. Never a mint
        // candidate (only `island.decls`, the top-level `def`s, are), so this
        // changes no decision; it records why the call site finds nothing.
        if let Some(outcome) = batch.outcomes.get(index) {
            let top_level: Vec<&str> =
                island.decls.iter().map(|(_, name, _)| name.as_str()).collect();
            for nested in
                trust_clean_origin::nested_island_definitions(env, &outcome.registered, &top_level)
            {
                let trust_clean_origin::MintRefusal::NotTopLevel {
                    name: bare,
                    clean_name,
                    namespace,
                    ..
                } = &nested
                else {
                    continue;
                };
                // No enclosing BLOCK of this island accounts for the name: it
                // is not a nested `def` the author wrote here (an elaborator
                // auxiliary, or a namespace another island opened), and a note
                // claiming a block would be a guess. Stay silent.
                let Some(block_span) = nested_block_span(island, namespace.as_deref()) else {
                    continue;
                };
                decision.nested.push(CleanOriginNestedDef {
                    name: Symbol::intern(bare),
                    namespace: namespace
                        .as_deref()
                        .map(|path| path.split('.').map(Symbol::intern).collect())
                        .unwrap_or_default(),
                    clean_name: clean_name.clone(),
                    span: block_span,
                    note: nested.note(),
                });
            }
        }
        for &(node_id, name, span) in &island.decls {
            let name_str = name.as_str();
            // Trust: AST names are source spelling; quoted dots are one component.
            let declaration = match trust_certify::clean_island::island_source_name(name_str) {
                Ok(name) => name,
                Err(note) => {
                    decision.refused.push(CleanOriginRefusal { name, span, note });
                    continue;
                }
            };

            // Precondition 1: the kernel re-checked this declaration. The
            // verdict is only TAKEN here; it is read below, after the
            // registered-constant check, so a declaration the environment
            // does not hold keeps its own, more specific note.
            let admission = trust_certify::clean_island::admit_certified_island_definition_for_name(
                env,
                &declaration,
                &mut facets,
            );

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
            let Some(constant) = env.get_const(&declaration) else {
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
            // Trust (2026-09-16, ruling v7/D3): a refused admission is refused
            // HERE, carrying the admitter's own reason. This arm used to be
            // `Err(_) => KernelStatus::Parsed`, "fail-closed to the weakest
            // status" — which is fail-closed, and which also made `decide_mint`
            // report a declaration the batch had ACCEPTED as a merely `parsed`
            // symbol and advise removing a `sorry` that was not there.
            // Measured: `def sfst (a : Int64) (b : Int64) : Int64 := a` is
            // registered and reported "kernel-checked", and its real refusal
            // is the admitter's "is universe-polymorphic". Exactly as closed as
            // before — the refusal still mints nothing — and no status is
            // fabricated to get there.
            let status: trust_symbols::KernelStatus = match admission {
                Ok(admission) => admission.status().clone(),
                Err(reason) => {
                    decision.refused.push(CleanOriginRefusal {
                        name,
                        span,
                        note: trust_clean_origin::MintRefusal::CertifiedAdmissionRefused {
                            name: name_str.to_owned(),
                            reason,
                            // Both refusals, when the signature has one too:
                            // the admitter speaks in kernel terms, and the
                            // carrier lane names the offending type.
                            carrier: trust_clean_carrier::carrier_signature_for(&constant.type_)
                                .err()
                                .map(|refusal| refusal.to_string()),
                            // An undeclared type NAME is auto-bound as a type
                            // variable; the note says so when the kernel type
                            // shows one.
                            type_variable_binders:
                                trust_clean_origin::leading_type_variable_binders(&constant.type_),
                        }
                        .note(),
                    });
                    continue;
                }
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
            let plan = match trust_clean_origin::plan_clean_origin_body_with_rust_callees_for_name(
                env,
                &declaration,
                &callee_table,
            ) {
                Ok(plan) => plan,
                Err(refusal) => {
                    decision.refused.push(CleanOriginRefusal { name, span, note: refusal.note() });
                    continue;
                }
            };
            // Trust (W5): `const` iff every Rust callee the body calls is
            // `const fn` in its own header. A def that calls no Rust keeps
            // the kernel language's constness.
            let is_const = match plan.shape() {
                trust_clean_origin::CleanOriginShape::RustCallChain { nodes } => nodes
                    .iter()
                    .all(|node| decision.rust_callees.get(node.callee).is_some_and(|c| c.is_const)),
                _ => true,
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

            decision
                .granted
                .push((node_id, CleanOriginMint { name, span, params, result, is_const }));
        }
    }

    decision
}

/// Render a rejected pre-walk batch: dependency cycles, then every island's
/// failures at their declaration spans (Clean's message verbatim), then the
/// registered-declaration note for each island that was accepted alongside
/// a rejected sibling.
///
/// Wording and span arithmetic are those of `trust_verify.rs`'s
/// `trust_check_clean_islands`, on purpose: the two seams check the same
/// batch, and a user must not be able to tell from the diagnostic which one
/// happened to report it. (They cannot share a function: `rustc_resolve`
/// and `rustc_mir_transform` do not depend on each other, and the renderer
/// needs `rustc_errors`, which `trust-certify` does not link.)
/// Trust (W5): decide which sibling `fn`s become Clean callees — increment
/// 1's VISIBILITY/IDENTITY rule, over the AST alone.
///
/// A `fn` is a CANDIDATE iff it is a free item at module level in a module
/// that holds at least one island of the pre-walk batch (it is then a
/// sibling of that island). A candidate is ADMITTED iff its AST verdict is
/// `Ok` and, because Clean sees ONE crate-wide namespace:
///
/// * no other admissible candidate in another module bears the same bare
///   name — otherwise ALL bearers are refused (ambiguous);
/// * no island `def` in ANOTHER module bears the name — a candidate that
///   would shadow it is refused (ambiguous). A `def` in the SAME module is
///   not decided here: the def mints, the `fn` collides with it, and the
///   ordinary `E0428` parity rule reports it;
/// * the Clean prelude does not already hold the name — probed by declaring
///   the candidate on a SCRATCH prelude environment (`DuplicateName`), so the
///   real session never sees a callee it would refuse.
///
/// Returns the admitted candidates (deterministic order: module, then span)
/// and every refusal with its v7/D3 note, for the `Unknown identifier`
/// diagnostics.
fn admit_rust_callees(
    fns: &[SiblingFn],
    islands: &[IslandSource],
    modules: &[String],
    batch_islands: &[&IslandSource],
) -> (Vec<RustCalleeCandidate>, Vec<RustCalleeRefusal>) {
    use std::collections::{BTreeMap, BTreeSet};

    let island_modules: BTreeSet<usize> =
        batch_islands.iter().map(|island| island.module).collect();
    let mut refusals = Vec::new();
    // The fresh prelude environment: the prelude probe below declares on a
    // scratch copy of it, and the shadowing rule asks it which names it holds.
    let prelude = trust_certify::clean_island::CleanIslandSession::new()
        .environment()
        .cloned()
        .expect("a fresh session is untainted");
    let prelude_holds =
        |name: Symbol| prelude.get_const(&clean_kernel::Name::from_string(name.as_str())).is_some();

    // Every island `def` name, by module — the shadowing rule reads it.
    let mut def_modules: BTreeMap<Symbol, BTreeSet<usize>> = BTreeMap::new();
    for island in islands {
        for &(_, name, _) in &island.decls {
            def_modules.entry(name).or_default().insert(island.module);
        }
    }

    // Trust (2026-09-16, silent-precedence hazard): an island `def` in ANOTHER
    // module bearing a refused `fn`'s bare name. The `fn` is refused for its
    // own reason below, but an island beside it that writes the name still
    // gets that `def` — silently — so the refusal records it for
    // [`warn_shadowed_callees`]. A `def` in the `fn`'s OWN module is the
    // `E0428` parity rule's business, not this one's. Failing that, a prelude
    // constant of the same name wins the name, just as silently.
    let shadowed_by = |func: &SiblingFn| -> Option<ShadowedCallee> {
        let foreign: Vec<usize> = def_modules
            .get(&func.name)
            .into_iter()
            .flatten()
            .copied()
            .filter(|&module| module != func.module)
            .collect();
        let owner = if !foreign.is_empty() {
            ShadowOwner::IslandDefs(foreign)
        } else if prelude_holds(func.name) {
            ShadowOwner::Prelude
        } else {
            return None;
        };
        Some(ShadowedCallee { fns: vec![(func.module, func.span)], owner })
    };

    // 1. the AST verdict, per candidate.
    let mut admissible: Vec<&SiblingFn> = Vec::new();
    for func in fns.iter().filter(|func| island_modules.contains(&func.module)) {
        match &func.verdict {
            Ok(_) => admissible.push(func),
            Err(CalleeInadmissible::Shape(reason)) => refusals.push(RustCalleeRefusal {
                name: func.name,
                note: format!(
                    "`{}` is visible from the island but not callable from Clean: {reason}.\n\
                     options:\n\
                     - add a sibling `fn` wrapper at a carrier type (`bool`/`u8`/`u16`/`u32`/\
                       `u64` parameters and result) and call that;\n\
                     - move `{}` into this module, if it is the wrong one that is visible;\n\
                     - cite it from a contract instead of calling it.",
                    func.name, func.name
                ),
                shadowed: shadowed_by(func),
            }),
            // Trust (W5, SOUNDNESS 2026-09-13): a `requires`/`ensures` callee
            // is refused fail-closed — its precondition is not charged at a
            // Clean `def` call site, so the obligations it proves only under
            // its contract would be accepted unconditionally. See
            // `CalleeInadmissible::Contract`.
            Err(CalleeInadmissible::Contract) => refusals.push(RustCalleeRefusal {
                name: func.name,
                note: format!(
                    "`{name}` has a `requires`/`ensures` contract and cannot yet be called \
                     from a Clean `def`: its precondition is not charged at the Clean call \
                     site, so the obligations `{name}` proves only UNDER its contract would be \
                     accepted unconditionally — a soundness gap.\n\
                     options:\n\
                     - remove the contract and rely on `{name}`'s own body obligations \
                       (a contract-free `fn` is verified unconditionally at the Clean call \
                       site);\n\
                     - wrap `{name}` in a contract-free sibling `fn` and call that from Clean;\n\
                     - call `{name}` only from Rust, where its precondition IS charged at the \
                       call site.",
                    name = func.name
                ),
                shadowed: shadowed_by(func),
            }),
        }
    }

    // 2. the one-namespace rules.
    let mut by_name: BTreeMap<Symbol, Vec<&SiblingFn>> = BTreeMap::new();
    for func in &admissible {
        by_name.entry(func.name).or_default().push(func);
    }
    let mut survivors: Vec<RustCalleeCandidate> = Vec::new();
    for (name, bearers) in by_name {
        let modules_of = |ids: &[usize]| -> String {
            ids.iter().map(|&id| format!("`{}`", modules[id])).collect::<Vec<_>>().join(" and ")
        };
        let bearer_modules: Vec<usize> = bearers.iter().map(|f| f.module).collect();
        // Trust (W5, measured 2026-09-13): a candidate whose OWN module holds an
        // island `def` of the same name is not a callee at all — declaring it
        // in the environment before the island elaborates made the kernel
        // refuse the whole batch ("Duplicate declaration: f") and silenced the
        // `E0428` parity rule the fixtures `clean_origin_parity_collision` and
        // `clean_unit_rust_collision` pin. Drop it silently: the def mints,
        // the `fn` collides with it, and `E0428` reports the collision.
        if bearers.iter().any(|f| def_modules.get(&name).is_some_and(|set| set.contains(&f.module)))
        {
            continue;
        }
        let foreign_defs: Vec<usize> = def_modules
            .get(&name)
            .map(|set| set.iter().copied().filter(|m| !bearer_modules.contains(m)).collect())
            .unwrap_or_default();
        if bearers.len() > 1 || !foreign_defs.is_empty() {
            let mut where_ = format!("declared as `fn` in {}", modules_of(&bearer_modules));
            if !foreign_defs.is_empty() {
                where_.push_str(&format!(" and as island `def` in {}", modules_of(&foreign_defs)));
            }
            refusals.push(RustCalleeRefusal {
                name,
                note: format!(
                    "Clean sees one namespace: `{name}` is {where_}.\n\
                     options:\n\
                     - rename one of them;\n\
                     - give the callee a distinct bare name;\n\
                     - cite from proof position instead of calling."
                ),
                // Trust: only a FOREIGN `def` makes the refusal silent — two
                // bare `fn` bearers leave the name unresolved, and the island
                // gets its `Unknown identifier` with this note attached.
                shadowed: if !foreign_defs.is_empty() {
                    Some(ShadowedCallee {
                        fns: bearers.iter().map(|f| (f.module, f.span)).collect(),
                        owner: ShadowOwner::IslandDefs(foreign_defs.clone()),
                    })
                } else if prelude_holds(name) {
                    Some(ShadowedCallee {
                        fns: bearers.iter().map(|f| (f.module, f.span)).collect(),
                        owner: ShadowOwner::Prelude,
                    })
                } else {
                    None
                },
            });
            continue;
        }
        let func = bearers[0];
        let Ok((params, result, is_const)) = &func.verdict else { continue };
        survivors.push(RustCalleeCandidate {
            node_id: func.node_id,
            name,
            params: params.clone(),
            result: *result,
            is_const: *is_const,
            span: func.span,
        });
    }

    // 3. the prelude probe, on a scratch environment. Deterministic order:
    // module, then span, so the callee table (and every diagnostic that lists
    // it) is stable.
    survivors.sort_by_key(|c| (c.module_of(fns), c.span.lo()));
    let mut scratch = prelude.clone();
    let mut admitted = Vec::with_capacity(survivors.len());
    for candidate in survivors {
        match trust_certify::clean_island::declare_rust_callees(
            &mut scratch,
            &[candidate.to_rust_callee()],
        ) {
            Ok(()) => admitted.push(candidate),
            Err(refusal) => refusals.push(RustCalleeRefusal {
                name: candidate.name,
                note: format!(
                    "Clean sees one namespace: `{}` is declared as `fn` here and already held \
                     by the Clean environment ({}).\n\
                     options:\n\
                     - rename the `fn`;\n\
                     - give the callee a distinct bare name;\n\
                     - cite from proof position instead of calling.",
                    candidate.name, refusal.reason
                ),
                // The name resolves in the island all the same, to what holds
                // it; say so wherever an island uses it.
                shadowed: prelude_holds(candidate.name).then(|| ShadowedCallee {
                    fns: vec![(candidate.module_of(fns), candidate.span)],
                    owner: ShadowOwner::Prelude,
                }),
            }),
        }
    }
    (admitted, refusals)
}

impl RustCalleeCandidate {
    /// The module index of the `fn` this candidate was read from, for the
    /// deterministic table order.
    fn module_of(&self, fns: &[SiblingFn]) -> usize {
        fns.iter().find(|f| f.node_id == self.node_id).map_or(usize::MAX, |f| f.module)
    }
}

/// Trust (W5): what the rejected-batch renderer needs to say WHY an island
/// could not name a Rust `fn` (ruling v7/D3).
struct CalleeDiagnostics<'a> {
    admitted: &'a [RustCalleeCandidate],
    refused: &'a [RustCalleeRefusal],
    modules: &'a [String],
    /// Trust (2026-09-28): see [`IslandCollector::visible_uncallable`].
    visible_uncallable: &'a [(usize, Symbol, UncallableKind)],
    /// Trust (2026-09-28): see [`IslandCollector::macro_modules`].
    macro_modules: &'a [usize],
}

impl CalleeDiagnostics<'_> {
    /// The note for an `Unknown identifier: <name>` in an island of `module`:
    /// the recorded refusal if `name` was a refused candidate, else the
    /// ABSENT note with the design's options.
    fn unknown_identifier_note(&self, name: &str, module: usize) -> String {
        if let Some(refusal) = self.refused.iter().find(|r| r.name.as_str() == name) {
            return refusal.note.clone();
        }
        // Trust (2026-09-28): the design's "Not admissible" note
        // (docs/design/2026-09-13-lean-calls-rust-lane.md, Diagnostics) for a name
        // the island CAN see. It used to get the "absent" note below, which says
        // the `fn` is not there when it is.
        if let Some(&(_, _, kind)) = self
            .visible_uncallable
            .iter()
            .find(|(m, visible, _)| *m == module && visible.as_str() == name)
        {
            let reason = match kind {
                UncallableKind::UseImport => {
                    "it is brought into this module by a `use` import, and only a free `fn` \
                     defined in the island's own module is callable from Clean"
                }
                UncallableKind::AssociatedFn => {
                    "it is an associated `fn` of an `impl` block, and only a free `fn` is \
                     callable from Clean"
                }
            };
            return format!(
                "`{name}` is visible from the island but not callable from Clean: {reason}.\n\
                 options:\n\
                 - add a sibling free `fn` wrapper at a carrier type (`bool`/`u8`/`u16`/`u32`/\
                   `u64` parameters and result) that calls it, and call that;\n\
                 - move `{name}` into this module as a free `fn`;\n\
                 - cite it from a contract instead of calling it."
            );
        }
        let mut note = format!(
            "`{name}` is not a Rust `fn` next to this island (no free `fn {name}` in {}).\n\
             options:\n\
             - define `fn {name}(..)` in the same module as the island, with `u8`/`u16`/`u32`/\
               `u64`/`bool` parameters and result;\n\
             - or declare it in Clean (`def {name} …`).",
            self.modules.get(module).map_or("this module", String::as_str)
        );
        if self.macro_modules.contains(&module) {
            note.push_str(&format!(
                "\nThis module also holds a macro invocation. The island is checked before \
                 macros expand, so a `fn` a macro generates is not callable from Clean. If \
                 `{name}` is one, call it from a plain sibling `fn` wrapper instead."
            ));
        }
        note
    }

    /// The note for any OTHER elaboration failure in an island that can see
    /// Rust callees: the callees and their carriers, so a wrong-carrier
    /// application (`Type mismatch: expected UInt32, got …`) says which `fn`
    /// takes what where. The exact position of the mismatched application is
    /// not recoverable from the elaborator's message, so every callee is
    /// listed.
    fn carrier_context_note(&self, decl: &str) -> Option<String> {
        if self.admitted.is_empty() {
            return None;
        }
        let rows: Vec<String> = self
            .admitted
            .iter()
            .map(|callee| {
                let positions: Vec<String> = callee
                    .params
                    .iter()
                    .enumerate()
                    .map(|(i, c)| format!("`{}` in position {i}", rust_carrier_name(*c)))
                    .collect();
                format!(
                    "`fn {}` takes {} and returns `{}`",
                    callee.name,
                    if positions.is_empty() {
                        "no parameters".to_owned()
                    } else {
                        positions.join(", ")
                    },
                    rust_carrier_name(callee.result)
                )
            })
            .collect();
        Some(format!(
            "`{decl}` is checked against the Rust callees declared for this island — {}. \
             Applying one at a different carrier than its `fn` takes is the Clean error \
             reported above.\n\
             options:\n\
             - restate the callee at the carrier `{decl}` uses;\n\
             - restate `{decl}` at the callee's carrier;\n\
             - wrap the callee in a sibling `fn` at the carrier the island uses.",
            rows.join("; ")
        ))
    }
}

/// The Rust spelling of a carrier, for the callee notes.
fn rust_carrier_name(carrier: CleanCarrierTy) -> &'static str {
    match carrier {
        CleanCarrierTy::Bool => "bool",
        CleanCarrierTy::U8 => "u8",
        CleanCarrierTy::U16 => "u16",
        CleanCarrierTy::U32 => "u32",
        CleanCarrierTy::U64 => "u64",
        CleanCarrierTy::Nat => "trust_bignum::Nat",
    }
}

/// The declaration an elaborator "`<name>` did not elaborate: …" message
/// names, when it names one.
fn decl_named_in(message: &str) -> Option<&str> {
    let start = message.find('`')? + 1;
    let rest = &message[start..];
    let end = rest.find('`')?;
    rest[end..].starts_with("` did not elaborate").then_some(&rest[..end])
}

/// The identifier an elaborator `Unknown identifier: <name>…` message names.
fn unknown_identifier_in(message: &str) -> Option<&str> {
    let rest = message.split("Unknown identifier: ").nth(1)?;
    let end = rest
        .char_indices()
        .find(|(_, c)| !(c.is_alphanumeric() || *c == '_' || *c == '.' || *c == '\''))
        .map_or(rest.len(), |(i, _)| i);
    (end > 0).then(|| &rest[..end])
}

/// Trust (2026-09-16): where a [`CleanOriginNestedDef`] note points — the
/// enclosing top-level block of the island's parse-time payload — or `None`
/// when no block of THIS island accounts for the declaration, in which case
/// nothing is recorded and the call site keeps its ordinary error.
/// Diagnostics only.
///
/// A namespaced declaration (`Geo.area`) is matched to a `namespace` block by
/// name: its namespace IS the block's name, or continues it (`namespace A`
/// holding `namespace B`). A declaration whose name is unqualified was nested
/// in a block that does not qualify names, so it is matched to the island's
/// first `section`/`mutual` block.
fn nested_block_span(island: &IslandSource, namespace: Option<&str>) -> Option<Span> {
    match namespace {
        Some(namespace) => island.blocks.iter().find_map(|&(kind, name, span)| {
            let name = name.as_str();
            (kind == CleanDeclKind::Namespace
                && !name.is_empty()
                && (namespace == name
                    || namespace.strip_prefix(name).is_some_and(|rest| rest.starts_with('.'))))
            .then_some(span)
        }),
        None => island.blocks.iter().find_map(|&(kind, _, span)| {
            matches!(kind, CleanDeclKind::Section | CleanDeclKind::Mutual).then_some(span)
        }),
    }
}

/// Trust (2026-09-16, SILENT-PRECEDENCE HAZARD): warn when an island next to a
/// refused sibling `fn` USED the contested bare name, which — Clean seeing one
/// crate-wide namespace — meant the island `def` of ANOTHER module.
///
/// [`admit_rust_callees`] refuses a sibling `fn` whose bare name an island
/// `def` elsewhere bears, and records the "Clean sees one namespace" note. That
/// note rides on `Unknown identifier`, and here the identifier is KNOWN: it
/// resolves to the `def`. Measured on probes 16c/16g: `mod a { clean { def inc
/// … := x + 2 } }`, a root `fn inc` (`x + 1`) and a root island
/// `def twice_inc … := inc (inc x)` compiled clean in either source order and
/// computed with the Clean `inc`; the only output was `function inc is never
/// used`. Coherent with the kernel term, so not unsound — and different
/// arithmetic from the function written beside the island, silently.
///
/// A WARNING, not an error, deliberately. The design of record
/// (`docs/design/2026-09-13-lean-calls-rust-lane.md`, VISIBILITY/IDENTITY)
/// rules that such a name REFUSES THE `fn` BEARERS; it does not rule the
/// program ill-formed, and a cross-module Clean call is a sanctioned shape
/// (`clean_symbol_graph_forward_reference.rs`). An error here would reject a
/// crate whose author meant exactly the Clean `def`. Nothing is weakened
/// either way: the `fn` stays refused, the batch stays as checked.
///
/// Trust (2026-09-28): the same hazard with a PRELUDE constant as the holder
/// ([`ShadowOwner::Prelude`]). A sibling `fn id`/`fn not` is refused by the
/// prelude probe, and an island beside it that writes `id x` computes with the
/// prelude's `id`: measured `call_id(5) = 5` against the Rust `id(5) = 6`, with
/// no output at all. A warning for the same reason: `id` meaning the prelude's
/// `id` is ordinary Lean.
///
/// Fires only on USE, read from the kernel's own terms
/// (`island_declarations_naming`), never on a name coincidence alone: a root
/// `fn inc` and an `a::inc` island `def` that no neighbouring island mentions
/// are two unrelated Rust paths.
fn warn_shadowed_callees(
    dcx: DiagCtxtHandle<'_>,
    islands: &[IslandSource],
    batch_islands: &[&IslandSource],
    batch: &trust_certify::clean_island_batch::CleanIslandBatch,
    env: &clean_kernel::Environment,
    refusals: &[RustCalleeRefusal],
    modules: &[String],
) {
    for refusal in refusals {
        let Some(shadowed) = &refusal.shadowed else { continue };
        let name = refusal.name;
        for (index, island) in batch_islands.iter().enumerate() {
            // Only an island that is a SIBLING of a refused bearer could have
            // meant that `fn`.
            let sibling_fns: Vec<Span> = shadowed
                .fns
                .iter()
                .filter(|(module, _)| *module == island.module)
                .map(|&(_, span)| span)
                .collect();
            if sibling_fns.is_empty() {
                continue;
            }
            let Some(outcome) = batch.outcomes.get(index) else { continue };
            let users = trust_certify::clean_island::island_declarations_naming(
                env,
                &outcome.registered,
                name.as_str(),
            );
            if users.is_empty() {
                continue;
            }
            // Point at the first using declaration when it is a top-level
            // `def` (the only declarations whose spans the payload carries),
            // else at the island.
            let at = island
                .decls
                .iter()
                .find(|(_, decl, _)| users.iter().any(|user| user.as_str() == decl.as_str()))
                .map_or(island.content_span, |&(_, _, span)| span);
            let (holder, computes_with) = match &shadowed.owner {
                ShadowOwner::IslandDefs(def_modules) => {
                    let def_modules: Vec<String> = def_modules
                        .iter()
                        .map(|&module| format!("`{}`", modules[module]))
                        .collect();
                    (
                        format!(
                            "the island `def {name}` declared in {}",
                            def_modules.join(" and ")
                        ),
                        format!("the Clean `def {name}`"),
                    )
                }
                ShadowOwner::Prelude => {
                    (format!("the Clean prelude's `{name}`"), format!("the prelude's `{name}`"))
                }
            };
            let mut diagnostic = dcx.struct_span_warn(
                at,
                format!(
                    "`{name}` in this Clean island names {holder}, NOT the sibling Rust `fn {name}`"
                ),
            );
            for span in sibling_fns {
                diagnostic = diagnostic.with_span_label(
                    span,
                    format!("this `fn {name}` was not declared to Clean, so `{name}` is not it"),
                );
            }
            if let ShadowOwner::IslandDefs(def_modules) = &shadowed.owner {
                for other in islands.iter().filter(|other| def_modules.contains(&other.module)) {
                    for &(_, decl, span) in &other.decls {
                        if decl == name {
                            diagnostic = diagnostic.with_span_label(
                                span,
                                format!("`{name}` resolves to this Clean `def`"),
                            );
                        }
                    }
                }
            }
            diagnostic
                .with_note(format!(
                    "{} {} kernel-checked — and any code emitted for {} computes — with \
                     {computes_with}, not with the Rust `fn {name}` written next to the island",
                    users.iter().map(|user| format!("`{user}`")).collect::<Vec<_>>().join(", "),
                    if users.len() == 1 { "was" } else { "were" },
                    if users.len() == 1 { "it" } else { "them" },
                ))
                // The recorded refusal, verbatim: the rule, where the two
                // bearers are, and the options.
                .with_note(refusal.note.clone())
                .emit();
        }
    }
}

fn report_rejected_batch(
    dcx: DiagCtxtHandle<'_>,
    islands: &[&IslandSource],
    batch: &trust_certify::clean_island_batch::CleanIslandBatch,
    callees: &CalleeDiagnostics<'_>,
) {
    // Island-relative byte offsets onto rustc coordinates; identical to the
    // parser's and the verify pass's remap, so a parse-time span, a
    // resolve-time span and a kernel-time span all point at the same bytes.
    let remap = |island: &IslandSource, start: usize, end: usize| -> Span {
        let text = &island.text;
        let start = start.min(text.len());
        let end = end.max(start).min(text.len());
        let lo = island.content_span.lo() + BytePos(start as u32);
        let mut hi = island.content_span.lo() + BytePos(end as u32);
        if hi == lo && lo < island.content_span.hi() {
            hi = lo + BytePos(1);
        }
        island.content_span.with_lo(lo).with_hi(hi)
    };

    for cycle in &batch.cycles {
        let Some(primary) = cycle.sites.first() else { continue };
        let site_span = |site: &trust_certify::clean_island_batch::CleanIslandCycleSite| {
            remap(islands[site.island], site.start, site.end)
        };
        let mut diagnostic = dcx.struct_span_err(
            site_span(primary),
            format!("Clean declarations form a dependency cycle: {}", cycle.render()),
        );
        for site in cycle.sites.iter().skip(1) {
            diagnostic = diagnostic
                .with_span_label(site_span(site), format!("`{}` closes the cycle", site.name));
        }
        diagnostic
            .with_note(
                "declaration headers are collected across every Clean island before any body \
                 is registered, so this cycle is found structurally rather than by the kernel \
                 diverging; nothing from these islands was registered",
            )
            .with_note(cycle.message.clone())
            .emit();
    }

    for (index, outcome) in batch.outcomes.iter().enumerate() {
        let island = islands[index];
        if outcome.is_rejected() {
            if island.reported_at_parse {
                // The parser already refused this island's syntax at the
                // exact position; the batch's re-parse would say the same
                // thing in different words.
                continue;
            }
            for err in &outcome.errors {
                let span = remap(island, err.start, err.end);
                // Trust: a rejected batch may fail before any declaration reaches
                // the kernel. Name the reporting phase without claiming a re-check.
                let mut diagnostic = dcx.struct_span_err(span, err.message.clone()).with_note(
                    "the Clean island was rejected during resolver checking \
                         (two-language design E10)",
                );
                // Trust (W5, ruling v7/D3): an island that could not name a
                // Rust `fn` is told why, with options.
                if let Some(name) = unknown_identifier_in(&err.message) {
                    diagnostic =
                        diagnostic.with_note(callees.unknown_identifier_note(name, island.module));
                } else if let Some(decl) =
                    decl_named_in(&err.message).map(str::to_owned).or_else(|| {
                        island
                            .decls
                            .iter()
                            .find(|(_, _, decl_span)| {
                                decl_span.contains(span) || span.contains(*decl_span)
                            })
                            .map(|(_, name, _)| name.to_string())
                    })
                    && let Some(note) = callees.carrier_context_note(&decl)
                {
                    diagnostic = diagnostic.with_note(note);
                }
                diagnostic.emit();
            }
        } else if !outcome.registered.is_empty() {
            dcx.struct_span_note(
                island.content_span,
                format!(
                    "Clean island kernel-checked: {} declaration(s) registered ({})",
                    outcome.registered.len(),
                    outcome.registered.join(", ")
                ),
            )
            .emit();
        }
        // Trust (2026-09-16, GREEN THAT LIES): an accepted island whose
        // `import` Clean's built-in prelude stand-in served says so, in the
        // verify pass's exact words (`trust_disclose_island_standin_imports`)
        // — both seams render the same batch. Empty for a rejected island.
        for import in &outcome.standin_imports {
            dcx.struct_span_note(remap(island, import.start, import.end), import.disclosure())
                .with_note(import.options())
                .emit();
        }
    }
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
                let CleanOriginMints { granted, refused, .. } = &mut self.clean_origin_mints;
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
            // Trust (2026-09-16): not a refused top-level `def` — but it may be
            // a `def` the island declared inside a block (`m::area` over
            // `namespace Geo def area … end Geo`), which was never a mint
            // candidate at all and used to get a bare `E0425`.
            if let Some(nested) =
                self.clean_origin_mints.nested().iter().find(|n| n.name == last.ident.name)
            {
                Self::trust_note_clean_origin_nested(err, nested);
            }
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

    /// Trust (2026-09-16, ruling v7/D3): the `E0433` twin of
    /// [`Self::trust_note_clean_origin_refusal`], for a path that walks THROUGH
    /// a Clean namespace as if it were a Rust module — `m::Geo::area` over
    /// `namespace Geo def area … end Geo`, which fails at `Geo` and used to say
    /// only "cannot find `Geo` in `m`".
    ///
    /// Called by late resolution AFTER it has merged the failed-to-resolve
    /// error over the typo-suggestion error: that merge REPLACES the
    /// diagnostic's children, so a note added any earlier (by the `E0425` hook,
    /// which does run on the prefix path) is discarded.
    ///
    /// Narrow on purpose: the last segment must be the nested `def`'s bare name
    /// AND an earlier segment must be a component of its Clean namespace. An
    /// unrelated unresolved module that happens to end in the same bare name
    /// stays an ordinary `E0433`.
    pub(crate) fn trust_note_clean_origin_namespace_path(
        &self,
        err: &mut rustc_errors::Diag<'_>,
        path: &[crate::Segment],
    ) {
        let Some((last, prefix)) = path.split_last() else { return };
        let Some(nested) = self.clean_origin_mints.nested().iter().find(|n| {
            n.name == last.ident.name
                && prefix.iter().any(|segment| n.namespace.contains(&segment.ident.name))
        }) else {
            return;
        };
        Self::trust_note_clean_origin_nested(err, nested);
    }

    /// Trust: the shared rendering of a [`CleanOriginNestedDef`] — where the
    /// declaration is, then `MintRefusal::NotTopLevel`'s note verbatim.
    fn trust_note_clean_origin_nested(
        err: &mut rustc_errors::Diag<'_>,
        nested: &CleanOriginNestedDef,
    ) {
        err.span_note(
            nested.span,
            format!(
                "`{}` is declared here, inside a block of this `clean {{ … }}` island, so it \
                 was given no Rust path",
                nested.clean_name
            ),
        );
        err.note(nested.note.clone());
    }
}
