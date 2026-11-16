//! Trust (spawn census plan step P4, design
//! `docs/design/2026-09-29-spawn-census-by-construction.md` §5.2, §5.7, §10 step 6): the
//! census's TRUST-IR LANE, its SHADOW differential against the MIR lane, and the report the
//! scoreboard (`scripts/spawn_census_shadow_scoreboard.py`) reads.
//!
//! # Shadow only
//!
//! Until the flip (§5.7) the MIR lane (`trust_mir_extract::concurrency_effects`) decides every
//! verdict and row a user sees. This lane runs only under `-Ztrust-spawn-census-shadow`
//! (default off, and then nothing here runs and no THIR is retained for it); it emits no row,
//! changes no verdict and grants nothing. What it computes is compared with the MIR lane's
//! answer, per fn-like local body, and printed.
//!
//! # Input
//!
//! `trust_ir_of(def)` for every fn-like local body the MIR lane answers for: the direct
//! producer's per-body module, the projection of its callee ledger and what the producer knows
//! the module does not carry (`TrustIrBody`). A per-body module names its callees by dense
//! body-local ids (`functions[0]` is the body; `1..` are callees no function of the module
//! holds), so the ledger is what turns an id into a definition. There is no crate-level module
//! with dep-graph identity: the producer's assembled crate module is session state, and its
//! declarations keep no definition identity (`crate_module.rs`, frozen). Anything the input
//! does not state is UNKNOWN, never QUIET.
//!
//! # Only the program is read
//!
//! A module is read as the program only if the producer's own effect-conservation check
//! (`effect_conservation`, D28) finds it is: every effect of rustc's built MIR paired in the
//! module, and no value abstraction (an `undef`, an enum collapsed to a lone `bool` or `()`, a
//! union or enum-parameter placeholder). A callable in an `Option<fn()>` payload lowered as a
//! lone `bool` is a CREATE the module does not hold, so such a body is [`Gap::Abstracted`],
//! and one with an unpaired effect [`Gap::NotConserved`]: declined, UNKNOWN, with nothing read
//! from it. The one abstraction accepted is an elided drop (`abstracted(drop)`,
//! `abstracted(destructor)`): the walk reads such a body as `WalkDropsElided`, UNKNOWN. The
//! check judges the lowering the `mir_built` hook recorded; the module read here is the query's
//! second lowering, so the judgement is bound to it by its effect shape
//! (`effect_conservation::ReaderJudge`).
//!
//! # Two levels, one solve
//!
//! **Level 1, per body: facts.** The engine's own walk (`inspect_module_reachability`) runs over
//! a copy of the body's module to which a bodyless declaration is added for every ledger row,
//! classified by [`CalleeClass`] (design §5.2's classifier, as built):
//!
//! * a std thread-creation entry point (`is_std_thread_spawn`), havoc rows included:
//!   [`CalleeClass::Seed`];
//! * a non-generic local item the lane walks, or a foreign item whose link name the crate graph
//!   resolves to one: [`CalleeClass::Body`], a PORT the crate graph links;
//! * a foreign item the crate graph resolves to Rust code elsewhere: `Gap(ExternRust)`;
//! * any other foreign item: [`CalleeClass::Foreign`] (opaque, R3, charged by rule H) when it
//!   cannot unwind, else `Gap(UnwindingForeign)`;
//! * a havoc row (no concrete instance): `Gap(Havoc)`;
//! * a concrete instance with no body of its own (a generic callee's, a shim):
//!   `Gap(GenericInstance)`, or `Gap(ExternRust)` in another crate;
//! * another crate's Rust: `Gap(ExternRust)`, until increment 6;
//! * a local definition the lane does not walk (a constructor, say): `Gap(OutsideCensus)`.
//!
//! No row is ever `CallerTypeParameter` (PARAM, R1): a havoc row does not record why the
//! producer could not resolve it, and one row stands for every unresolved call of one
//! definition in the body (`admit_callee_inner` interns them on the definition alone), so a
//! call through the caller's own parameters and one through an opaque type share it. Reading
//! such a row as PARAM would let the opaque call through as QUIET. Increment 3's instance lane
//! is what retires the row. Runtime services (a panic, the allocator, reference counting) run
//! std code that has no trust-ir here: UNKNOWN. A closure value passed as `()` or a composite
//! constant placeholder is an UNKNOWN of its own.
//!
//! A declaration standing for the other bodies' callables, classified UNKNOWN and reached by
//! nothing, leaves the walk's pools unclosed: one body's walk sees only its own callables, so
//! every indirect call, and every hand-off that may carry a callable, reaches an UNKNOWN sink
//! (the engine's rule for a pool that may hold a callable it did not enumerate).
//!
//! The walk's labels are not read. What a body gives the crate graph ([`BodyGraph`]) is the
//! walk's EXPANDED graph, as its logical edges: the adapter's edges and the APPROX edges the
//! engine derived from the body's pools, every node with its [`Role`]. The hubs the engine
//! stores derived edges through are not imported.
//!
//! **Level 2, the crate: the one solve.** One [`ReachGraph`] imports every body's facts. A
//! body's own node, the ports naming it and its root are one node; every seed declaration is
//! the one seed; every foreign declaration is the FOREIGN WORLD ([`ForeignWorld`], below); any
//! other node of a walk (a synthesized adapter, a global, a gap declaration) is a node of its
//! own. An adapter edge is imported as is (a RUN into the seed as a spawn). A derived APPROX
//! edge is derived again by the engine, from a one-member pool its source invokes: an adapter
//! may not push one. A sink is a fresh sink of the same reason, reached from the same source;
//! an APPROX edge into a sink is imported as a RUN edge, which the UNKNOWN level admits alike
//! (every class but PARAM does). The engine solves the crate graph and checks its certificate;
//! every verdict-bearing step is the engine's, and a body's verdict is its root's label.
//!
//! What the compilation adds to a body after the producer lowered it, the module cannot hold:
//! the optimization pipeline's UB checks (a panic before a raw-pointer dereference or after a
//! transmute into an enum) and a certified monitor TrustVerify installs. The MIR lane charges
//! both; this lane charges the same predicates ([`AfterLowering`]), as gaps. A Clean-origin def
//! has no THIR, so it is a gap too (R5 is the MIR lane's).
//!
//! # The foreign world
//!
//! Foreign code is one node, which every body that reaches foreign code runs. It may call
//! every function the crate graph exports by symbol (the MIR lane's `SymbolTables`; an APPROX
//! edge, as the MIR lane's world: such code MAY call them). It may read every static the
//! crate graph exports by symbol or places in a named section and call what it holds, which no
//! census root walks ([`Gap::ExportedStatic`]). And it may call back whatever code out of sight
//! was handed or stored where foreign code can reach it ([`Gap::ForeignCallback`]), which this
//! lane does not enumerate. A body HANDS OUT, by its own instructions, when it calls foreign
//! code with an operand or for a result that may lead to memory (a store through it is foreign
//! code's), reaches any UNKNOWN sink or gap declaration (code it cannot see, which may hand
//! foreign code anything, its own callables included), or touches a global whose contents the
//! module does not hold (an `extern` static is foreign memory); a body with a foreign calling
//! convention that takes or returns anything hands out (foreign code may call it); a body this
//! lane does not walk hands out unless it is Clean-origin (R5). Module-level assembly is a gap
//! of the world.
//!
//! # Against the MIR lane
//!
//! The differential is the guard: the trust-ir lane QUIET where the MIR lane refuses is a
//! fail-open the flip must not inherit, and is reported as one; `check` makes it an error. It
//! sees a disagreement only. What the two lanes share is common-mode and invisible to it: the
//! foreign symbol tables (`SymbolTables`: the export list and link targets), the exported-static
//! predicate (`static_named_by_foreign_code`), the seed predicate
//! (`is_std_thread_spawn`), the monitor and Clean-origin predicates (`CensusHooks`), the UB-check
//! predicate and `trust_def_has_user_unsafe_source`. A fact both lanes miss stays missed.
//!
//! # What it does not see
//!
//! A producer that silently drops a call, a drop or a callable value that the effect-conservation
//! check also cannot see (design §12, R7): the module is the producer's word, checked against
//! rustc's built MIR only as far as that check pairs effects.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_hir::def::DefKind;
use rustc_middle::mir::trust_proof::{TrustSpawnCensus, TrustSpawnVerdict};
use rustc_middle::ty::{TyCtxt, TyKind};
use rustc_session::config::TrustSpawnCensusShadow;
use rustc_span::def_id::{DefId, DefIndex, LocalDefId};
use trust_ir::analysis::{PoolKey, PrincipalKey};
use trust_ir::function_dependencies::{
    DeclClassifier, DefinitionKey, DependencyNode, DependencyRefusalKind, DependencySite,
    EdgeClass, FunctionClass, Locality, NodeBody, NodeOrigin, ReachGraph, ReachNode, ReachNodeKind,
    ReachNodeSpec, ReachSite, RuntimeService, ServiceClass, Verdict, inspect_module_reachability,
};
use trust_ir::{BlockId, FuncId, FuncTy, FuncTyId, Function, Inst, Module, Ty};

use crate::effect_conservation::{self, Lane, TagKind};
use crate::{TrustIrCallee, TrustIrDecline, TrustIrOmission};

// ---------------------------------------------------------------------------------------------
// The vocabulary: why part of a closure is not enumerated.
// ---------------------------------------------------------------------------------------------

/// Why the trust-ir lane could not enumerate part of a body's closure: the reason each of its
/// UNKNOWN sinks carries, and what the scoreboard counts bodies by.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Gap {
    /// `trust_ir_of` produced no module for the body, for the query's own reason and in its own
    /// spelling. The lane runs only under verification, which runs the producer, so it does not
    /// meet `TrustIrDecline::LoweringDisabled`; the reason is the query's, never relabelled.
    Declined(TrustIrDecline),
    /// A Clean-origin definition: its trust-ir is not `trust_ir_of`'s.
    CleanOrigin,
    /// The effect-conservation check found an effect of the program the module does not carry
    /// (`not-conserved(..)`), or has no census of the body: the module is not the program.
    NotConserved,
    /// The module carries a value abstraction (`abstracted(undef | opaque-lane | union-lane |
    /// enum-param-lane)`): a value, and any callable in it, is spelled with fewer bytes than the
    /// program has.
    Abstracted,
    /// The producer emitted none of the body's drops (the drop planner refused it), or the
    /// effect-conservation check found a drop of the program the module does not carry.
    ElidedDrops,
    /// A capture-free closure was passed to a call as the `()` placeholder.
    ClosureValueOmitted,
    /// A composite named constant is a placeholder the crate finalizer patches later.
    PendingConst,
    /// A call the producer did not resolve to one instance (a type parameter, an opaque type,
    /// a `dyn` dispatch).
    Havoc,
    /// A concrete instance with no body of its own here (a generic callee, a shim).
    GenericInstance,
    /// Another crate's Rust code: no trust-ir crosses a crate boundary yet.
    ExternRust,
    /// A foreign function that may unwind: its cleanup path is not in any module.
    UnwindingForeign,
    /// Foreign code may call back what code out of sight handed it or stored where it can
    /// reach (a kept callback).
    ForeignCallback,
    /// The crate graph exports a static by symbol: foreign code may read it and call what it
    /// holds.
    ExportedStatic,
    /// A local definition the lane does not walk.
    OutsideCensus,
    /// A callee id no ledger row names.
    UnledgeredCallee,
    /// An `Inst::Drop`: drop glue is not a call yet (increment 4c).
    Drop,
    /// A panic runs std's panic runtime, and the panic hook.
    Panic,
    /// An allocation or deallocation runs the allocator.
    Allocator,
    /// The reference-count runtime.
    ReferenceCount,
    /// A panic the optimization pipeline's UB checks add after the body was lowered (before a
    /// raw-pointer dereference, after a transmute into an enum), in a body with user `unsafe`.
    UbCheck,
    /// A certified runtime monitor TrustVerify installs after the body was lowered (it panics).
    MonitorCheck,
    /// An indirect call or hand-off whose pool may hold a callable no walk enumerated.
    IndirectCall,
    /// A `dyn` principal whose runtime types are not all recorded.
    OpenPrincipal,
    /// An exactly resolved indirect call whose signature disagrees with its target's.
    IndirectSignature,
    /// A global whose contents are not in the module.
    ValueLessGlobal,
    /// An opaque dialect operation.
    DialectOp,
    /// Module-level assembly.
    GlobalAsm,
    /// A module shape the engine refuses (a missing or shared id, a malformed body).
    Malformed,
    /// A census that fell back: a malformed fact or a rejected certificate.
    CensusFallback,
}

impl Gap {
    /// Every gap, in report order.
    pub const ALL: [Gap; 33] = [
        Gap::Declined(TrustIrDecline::ALL[0]),
        Gap::Declined(TrustIrDecline::ALL[1]),
        Gap::Declined(TrustIrDecline::ALL[2]),
        Gap::Declined(TrustIrDecline::ALL[3]),
        Gap::Declined(TrustIrDecline::ALL[4]),
        Gap::CleanOrigin,
        Gap::NotConserved,
        Gap::Abstracted,
        Gap::ElidedDrops,
        Gap::ClosureValueOmitted,
        Gap::PendingConst,
        Gap::Havoc,
        Gap::GenericInstance,
        Gap::ExternRust,
        Gap::UnwindingForeign,
        Gap::ForeignCallback,
        Gap::ExportedStatic,
        Gap::OutsideCensus,
        Gap::UnledgeredCallee,
        Gap::Drop,
        Gap::Panic,
        Gap::Allocator,
        Gap::ReferenceCount,
        Gap::UbCheck,
        Gap::MonitorCheck,
        Gap::IndirectCall,
        Gap::OpenPrincipal,
        Gap::IndirectSignature,
        Gap::ValueLessGlobal,
        Gap::DialectOp,
        Gap::GlobalAsm,
        Gap::Malformed,
        Gap::CensusFallback,
    ];

    /// The stable spelling a report uses.
    pub fn as_str(self) -> &'static str {
        match self {
            Gap::Declined(decline) => decline.as_str(),
            Gap::CleanOrigin => "clean-origin",
            Gap::NotConserved => "not-conserved",
            Gap::Abstracted => "abstracted",
            Gap::ElidedDrops => "elided-drops",
            Gap::ClosureValueOmitted => "closure-value-omitted",
            Gap::PendingConst => "pending-const",
            Gap::Havoc => "havoc",
            Gap::GenericInstance => "generic-instance",
            Gap::ExternRust => "extern-rust",
            Gap::UnwindingForeign => "unwinding-foreign",
            Gap::ForeignCallback => "foreign-callback",
            Gap::ExportedStatic => "exported-static",
            Gap::OutsideCensus => "outside-census",
            Gap::UnledgeredCallee => "unledgered-callee",
            Gap::Drop => "drop",
            Gap::Panic => "panic",
            Gap::Allocator => "allocator",
            Gap::ReferenceCount => "refcount",
            Gap::UbCheck => "ub-check",
            Gap::MonitorCheck => "monitor-check",
            Gap::IndirectCall => "indirect-call",
            Gap::OpenPrincipal => "open-principal",
            Gap::IndirectSignature => "indirect-signature",
            Gap::ValueLessGlobal => "value-less-global",
            Gap::DialectOp => "dialect-op",
            Gap::GlobalAsm => "global-asm",
            Gap::Malformed => "malformed",
            Gap::CensusFallback => "census-fallback",
        }
    }

    fn bit(self) -> u64 {
        let position = Gap::ALL.iter().position(|gap| *gap == self).unwrap_or(0);
        1 << position
    }

    /// The engine's refusal for a declaration or sink of this gap. Only its being a sink
    /// matters: the gap itself is carried beside it.
    fn refusal(self, id: FuncId) -> DependencyRefusalKind {
        match self {
            Gap::Havoc => DependencyRefusalKind::HavocDeclaration,
            Gap::GenericInstance => DependencyRefusalKind::BodylessFunction(id),
            Gap::OutsideCensus | Gap::UnledgeredCallee => {
                DependencyRefusalKind::Missing(DependencyNode::Function(id))
            }
            _ => DependencyRefusalKind::UnresolvedExtern,
        }
    }

    /// Whether a body this lane does not walk, for this reason, may hand foreign code a
    /// callable it keeps. Every unwalked body may, except a Clean-origin one: the purity guard
    /// lets it call no impure Rust (R5), so it reaches no foreign code.
    fn unwalked_may_hand_out(self) -> bool {
        self != Gap::CleanOrigin
    }
}

/// A set of [`Gap`]s.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct GapSet(u64);

impl GapSet {
    pub fn insert(&mut self, gap: Gap) {
        self.0 |= gap.bit();
    }

    pub fn contains(self, gap: Gap) -> bool {
        self.0 & gap.bit() != 0
    }

    pub fn is_empty(self) -> bool {
        self.0 == 0
    }

    /// The gaps, in [`Gap::ALL`] order.
    pub fn iter(self) -> impl Iterator<Item = Gap> {
        Gap::ALL.into_iter().filter(move |gap| self.contains(*gap))
    }

    fn union(self, other: GapSet) -> GapSet {
        GapSet(self.0 | other.0)
    }
}

// ---------------------------------------------------------------------------------------------
// Level 1: one body's module, walked by the engine, as facts.
// ---------------------------------------------------------------------------------------------

/// What one ledger row stands for on this lane (see the module docs' list).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CalleeClass<B> {
    /// A std thread-creation entry point.
    Seed,
    /// A body this lane walks, linked at level 2.
    Body(B),
    /// Foreign code that cannot unwind: opaque, assumed to start no thread itself (R3), and
    /// charged by rule H with what the body hands it.
    Foreign,
    /// No trust-ir body here.
    Gap(Gap),
}

/// One classified ledger row.
#[derive(Clone, Debug)]
pub struct Declaration<'a, B> {
    pub func_id: FuncId,
    pub class: CalleeClass<B>,
    /// The parameter types a [`CalleeClass::Foreign`] declaration is signed with (rule H reads
    /// them); `None` carries anything.
    pub params: Option<&'a [Ty]>,
    /// A [`CalleeClass::Foreign`] declaration whose result may lead to memory foreign code
    /// reads later (anything but a scalar or `()`): a store through it hands that code what the
    /// memory holds, so a call of it hands out as a call with an operand does.
    pub returns_memory: bool,
}

/// The role a node of a body's walk plays in the crate graph.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Role<B> {
    /// The body itself (`functions[0]` of its module).
    Root,
    /// A ledger row naming a walked body: that body's own node in the crate graph.
    Port(B),
    /// A std thread-creation entry point: the crate graph's seed.
    Seed,
    /// Foreign code that cannot unwind: the crate graph's foreign world.
    Foreign,
    /// Any other program node of the walk (an adapter the producer synthesized, a global, a gap
    /// declaration, an id two functions share): a node of its own in the crate graph.
    Node(ReachNodeSpec),
    /// An UNKNOWN sink, and the gap it stands for.
    Sink(DependencyRefusalKind, Gap),
    /// An engine hub (`ReachNodeKind::Hub`): no logical edge touches it, and it is not imported.
    Hub,
}

/// One edge of a body's walk, by node position in [`BodyGraph::nodes`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Fact {
    pub from: usize,
    pub to: usize,
    pub class: EdgeClass,
    pub site: ReachSite,
    pub via_drop: bool,
}

/// What one body's walk tells the crate graph: the engine's expanded graph of the body's
/// module, every node with its role. The edges out of a port, a seed or a foreign declaration
/// are not kept: each stands for a node of the crate graph whose facts are its own.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BodyGraph<B> {
    pub nodes: Vec<Role<B>>,
    pub facts: Vec<Fact>,
    /// Gaps of the body the module cannot hold (the producer's omissions; what the compilation
    /// adds after lowering): sinks of its root.
    pub gaps: GapSet,
    /// The body hands code out of sight something it may keep (see the module docs).
    pub hands_out: bool,
}

/// What the lane knows of one body, for the crate graph.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BodyFacts<B> {
    Walked(BodyGraph<B>),
    /// No module is read for the body: UNKNOWN, for this reason.
    Declined(Gap),
}

/// The level-1 classifier: the body's own functions walk, each ledger row's declaration takes
/// its class, and every runtime service is std code with no trust-ir here.
struct BodyClasses(BTreeMap<FuncId, FunctionClass>);

impl DeclClassifier for BodyClasses {
    fn classify(&self, function: &Function) -> FunctionClass {
        // Every function of the census module was given a class; a function asked about
        // twice under one id is the engine's own `Ambiguous` node and is never asked.
        self.0.get(&function.id).cloned().unwrap_or(FunctionClass::Unknown(
            DependencyRefusalKind::Missing(DependencyNode::Function(function.id)),
        ))
    }

    fn definition(&self, function: &Function) -> DefinitionKey {
        DefinitionKey(u128::from(function.id.index()))
    }

    fn runtime_service(&self, _service: RuntimeService) -> ServiceClass {
        ServiceClass::Unknown(DependencyRefusalKind::UnresolvedExtern)
    }
}

/// The id of the declaration that stands for the callables other bodies mint (see the
/// module docs). Never named by an instruction the producer emits: body-local callee ids are
/// dense from 1 and adapters sit in a band below `u32::MAX`; a module that did name it, or
/// held a function under it, would make it an `Ambiguous` or UNKNOWN node, never a quiet one.
const OTHER_BODIES: FuncId = FuncId::new(u32::MAX);

/// The id the crate graph's foreign-world node is labelled with (an origin only).
const FOREIGN_WORLD: FuncId = FuncId::new(u32::MAX - 1);

/// Level 1: walk one body's module and keep the facts the crate graph imports.
pub fn walk_body<B: Clone + Ord>(
    module: &Module,
    declarations: &[Declaration<'_, B>],
    omissions: &[TrustIrOmission],
) -> BodyFacts<B> {
    let Some(body) = module.functions.first().map(|function| function.id) else {
        return BodyFacts::Declined(Gap::Malformed);
    };
    let elided =
        omissions.iter().any(|omission| matches!(omission, TrustIrOmission::ElidedDrops(_)));
    let mut census = module.clone();
    let mut classes = BTreeMap::new();
    for function in &module.functions {
        let class = if function.id == body && elided {
            FunctionClass::WalkDropsElided
        } else {
            FunctionClass::Walk
        };
        classes.insert(function.id, class);
    }
    let mut ports: BTreeMap<FuncId, B> = BTreeMap::new();
    let mut seeds: BTreeSet<FuncId> = BTreeSet::new();
    let mut foreign: BTreeSet<FuncId> = BTreeSet::new();
    let mut returning_ids: BTreeSet<FuncId> = BTreeSet::new();
    let mut declared: BTreeMap<FuncId, Gap> = BTreeMap::new();
    for declaration in declarations {
        let id = declaration.func_id;
        let mut signature = None;
        let class = match &declaration.class {
            CalleeClass::Seed => {
                seeds.insert(id);
                // No summary of the std code around the spawned callable
                // (trust-ir C1 N-4): that code is not enumerated, so the
                // thread is never modelable — the fail-closed seed.
                FunctionClass::Seed { spawned: None, child: None }
            }
            CalleeClass::Body(target) => {
                ports.insert(id, target.clone());
                FunctionClass::Unknown(DependencyRefusalKind::Missing(DependencyNode::Function(id)))
            }
            CalleeClass::Foreign => {
                foreign.insert(id);
                if declaration.returns_memory {
                    returning_ids.insert(id);
                }
                signature = declaration.params.map(|params| FuncTy {
                    params: params.to_vec(),
                    returns: Vec::new(),
                    is_vararg: false,
                    abi: None,
                });
                FunctionClass::Foreign
            }
            CalleeClass::Gap(gap) => {
                declared.insert(id, *gap);
                FunctionClass::Unknown(gap.refusal(id))
            }
        };
        // A missing signature carries anything (rule H) and matches every pool shape.
        let ty = match signature {
            // Trust (trust-ir D1b): a full type table declines the body, never panics.
            Some(signature) => match census.add_func_type(signature) {
                Ok(ty) => ty,
                Err(_) => return BodyFacts::Declined(Gap::Malformed),
            },
            None => FuncTyId::new(u32::MAX),
        };
        // Two rows, or a row and a function of the module, under one id are one `Ambiguous`
        // node to the engine: none of their classes is asked.
        census.functions.push(Function::new(
            id,
            format!("{{ledger #{}}}", id.index()),
            ty,
            BlockId::new(0),
        ));
        classes.insert(id, class);
    }
    census.functions.push(Function::new(
        OTHER_BODIES,
        "{callables of other bodies}",
        FuncTyId::new(u32::MAX),
        BlockId::new(0),
    ));
    classes.insert(OTHER_BODIES, FunctionClass::Unknown(DependencyRefusalKind::UnresolvedExtern));
    let walk = inspect_module_reachability(&census, &BodyClasses(classes));
    let reach = walk.census();
    if reach.fallback().is_some() {
        return BodyFacts::Declined(Gap::CensusFallback);
    }
    let Some(root) = walk.node(DependencyNode::Function(body)) else {
        return BodyFacts::Declined(Gap::Malformed);
    };
    let expanded = reach.expanded();
    let edges = expanded.logical_edges();

    // A declaration stands for a crate-graph node only when its id names one function: an id
    // two functions share is the engine's `Ambiguous` node, UNKNOWN, and imported as itself.
    let mut holders: BTreeMap<FuncId, usize> = BTreeMap::new();
    for function in &census.functions {
        *holders.entry(function.id).or_default() += 1;
    }
    let node_of = |id: FuncId| {
        (holders.get(&id) == Some(&1))
            .then(|| walk.node(DependencyNode::Function(id)))
            .flatten()
            .map(|node| node.index())
    };
    let mut special: BTreeMap<usize, Role<B>> = BTreeMap::new();
    for (id, target) in &ports {
        if let Some(index) = node_of(*id) {
            special.insert(index, Role::Port(target.clone()));
        }
    }
    for id in &seeds {
        if let Some(index) = node_of(*id) {
            special.insert(index, Role::Seed);
        }
    }
    for id in &foreign {
        if let Some(index) = node_of(*id) {
            special.insert(index, Role::Foreign);
        }
    }
    let returning: BTreeSet<usize> = returning_ids.iter().filter_map(|id| node_of(*id)).collect();
    special.insert(root.index(), Role::Root);
    let mut nodes: Vec<Role<B>> = expanded
        .nodes()
        .map(|(node, kind)| match (special.remove(&node.index()), kind) {
            (Some(role), _) => role,
            (None, ReachNodeKind::Program(spec)) => Role::Node(spec.clone()),
            // Named below, from the edge into it.
            (None, ReachNodeKind::Sink(reason)) => Role::Sink(reason.clone(), Gap::Malformed),
            (None, ReachNodeKind::Hub) => Role::Hub,
        })
        .collect();
    let mut named = vec![false; nodes.len()];
    for edge in &edges {
        let to = edge.to.index();
        if named[to] {
            continue;
        }
        if let Role::Sink(reason, gap) = &mut nodes[to] {
            *gap = sink_gap(&census, &declared, edge.site, reason);
            named[to] = true;
        }
    }

    // What the body hands code out of sight, read off the walk's own facts (every instruction
    // the engine reads as a call, a CREATE or a READ is seen): any edge of the body's own
    // functions into code or memory this lane does not walk, and a call of foreign code with
    // an operand. Any operand, not only one whose type spells a callable: a callable laundered
    // into an integer anywhere in the crate travels as data (`CarriedKey::Laundered`), and one
    // body cannot see another body's LAUNDER.
    let own: BTreeSet<usize> = module
        .functions
        .iter()
        .filter_map(|function| walk.node(DependencyNode::Function(function.id)))
        .map(|node| node.index())
        .collect();
    let hands_out = edges.iter().any(|edge| {
        own.contains(&edge.from.index())
            && !own.contains(&edge.to.index())
            && match &nodes[edge.to.index()] {
                Role::Root | Role::Port(_) | Role::Seed => false,
                Role::Foreign => {
                    edge.class == EdgeClass::Run
                        && (returning.contains(&edge.to.index())
                            || instruction_at(&census, edge.site).is_some_and(|inst| {
                                let mut operands = 0usize;
                                inst.visit_value_operands(|_| operands += 1);
                                operands > 0
                            }))
                }
                // A global whose contents the module does not hold may be foreign memory (an
                // `extern` static): what the body stores there, foreign code may call.
                Role::Node(ReachNodeSpec {
                    origin: NodeOrigin::TrustIr(DependencyNode::Global(id)),
                    ..
                }) => census.globals.get(id.as_usize()).is_none_or(|g| g.initializer.is_none()),
                Role::Node(_) | Role::Sink(..) | Role::Hub => true,
            }
    });

    let facts = edges
        .iter()
        .filter(|edge| {
            !matches!(nodes[edge.from.index()], Role::Port(_) | Role::Seed | Role::Foreign)
        })
        .map(|edge| Fact {
            from: edge.from.index(),
            to: edge.to.index(),
            class: edge.class,
            site: edge.site,
            via_drop: edge.via_drop,
        })
        .collect();
    let mut gaps = GapSet::default();
    for omission in omissions {
        match omission {
            // Walked as `WalkDropsElided`: the engine's own sink says it.
            TrustIrOmission::ElidedDrops(_) => {}
            TrustIrOmission::ClosureValueAsUnit => gaps.insert(Gap::ClosureValueOmitted),
            TrustIrOmission::PendingConstValue => gaps.insert(Gap::PendingConst),
        }
    }
    BodyFacts::Walked(BodyGraph { nodes, facts, gaps, hands_out })
}

/// The gap a level-1 sink stands for, read off the edge into it.
fn sink_gap(
    module: &Module,
    declared: &BTreeMap<FuncId, Gap>,
    site: ReachSite,
    reason: &DependencyRefusalKind,
) -> Gap {
    use DependencyRefusalKind as K;
    // A declaration's own sink: the edge out of the declaration names it.
    if let ReachSite::TrustIr(DependencySite::Definition(DependencyNode::Function(id))) = site {
        if let Some(gap) = declared.get(&id) {
            return *gap;
        }
    }
    match reason {
        K::ImplicitDestructor(_) => Gap::Drop,
        K::ElidedDrops => Gap::ElidedDrops,
        K::UnclosedPool | K::IndirectCall => Gap::IndirectCall,
        K::OpenPrincipal => Gap::OpenPrincipal,
        K::IndirectSignatureMismatch => Gap::IndirectSignature,
        K::Missing(DependencyNode::Function(_)) => Gap::UnledgeredCallee,
        K::MissingGlobalInitializer(_) => Gap::ValueLessGlobal,
        K::OpaqueDialectOperation => Gap::DialectOp,
        K::GlobalAssembly => Gap::GlobalAsm,
        // A runtime service (the classifier's only `UnresolvedExtern` outside declarations):
        // the instruction at the site says which.
        K::UnresolvedExtern => match instruction_at(module, site) {
            Some(Inst::Assert { .. }) => Gap::Panic,
            Some(Inst::HeapAlloc { .. } | Inst::Dealloc { .. }) => Gap::Allocator,
            Some(Inst::Retain { .. } | Inst::Release { .. } | Inst::IsUnique { .. }) => {
                Gap::ReferenceCount
            }
            _ => Gap::Malformed,
        },
        K::Missing(_)
        | K::Ambiguous(_)
        | K::BodylessFunction(_)
        | K::UnresolvedSymbol(_)
        | K::AmbiguousSymbol(_)
        | K::OpaqueType
        | K::AmbiguousBlock(_)
        | K::MissingEntryBlock(_)
        | K::GlobalTableTooLarge
        | K::HavocDeclaration
        | K::Widened
        | K::InlineAsm
        | K::AsyncDropShim
        | K::CoroutineClone
        | K::ResolutionError
        | K::UncoveredMention => Gap::Malformed,
    }
}

fn instruction_at(module: &Module, site: ReachSite) -> Option<&Inst> {
    let ReachSite::TrustIr(DependencySite::Instruction { function, block, index }) = site else {
        return None;
    };
    let mut functions = module.functions.iter().filter(|candidate| candidate.id == function);
    let (Some(function), None) = (functions.next(), functions.next()) else {
        return None;
    };
    let block = function.blocks.iter().find(|candidate| candidate.id == block)?;
    block.body.get(index).map(|node| &node.inst)
}

// ---------------------------------------------------------------------------------------------
// Level 2: the crate, one graph, one solve.
// ---------------------------------------------------------------------------------------------

/// The trust-ir lane's answer for one body.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LaneVerdict {
    pub verdict: Verdict,
    /// Every sink the body's closure reaches (empty: the closure is enumerated).
    pub gaps: GapSet,
}

/// What foreign code may call without being handed it (design §10, "P2 as built", Worlds):
/// every function the crate graph links under a name of its own (`#[no_mangle]`,
/// `#[export_name]`), what module-level assembly names, and what an exported static holds. The
/// walked functions are `exported`; every other is one of `gaps`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ForeignWorld<B> {
    pub exported: Vec<B>,
    pub gaps: GapSet,
}

impl<B> Default for ForeignWorld<B> {
    fn default() -> Self {
        ForeignWorld { exported: Vec::new(), gaps: GapSet::default() }
    }
}

/// The crate graph as it is built: the graph, the gap each sink stands for, and the next
/// one-member pool's key.
struct CrateGraph {
    graph: ReachGraph,
    sinks: BTreeMap<ReachNode, Gap>,
    pools: u64,
}

impl CrateGraph {
    /// An UNKNOWN sink of `gap` reached from `from`. The engine admits an adapter's APPROX
    /// edge nowhere; into a sink, every class but PARAM is admitted alike (a sink matters only
    /// at the UNKNOWN level), so APPROX becomes RUN.
    fn sink(
        &mut self,
        from: ReachNode,
        reason: DependencyRefusalKind,
        gap: Gap,
        class: EdgeClass,
        site: ReachSite,
        via_drop: bool,
    ) {
        let class = if class == EdgeClass::Approx { EdgeClass::Run } else { class };
        let node = self.graph.add_unknown(from, reason, class, site, via_drop);
        self.sinks.insert(node, gap);
    }

    /// An APPROX edge, which only the engine derives: a one-member pool `from` invokes.
    fn approx(&mut self, from: ReachNode, to: ReachNode, site: ReachSite, via_drop: bool) {
        let key = PoolKey::DynDrop(PrincipalKey(self.pools));
        self.pools += 1;
        self.graph.add_pool_member(to, key.clone(), false);
        self.graph.add_invoke(from, key, Vec::new(), site, via_drop);
    }
}

/// Level 2: import every body's facts into one crate graph, solve it, and answer for each body.
///
/// Foreign code is one node, the foreign WORLD, which every body that reaches foreign code
/// runs: it may call each function the crate graph exports by symbol (an APPROX edge, as the
/// MIR lane's world: such code MAY call them), and it may call back whatever code out of sight
/// was handed or stored where it can reach, which this lane does not enumerate
/// (`ForeignCallback`).
pub fn solve_crate<B: Clone + Ord>(
    bodies: &[(B, BodyFacts<B>)],
    world: &ForeignWorld<B>,
) -> BTreeMap<B, LaneVerdict> {
    let mut crate_graph = CrateGraph { graph: ReachGraph::new(), sinks: BTreeMap::new(), pools: 0 };
    let site = |index: usize| {
        ReachSite::TrustIr(DependencySite::Definition(DependencyNode::Function(FuncId::new(
            u32::try_from(index).unwrap_or(u32::MAX),
        ))))
    };
    let mut roots: BTreeMap<B, ReachNode> = BTreeMap::new();
    for (index, (body, _)) in bodies.iter().enumerate() {
        let id = u32::try_from(index).unwrap_or(u32::MAX);
        let node = crate_graph.graph.add_node(ReachNodeSpec {
            origin: NodeOrigin::TrustIr(DependencyNode::Function(FuncId::new(id))),
            definition: Some(DefinitionKey(u128::from(id))),
            locality: Locality::Local,
            body: NodeBody::Walked,
        });
        roots.insert(body.clone(), node);
    }
    let seed = crate_graph.graph.add_node(ReachNodeSpec {
        origin: NodeOrigin::TrustIr(DependencyNode::Function(OTHER_BODIES)),
        definition: None,
        locality: Locality::External,
        body: NodeBody::Seed,
    });
    let foreign = crate_graph.graph.add_node(ReachNodeSpec {
        origin: NodeOrigin::TrustIr(DependencyNode::Function(FOREIGN_WORLD)),
        definition: None,
        locality: Locality::External,
        body: NodeBody::Walked,
    });
    let unknown = |gap: Gap| gap.refusal(OTHER_BODIES);
    let mut handed_out = false;
    for (index, (body, facts)) in bodies.iter().enumerate() {
        let root = roots[body];
        match facts {
            BodyFacts::Declined(gap) => {
                crate_graph.sink(root, unknown(*gap), *gap, EdgeClass::Run, site(index), false);
                handed_out |= gap.unwalked_may_hand_out();
            }
            BodyFacts::Walked(walk) => {
                let mut mapped: Vec<Option<ReachNode>> = Vec::with_capacity(walk.nodes.len());
                for role in &walk.nodes {
                    mapped.push(match role {
                        Role::Root => Some(root),
                        Role::Port(target) => Some(match roots.get(target) {
                            Some(&node) => node,
                            None => {
                                let node = crate_graph.graph.add_node(ReachNodeSpec {
                                    origin: NodeOrigin::TrustIr(DependencyNode::Function(
                                        OTHER_BODIES,
                                    )),
                                    definition: None,
                                    locality: Locality::Local,
                                    body: NodeBody::Walked,
                                });
                                crate_graph.sink(
                                    node,
                                    unknown(Gap::OutsideCensus),
                                    Gap::OutsideCensus,
                                    EdgeClass::Run,
                                    site(index),
                                    false,
                                );
                                node
                            }
                        }),
                        Role::Seed => Some(seed),
                        Role::Foreign => Some(foreign),
                        // Its definition key is body-local: it joins nothing here.
                        Role::Node(spec) => Some(
                            crate_graph
                                .graph
                                .add_node(ReachNodeSpec { definition: None, ..spec.clone() }),
                        ),
                        Role::Sink(..) | Role::Hub => None,
                    });
                }
                for fact in &walk.facts {
                    // A sink has no edge out; an unmapped source is a sink.
                    let Some(from) = mapped[fact.from] else { continue };
                    match (&walk.nodes[fact.to], mapped[fact.to]) {
                        (Role::Sink(reason, gap), _) => crate_graph.sink(
                            from,
                            reason.clone(),
                            *gap,
                            fact.class,
                            fact.site,
                            fact.via_drop,
                        ),
                        (_, None) => {}
                        (_, Some(to)) if fact.class == EdgeClass::Approx => {
                            crate_graph.approx(from, to, fact.site, fact.via_drop)
                        }
                        (Role::Seed, Some(to)) if fact.class == EdgeClass::Run => {
                            crate_graph.graph.add_spawn(from, to, None, fact.site, fact.via_drop)
                        }
                        (_, Some(to)) => crate_graph.graph.add_edge(
                            from,
                            to,
                            fact.class,
                            fact.site,
                            fact.via_drop,
                        ),
                    }
                }
                for gap in walk.gaps.iter() {
                    crate_graph.sink(root, unknown(gap), gap, EdgeClass::Run, site(index), false);
                }
                handed_out |= walk.hands_out;
            }
        }
    }
    let world_site =
        ReachSite::TrustIr(DependencySite::Definition(DependencyNode::Function(FOREIGN_WORLD)));
    let mut world_gaps = world.gaps;
    if handed_out {
        world_gaps.insert(Gap::ForeignCallback);
    }
    for gap in world_gaps.iter() {
        crate_graph.sink(foreign, unknown(gap), gap, EdgeClass::Run, world_site, false);
    }
    // One pool the world invokes, holding every exported body: the engine derives an APPROX
    // edge to each, as the MIR lane's world does.
    let key = PoolKey::DynDrop(PrincipalKey(crate_graph.pools));
    let mut members = 0usize;
    for exported in &world.exported {
        match roots.get(exported) {
            Some(&member) => {
                crate_graph.graph.add_pool_member(member, key.clone(), false);
                members += 1;
            }
            None => crate_graph.sink(
                foreign,
                unknown(Gap::OutsideCensus),
                Gap::OutsideCensus,
                EdgeClass::Run,
                world_site,
                false,
            ),
        }
    }
    if members > 0 {
        crate_graph.graph.add_invoke(foreign, key, Vec::new(), world_site, false);
    }
    let CrateGraph { graph, sinks, .. } = crate_graph;
    let census = graph.solve();
    if census.fallback().is_some() {
        let mut gaps = GapSet::default();
        gaps.insert(Gap::CensusFallback);
        return roots
            .into_keys()
            .map(|body| (body, LaneVerdict { verdict: Verdict::Unknown, gaps }))
            .collect();
    }
    // The gaps of each node's closure, for the report only: sinks propagated backwards over
    // every admitted edge. The verdict is the engine's label alone.
    let expanded = census.expanded();
    let mut masks = vec![GapSet::default(); expanded.nodes().len()];
    let mut queue = VecDeque::new();
    for (node, kind) in expanded.nodes() {
        if let ReachNodeKind::Sink(reason) = kind {
            let gap = sinks.get(&node).copied().unwrap_or(match reason {
                DependencyRefusalKind::OpenPrincipal => Gap::OpenPrincipal,
                DependencyRefusalKind::UnclosedPool => Gap::IndirectCall,
                _ => Gap::Malformed,
            });
            masks[node.index()].insert(gap);
            queue.push_back(node.index());
        }
    }
    let mut predecessors = vec![Vec::new(); masks.len()];
    for edge in expanded.edges() {
        if edge.class.cap() != Verdict::Quiet {
            predecessors[edge.to.index()].push(edge.from.index());
        }
    }
    while let Some(to) = queue.pop_front() {
        let gaps = masks[to];
        for &from in &predecessors[to] {
            let joined = masks[from].union(gaps);
            if joined != masks[from] {
                masks[from] = joined;
                queue.push_back(from);
            }
        }
    }
    roots
        .into_iter()
        .map(|(body, node)| {
            (body, LaneVerdict { verdict: census.verdict(node), gaps: masks[node.index()] })
        })
        .collect()
}

// ---------------------------------------------------------------------------------------------
// The rustc side: the classifier and the lane.
// ---------------------------------------------------------------------------------------------

/// What the compilation does to a body after the producer lowered it, which only the pass
/// manager and TrustVerify can say (`rustc_mir_transform` supplies it). The MIR lane charges
/// both: they are panics added after the body the census reads.
pub struct AfterLowering<'a> {
    /// The optimization pipeline's UB checks run (`CheckAlignment`, `CheckNull`,
    /// `CheckEnums`: `-Zub-checks`, `-Zmir-enable-passes`).
    pub ub_checks: bool,
    /// TrustVerify may install a certified runtime monitor in this body.
    pub may_carry_monitor: &'a dyn Fn(LocalDefId) -> bool,
    /// This is a Clean-origin def, which has no THIR (R5).
    pub is_clean_origin: &'a dyn Fn(LocalDefId) -> bool,
}

/// The effect-conservation tags a reader of the census accepts: an elided drop, which the walk
/// reads as `WalkDropsElided` (an UNKNOWN sink), whether or not its glue runs a destructor.
const ACCEPTED_TAGS: [TagKind; 2] =
    [TagKind::Abstracted(Lane::Drop), TagKind::Abstracted(Lane::Destructor)];

/// Whether the module `trust_ir_of(def)` returned is the program (see the module docs): `Ok`
/// with whether the check found an elided drop, or the gap that declines the body.
fn read_as_program(
    tcx: TyCtxt<'_>,
    judge: &effect_conservation::ReaderJudge,
    def: LocalDefId,
    module: &Module,
) -> Result<bool, Gap> {
    let Some(read) = module.functions.first() else { return Err(Gap::Malformed) };
    let tags = judge.tags(tcx, def, module, read);
    let refused = effect_conservation::refused_for_verification(&tags, &ACCEPTED_TAGS);
    if refused.iter().any(|tag| matches!(tag.kind, TagKind::NotConserved(_))) {
        Err(Gap::NotConserved)
    } else if !refused.is_empty() {
        Err(Gap::Abstracted)
    } else {
        Ok(!tags.is_empty())
    }
}

/// The trust-ir lane over `roots` (the fn-like local bodies the MIR lane answers for).
pub fn trust_ir_lane(
    tcx: TyCtxt<'_>,
    roots: &[LocalDefId],
    after: &AfterLowering<'_>,
) -> FxHashMap<LocalDefId, LaneVerdict> {
    let walked: FxHashSet<LocalDefId> = roots.iter().copied().collect();
    let mut symbols = None;
    let judge = effect_conservation::ReaderJudge::new(tcx);
    let bodies: Vec<(DefIndex, BodyFacts<DefIndex>)> = roots
        .iter()
        .map(|&def| {
            // A Clean-origin def is lowered by the Clean pipeline, not from THIR: asking
            // `trust_ir_of` would ask a body HIR does not have.
            if (after.is_clean_origin)(def) {
                return (def.local_def_index, BodyFacts::Declined(Gap::CleanOrigin));
            }
            let Some(body) = tcx.trust_ir_of(def) else {
                let decline = crate::trust_ir_of_declined(tcx, def);
                return (def.local_def_index, BodyFacts::Declined(Gap::Declined(decline)));
            };
            let drops_elided = match read_as_program(tcx, &judge, def, &body.module) {
                Ok(drops_elided) => drops_elided,
                Err(gap) => return (def.local_def_index, BodyFacts::Declined(gap)),
            };
            let declarations: Vec<Declaration<'_, DefIndex>> =
                body.callees.iter().map(|row| classify(tcx, row, &walked, &mut symbols)).collect();
            let mut omissions = body.omissions.clone();
            if drops_elided
                && !omissions
                    .iter()
                    .any(|omission| matches!(omission, TrustIrOmission::ElidedDrops(_)))
            {
                omissions.push(TrustIrOmission::ElidedDrops(
                    "the effect-conservation check found an elided drop".to_string(),
                ));
            }
            let mut facts = walk_body(&body.module, &declarations, &omissions);
            if let BodyFacts::Walked(graph) = &mut facts {
                // Raw-pointer dereferences and transmutes need user `unsafe` in the body's
                // source (a callee's are its own).
                if after.ub_checks && tcx.trust_def_has_user_unsafe_source(def.to_def_id()) {
                    graph.gaps.insert(Gap::UbCheck);
                }
                if (after.may_carry_monitor)(def) {
                    graph.gaps.insert(Gap::MonitorCheck);
                }
                // A body with a foreign calling convention may be called by foreign code: what
                // it is passed may lead to memory foreign code reads later, and what it returns
                // is handed to foreign code (the MIR lane's `foreign_entry`).
                if foreign_entry_hands_out(tcx, def) {
                    graph.hands_out = true;
                }
            }
            (def.local_def_index, facts)
        })
        .collect();
    let reaches_foreign_code = bodies.iter().any(|(_, facts)| match facts {
        BodyFacts::Walked(graph) => graph.nodes.iter().any(|role| *role == Role::Foreign),
        BodyFacts::Declined(_) => false,
    });
    let world = if reaches_foreign_code {
        let symbols = symbols
            .get_or_insert_with(|| trust_mir_extract::concurrency_effects::SymbolTables::new(tcx));
        foreign_world(tcx, symbols, &walked)
    } else {
        ForeignWorld::default()
    };
    solve_crate(&bodies, &world)
        .into_iter()
        .map(|(local_def_index, verdict)| (LocalDefId { local_def_index }, verdict))
        .collect()
}

/// The foreign world of the crate graph: the functions it exports by symbol (`SymbolTables`,
/// the MIR lane's own table), the statics it exports by symbol, and the crate's module-level
/// assembly.
fn foreign_world(
    tcx: TyCtxt<'_>,
    symbols: &trust_mir_extract::concurrency_effects::SymbolTables,
    walked: &FxHashSet<LocalDefId>,
) -> ForeignWorld<DefIndex> {
    let mut world = ForeignWorld::default();
    for def in symbols.exported() {
        match walked_body(def, walked) {
            Ok(index) => world.exported.push(index),
            Err(gap) => world.gaps.insert(gap),
        }
    }
    world.exported.sort_unstable();
    if exports_a_static(tcx) {
        world.gaps.insert(Gap::ExportedStatic);
    }
    // A Clean island also takes `DefKind::GlobalAsm`; it is not assembly.
    if tcx.hir_crate_items(()).definitions().any(|def| {
        tcx.def_kind(def) == DefKind::GlobalAsm && !tcx.trust_def_is_clean_island(def.to_def_id())
    }) {
        world.gaps.insert(Gap::GlobalAsm);
    }
    world
}

/// Whether `def` is a fn with a foreign calling convention that takes or returns anything.
fn foreign_entry_hands_out(tcx: TyCtxt<'_>, def: LocalDefId) -> bool {
    if !matches!(tcx.def_kind(def), DefKind::Fn | DefKind::AssocFn) {
        return false;
    }
    let signature = tcx.fn_sig(def).skip_binder().skip_binder();
    !signature.abi().is_rustic_abi()
        && (!signature.inputs().is_empty() || !signature.output().is_unit())
}

/// Whether the crate graph has a static foreign code names without being handed it (the MIR
/// lane's `static_named_by_foreign_code`: an export of its own or a named section, outside the
/// sysroot), the local crate's or a dependency's: foreign code may read it, and call what it
/// holds or what Rust stores in it later. The MIR lane's foreign world calls both; this lane
/// does not enumerate them and says UNKNOWN.
fn exports_a_static(tcx: TyCtxt<'_>) -> bool {
    let exported =
        |def: DefId| trust_mir_extract::concurrency_effects::static_named_by_foreign_code(tcx, def);
    tcx.hir_crate_items(()).definitions().any(|def| exported(def.to_def_id()))
        || tcx
            .crates(())
            .iter()
            .filter(|&&krate| !trust_mir_extract::concurrency_effects::in_sysroot(tcx, krate))
            .any(|&krate| {
                trust_mir_extract::concurrency_effects::linked_candidates(tcx, krate)
                    .into_iter()
                    .any(exported)
            })
}

/// Design §5.2's classifier for one ledger row (see the module docs' list).
fn classify<'a>(
    tcx: TyCtxt<'_>,
    row: &'a TrustIrCallee,
    walked: &FxHashSet<LocalDefId>,
    symbols: &mut Option<trust_mir_extract::concurrency_effects::SymbolTables>,
) -> Declaration<'a, DefIndex> {
    let declaration =
        |class| Declaration { func_id: row.func_id, class, params: None, returns_memory: false };
    let def = row.def_id;
    // A seed stays a seed, whatever the producer could resolve of the call.
    if trust_mir_extract::concurrency_effects::is_std_thread_spawn(tcx, def) {
        return declaration(CalleeClass::Seed);
    }
    if row.force_bodyless && !row.concrete {
        return declaration(CalleeClass::Gap(Gap::Havoc));
    }
    if tcx.is_foreign_item(def) {
        let symbols = symbols
            .get_or_insert_with(|| trust_mir_extract::concurrency_effects::SymbolTables::new(tcx));
        if let Some(target) = symbols.link_target(tcx, def) {
            return declaration(body_or_gap(walked_body(target, walked)));
        }
        let signature = tcx.fn_sig(def).skip_binder().skip_binder();
        if rustc_middle::ty::layout::fn_can_unwind(tcx, Some(def), signature.abi()) {
            return declaration(CalleeClass::Gap(Gap::UnwindingForeign));
        }
        // A C-variadic call's extra arguments have no stated type: unsigned, it carries all.
        let params = if signature.c_variadic() { None } else { row.params.as_deref() };
        let output = signature.output();
        let returns_memory = !output.is_unit()
            && !matches!(
                output.kind(),
                TyKind::Bool
                    | TyKind::Char
                    | TyKind::Int(_)
                    | TyKind::Uint(_)
                    | TyKind::Float(_)
                    | TyKind::Never
            );
        return Declaration {
            func_id: row.func_id,
            class: CalleeClass::Foreign,
            params,
            returns_memory,
        };
    }
    if row.force_bodyless {
        return declaration(CalleeClass::Gap(if def.is_local() {
            Gap::GenericInstance
        } else {
            Gap::ExternRust
        }));
    }
    declaration(body_or_gap(walked_body(def, walked)))
}

/// The body this lane walks for `def`, keyed by its `DefIndex` (`LocalDefId` is deliberately
/// unordered), or why there is none.
fn walked_body(def: DefId, walked: &FxHashSet<LocalDefId>) -> Result<DefIndex, Gap> {
    match def.as_local() {
        Some(local) if walked.contains(&local) => Ok(local.local_def_index),
        Some(_) => Err(Gap::OutsideCensus),
        None => Err(Gap::ExternRust),
    }
}

fn body_or_gap(body: Result<DefIndex, Gap>) -> CalleeClass<DefIndex> {
    match body {
        Ok(index) => CalleeClass::Body(index),
        Err(gap) => CalleeClass::Gap(gap),
    }
}

// ---------------------------------------------------------------------------------------------
// The shadow differential and its report.
// ---------------------------------------------------------------------------------------------

/// How the two lanes' verdicts for one body compare.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Agreement {
    Equal,
    /// The trust-ir lane is UNKNOWN; the MIR lane decided otherwise.
    TrustIrUnknown,
    /// Both refuse, with different verdicts, and the trust-ir lane's is not UNKNOWN.
    Differs,
    /// INVARIANT: the trust-ir lane is QUIET where the MIR lane refuses, a fail-open the flip
    /// must not inherit.
    FailOpen,
    /// INVARIANT (design §5.7): the trust-ir lane reaches a seed (SPAWNS, ESCAPES, INDIRECT)
    /// where the MIR lane is QUIET.
    MirQuietClaim,
    /// The MIR lane did not walk the body (a Clean-origin def, R5): nothing to compare.
    MirNotWalked,
    /// The MIR lane's census fell back (a malformed fact or a rejected certificate): every
    /// MIR verdict is its fallback UNKNOWN, nothing to compare. `check` fails the crate.
    MirFellBack,
}

impl Agreement {
    pub fn as_str(self) -> &'static str {
        match self {
            Agreement::Equal => "equal",
            Agreement::TrustIrUnknown => "trust-ir-unknown",
            Agreement::Differs => "differs",
            Agreement::FailOpen => "fail-open",
            Agreement::MirQuietClaim => "mir-quiet-claim",
            Agreement::MirNotWalked => "mir-not-walked",
            Agreement::MirFellBack => "mir-fell-back",
        }
    }

    pub fn is_violation(self) -> bool {
        matches!(self, Agreement::FailOpen | Agreement::MirQuietClaim)
    }

    pub fn compare(mir: Verdict, mir_walked: bool, trust_ir: Verdict) -> Agreement {
        if !mir_walked {
            Agreement::MirNotWalked
        } else if mir == trust_ir {
            Agreement::Equal
        } else if trust_ir == Verdict::Quiet {
            Agreement::FailOpen
        } else if mir == Verdict::Quiet && trust_ir > Verdict::Unknown {
            Agreement::MirQuietClaim
        } else if trust_ir == Verdict::Unknown {
            Agreement::TrustIrUnknown
        } else {
            Agreement::Differs
        }
    }
}

fn mir_verdict(verdict: TrustSpawnVerdict) -> Verdict {
    match verdict {
        TrustSpawnVerdict::Quiet => Verdict::Quiet,
        TrustSpawnVerdict::Unknown => Verdict::Unknown,
        TrustSpawnVerdict::Indirect => Verdict::Indirect,
        TrustSpawnVerdict::Escapes => Verdict::Escapes,
        TrustSpawnVerdict::Spawns => Verdict::Spawns,
    }
}

fn verdict_str(verdict: Verdict) -> &'static str {
    match verdict {
        Verdict::Quiet => "QUIET",
        Verdict::Unknown => "UNKNOWN",
        Verdict::Indirect => "INDIRECT",
        Verdict::Escapes => "ESCAPES",
        Verdict::Spawns => "SPAWNS",
    }
}

/// The line prefix every report line carries (the scoreboard keys on it).
pub const REPORT_PREFIX: &str = "trust-spawn-census-shadow:";

/// A TEST-ONLY fault (`TRUST_SPAWN_CENSUS_TEST_FAULT=shadow-forge-quiet`, read through the
/// tracked `env_var_os` query, the MIR lane's own fault variable, whose values it ignores): the
/// trust-ir lane's every answer is forged to QUIET, so `check`'s error is exercised end to end
/// on a real fail-open. It changes only this measurement's report, never a verdict.
fn forges_quiet(tcx: TyCtxt<'_>) -> bool {
    tcx.env_var_os(std::ffi::OsStr::new("TRUST_SPAWN_CENSUS_TEST_FAULT"))
        .is_some_and(|value| value == "shadow-forge-quiet")
}

/// Run the trust-ir lane in shadow, compare it with the MIR lane's census and print the
/// differential. Changes no verdict. Under [`TrustSpawnCensusShadow::Check`] an invariant
/// violation is a compile error, and so is a crate whose MIR census fell back: nothing was
/// compared, and a comparison that did not run is not a pass.
pub fn shadow(tcx: TyCtxt<'_>, mode: TrustSpawnCensusShadow, after: &AfterLowering<'_>) {
    let census: &TrustSpawnCensus<'_> = tcx.trust_spawn_census(());
    let roots: Vec<LocalDefId> = census.definitions.iter().map(|(def, _)| *def).collect();
    let mut lane = trust_ir_lane(tcx, &roots, after);
    if forges_quiet(tcx) {
        for answer in lane.values_mut() {
            *answer = LaneVerdict { verdict: Verdict::Quiet, gaps: GapSet::default() };
        }
    }
    let crate_name = tcx.crate_name(rustc_span::def_id::LOCAL_CRATE);
    if let Some(reason) = &census.fallback {
        eprintln!("{REPORT_PREFIX} crate `{crate_name}` mir lane fell back: {reason}");
    }
    let mut counts: BTreeMap<Agreement, usize> = BTreeMap::new();
    let (mut decided, mut residue) = (0usize, 0usize);
    let mut violations = Vec::new();
    for (def, sites) in &census.definitions {
        let mir = mir_verdict(sites.verdict);
        let ir = lane[def];
        let agreement = if census.fallback.is_some() {
            Agreement::MirFellBack
        } else {
            Agreement::compare(mir, sites.walked, ir.verdict)
        };
        *counts.entry(agreement).or_default() += 1;
        if ir.gaps.is_empty()
            && !matches!(agreement, Agreement::MirNotWalked | Agreement::MirFellBack)
        {
            decided += 1;
            residue += usize::from(agreement != Agreement::Equal);
        }
        let path = rustc_middle::ty::print::with_no_trimmed_paths!(tcx.def_path_str(*def));
        let gaps: Vec<&str> = ir.gaps.iter().map(Gap::as_str).collect();
        eprintln!(
            "{REPORT_PREFIX} body `{path}` mir={} trust-ir={} {} gaps={}",
            verdict_str(mir),
            verdict_str(ir.verdict),
            agreement.as_str(),
            if gaps.is_empty() { "-".to_string() } else { gaps.join(",") },
        );
        if agreement.is_violation() {
            violations.push(format!("`{path}` ({})", agreement.as_str()));
        }
    }
    let count = |agreement| counts.get(&agreement).copied().unwrap_or(0);
    eprintln!(
        "{REPORT_PREFIX} crate `{crate_name}` bodies={} equal={} trust-ir-unknown={} differs={} \
         fail-open={} mir-quiet-claim={} mir-not-walked={} mir-fell-back={} decided={decided} \
         residue={residue}",
        census.definitions.len(),
        count(Agreement::Equal),
        count(Agreement::TrustIrUnknown),
        count(Agreement::Differs),
        count(Agreement::FailOpen),
        count(Agreement::MirQuietClaim),
        count(Agreement::MirNotWalked),
        count(Agreement::MirFellBack),
    );
    if mode != TrustSpawnCensusShadow::Check {
        return;
    }
    let bodies = |n: usize| if n == 1 { "body" } else { "bodies" };
    if let Some(reason) = &census.fallback {
        let n = census.definitions.len();
        tcx.dcx().err(format!(
            "the spawn census's trust-ir shadow lane compared nothing on {n} {}: the MIR lane's \
             census fell back ({reason})",
            bodies(n),
        ));
    }
    if !violations.is_empty() {
        tcx.dcx().err(format!(
            "the spawn census's trust-ir shadow lane violates its invariant on {} {}: {}",
            violations.len(),
            bodies(violations.len()),
            violations.join(", "),
        ));
    }
}

#[cfg(test)]
mod tests;
