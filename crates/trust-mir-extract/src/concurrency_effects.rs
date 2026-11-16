// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: MIT OR Apache-2.0

//! The spawn census's MIR adapter (design
//! `docs/design/2026-09-29-spawn-census-by-construction.md` §5.2-§5.6, plan
//! step P2). It turns MIR into the facts of trust-ir's reachability engine
//! ([`ReachGraph`], `function_dependencies.rs`), solves the graph once per
//! crate, and renders each local body's verdict and rows. Rows only authorize
//! a refusal; a QUIET body is not evidence that it or its callees are
//! race-free.
//!
//! # What a row claims
//!
//! The engine labels every node with the strongest verdict a path admits
//! ([`Verdict`]). A row is an edge out of a local body whose target is not
//! QUIET; its strength is the weaker of the edge class's cap and the target's
//! label. Only a path of RUN edges claims a spawn (SPAWNS, S1-S3):
//!
//! * **(S1)** a call of a std thread-creation entry point
//!   ([`is_std_thread_spawn`], the five diagnostic items);
//! * **(S2)** a call that rustc's resolver resolves EXACTLY to a body (an item,
//!   a shim over an item, a fallback intrinsic body, a resolved foreign
//!   runtime symbol) that reaches one over RUN edges only;
//! * **(S3)** a MIR `Drop` of a value whose drop glue, decomposed
//!   structurally (an ADT's `Drop::drop` then its fields, aggregates, a
//!   coroutine's `coroutine_drop` body), reaches one.
//!
//! Every other row refuses without claiming a spawn: ESCAPES (a callable that
//! reaches a spawn is made into a fn pointer or `dyn` value, or a `const` /
//! `static` holding one is read), INDIRECT (`IndirectCallMaySpawn`: an indirect
//! call's pool, or a rule H hand-off, holds a callable that reaches a spawn)
//! and UNKNOWN ("not enumerated (no spawn was found)"). Rows say "reaches":
//! a `const`-false branch is still walked.
//!
//! # The facts (design §5.2-§5.4)
//!
//! One pass per body. Local bodies are read PRE-STEAL through
//! [`CensusHooks::with_local_body`] (`mir_drops_elaborated_and_const_checked`,
//! on a copy to which the UB checks the optimization pipeline adds first are
//! applied: a misaligned or null pointer dereference, an invalid enum
//! construction), `mir_for_ctfe` and `promoted_mir`; external bodies come from
//! metadata (`optimized_mir`, `mir_for_ctfe`, `promoted_mir`, the evaluated
//! static allocation, and for the sysroot scan only each body's
//! `trust_mentioned_items`). The census never reads a LOCAL `optimized_mir`,
//! `mir_shims` or a fresh const evaluation, and never asks rustc's resolver
//! for drop glue (for a coroutine it demands `optimized_mir`).
//!
//! * rustc's `MentionedItems` enumeration ([`CensusHooks::for_each_mentioned_item`])
//!   supplies the calls, drops and callable casts. The callee is
//!   `func.ty(body)`, so `let f = launch; f()` is a direct call at every opt
//!   level, and every item is resolved per instance by rustc's resolvers.
//! * A visitor with no wildcard arm adds the rest: constant provenance
//!   (functions, vtables and statics in allocations: CREATE and READ),
//!   thread-locals, panics and unwind termination (the lang items), inline
//!   assembly (UNKNOWN), LAUNDER and LIFETIME-ERASE. A contract owner of a
//!   monitored test session also runs the certified-monitor check TrustVerify
//!   installs after the census.
//! * A local function is a node as its identity instance and as every
//!   concrete instance reachable from a root; what its identity instance
//!   cannot resolve (a call or drop through its own type parameters) is a
//!   PARAM edge, admitted by no verdict (R1), and exact in each concrete
//!   instance.
//! * Drops are decomposed structurally (never through `mir_shims`); `dyn`
//!   drops and calls charge their pools ([`PoolKey`]); a foreign symbol is
//!   resolved by link name (the allocator's `__rust_alloc*` to the
//!   `#[global_allocator]` or std's default, `panic_impl` to the panic
//!   handler, std-internal runtime symbols to their definitions, any other
//!   declaration to the function the crate graph exports under its link
//!   name), otherwise it is opaque (R3) and charged by rule H.
//! * Code the census cannot walk (foreign code, MIR-less Rust) RUNs its
//!   WORLD's node, which may call what such code can reach unseen: whatever
//!   any frame outside the sysroot ever handed such code (a kept callback),
//!   what Rust may store in memory foreign code reads without being handed
//!   it (an `extern` static a walked node names, memory behind a pointer
//!   foreign code returned or passed in, a static foreign code names by
//!   symbol or section), the functions and statics the crate graph exports by
//!   symbol, module-level assembly (UNKNOWN), and, for MIR-less Rust, the
//!   global allocator, the alloc error handler and the panic handler. A MIR-less function that can hand a
//!   callable back (by return or through a pointer it is handed) is UNKNOWN:
//!   no pool records what it minted.
//!
//! # Exclusions (design §12)
//!
//! R1 reach only through a definition's own type parameters, with no in-crate
//! instantiation. R2 MIR-less non-generic external Rust outside the sysroot is
//! opaque: assumed to start no thread itself and to launder no callable into
//! plain data (a MIR-less SYSROOT item is UNKNOWN). R3 foreign code: it starts
//! no thread itself, and the sysroot's own calls into the platform's C library
//! keep nothing that runs as part of a caller (thread-exit destructors are R6).
//! R4 UB. R5 Clean-origin bodies: the purity guard's argument covers them and
//! the census does not read them ([`CensusHooks::is_clean_origin`]). A vtable
//! that erases a reference to a local of its frame is CONFINED (design §5.4,
//! [`Walker::vtable`]): an invoke in external code does not see its members,
//! and its creator, and every local frame that hands it to external code by a
//! call, an indirect call or a drop, is charged instead; any cast,
//! transmute, raw pointer or union whose type carries the principal demotes
//! it. A LAUNDER leaves the fn pools keyed by shape: calling a fn pointer at
//! a shape its callee's does not match is R4 UB. Every route by which a
//! callable's bytes reach plain data (a value reinterpretation, a pointer
//! view at another pointee, a union's fields, a reshaped fn pointer's
//! arguments, an exposed address, a constant's bytes) is a LAUNDER keyed by
//! the callables those bytes may hold, and plain data holds what the keys of
//! every LAUNDER admit (design §10, "Typed LAUNDER"; a value reinterpretation
//! is still a LAUNDER of every callable).

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::hash::{Hash, Hasher};
use std::rc::Rc;

use rustc_abi::{FieldsShape, Variants};
use rustc_attr_ir::lang_items::LangItem;
use rustc_data_structures::fx::{FxHashMap, FxHashSet, FxHasher, FxIndexSet};
use rustc_data_structures::graph::scc::Sccs;
use rustc_data_structures::graph::vec_graph::VecGraph;
use rustc_hir::def::DefKind;
use rustc_middle::middle::codegen_fn_attrs::CodegenFnAttrFlags;
use rustc_middle::middle::exported_symbols::ExportedSymbol;
use rustc_middle::mir::interpret::{AllocId, Allocation, GlobalAlloc, Scalar, read_target_uint};
use rustc_middle::mir::trust_proof::{
    TrustSpawnCensus, TrustSpawnRow, TrustSpawnSites, TrustSpawnVerdict,
};
use rustc_middle::mir::{self, Location, MentionedItem, TerminatorKind};
use rustc_middle::ty::adjustment::PointerCoercion;
use rustc_middle::ty::layout::{LayoutCx, TyAndLayout, ValidityRequirement};
use rustc_middle::ty::{
    self, GenericArgKind, GenericArgs, Instance, InstanceKind, ShimKind, Ty, TyCtxt,
    TypeVisitableExt,
};
use rustc_span::def_id::{DefId, LocalDefId};
use rustc_span::{DUMMY_SP, Span, Symbol, sym};
use trust_ir::analysis::{ArgClass, CarriedKey, FnShape, MethodKey, PoolKey, PrincipalKey};
use trust_ir::function_dependencies::{
    DefinitionKey, DependencyRefusalKind, DerivedOrder, EdgeClass, Locality, NodeBody, NodeOrigin,
    ReachCensus, ReachEdge, ReachGraph, ReachNode, ReachNodeKind, ReachNodeSpec, ReachSite,
    Verdict,
};

mod sealed;
mod writer_origins;

pub use sealed::{SealDecl, check_seals};

// ---------------------------------------------------------------------------
// Seeds
// ---------------------------------------------------------------------------

/// A recognized standard-library thread creation entry point: a SEED of the
/// census. The `DefId`, not a source-spellable function name, supplies the
/// identity: std's own `rustc_diagnostic_item`s on `thread::spawn`,
/// `Builder::spawn`, `Builder::spawn_unchecked`, `Builder::spawn_scoped` and
/// `Scope::spawn` -- also the off-thread edges of `trust_once_reentrancy`. A
/// diagnostic item is independent of printing, re-exports and trimming (an
/// untrimmed `def_path_str` table once missed `Scope::spawn`). The item alone
/// is not identity -- any crate may declare one under `rustc_attrs` -- so the
/// item must also live in the real sysroot `std`.
pub fn is_std_thread_spawn(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    tcx.crate_name(def_id.krate) == sym::std
        && matches!(
            tcx.get_diagnostic_name(def_id),
            Some(
                sym::thread_spawn
                    | sym::thread_builder_spawn
                    | sym::thread_builder_spawn_unchecked
                    | sym::thread_builder_spawn_scoped
                    | sym::thread_scope_spawn
            )
        )
        && crate::def_is_in_real_sysroot_crate(tcx, def_id)
}

/// A std channel send: `send` on `std::sync::mpsc::Sender` (std's
/// `MpscSender` diagnostic item) or `std::sync::mpsc::SyncSender`, in the real
/// sysroot `std`. What the send census (`-Ztrust-send-census`) looks for in
/// each thread's reach; winit's `EventLoopProxy::send_event` is generic, so
/// its MIR is walked and ends here.
pub fn is_std_channel_send(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    if tcx.crate_name(def_id.krate) != sym::std
        || !crate::def_is_in_real_sysroot_crate(tcx, def_id)
        || tcx
            .opt_item_name(def_id)
            .is_none_or(|name| !matches!(name.as_str(), "send" | "try_send"))
    {
        return false;
    }
    let Some(owner) = tcx.impl_of_assoc(def_id) else { return false };
    let ty::Adt(adt, _) = *tcx.type_of(owner).instantiate_identity().skip_norm_wip().kind() else {
        return false;
    };
    let named =
        tcx.get_diagnostic_name(adt.did()).is_some_and(|name| name.as_str() == "MpscSender");
    // By the module's own name, not a printed path: `def_path_str` trims
    // paths in a diagnostic session, and `std::sync::mpsc` prints as `mpsc`.
    let sync = tcx.item_name(adt.did()).as_str() == "SyncSender"
        && tcx.opt_item_name(tcx.parent(adt.did())).is_some_and(|name| name.as_str() == "mpsc");
    named || sync
}

/// Whether `def_id` takes messages off a std channel: `recv`, `try_recv`,
/// `recv_timeout`, `recv_deadline`, `iter`, `try_iter` or `into_iter` on
/// `std::sync::mpsc::Receiver`.
/// Whether `def_id` is in std's module `module` (at any depth), by the
/// modules' own names.
fn in_std_module(tcx: TyCtxt<'_>, def_id: DefId, module: &str) -> bool {
    if tcx.crate_name(def_id.krate) != sym::std || !crate::def_is_in_real_sysroot_crate(tcx, def_id)
    {
        return false;
    }
    let mut at = def_id;
    while let Some(parent) = tcx.opt_parent(at) {
        if tcx.opt_item_name(parent).is_some_and(|name| name.as_str() == module) {
            return true;
        }
        at = parent;
    }
    false
}

/// Whether `def_id` is what `mpsc`'s `send` and `try_send` run inside std:
/// `send` or `try_send` of `std::sync::mpmc`'s `Sender` and of its three
/// channel flavors. A dependency built with optimization ships its generic
/// code with `mpsc::Sender::send` already inlined, so in the census's graph
/// the send is one of these ([`is_std_channel_send`] finds none). A thread
/// that calls `mpsc`'s own `send` reaches these too, from inside the channel
/// code, where they are not counted again.
pub fn is_std_channel_send_inside(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    tcx.opt_item_name(def_id).is_some_and(|name| matches!(name.as_str(), "send" | "try_send"))
        && tcx.impl_of_assoc(def_id).is_some()
        && in_std_module(tcx, def_id, "mpmc")
}

pub fn is_std_channel_recv(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    const RECEIVES: [&str; 7] =
        ["recv", "try_recv", "recv_timeout", "recv_deadline", "iter", "try_iter", "into_iter"];
    if tcx.crate_name(def_id.krate) != sym::std
        || !crate::def_is_in_real_sysroot_crate(tcx, def_id)
        || tcx.opt_item_name(def_id).is_none_or(|name| !RECEIVES.contains(&name.as_str()))
    {
        return false;
    }
    let Some(owner) = tcx.impl_of_assoc(def_id) else { return false };
    let ty::Adt(adt, _) = *tcx.type_of(owner).instantiate_identity().skip_norm_wip().kind() else {
        return false;
    };
    tcx.get_diagnostic_name(adt.did()).is_some_and(|name| name.as_str() == "MpscReceiver")
}

// ---------------------------------------------------------------------------
// Row kinds
// ---------------------------------------------------------------------------

/// The kind of one refused site (design §5.5). Only the three SPAWNS kinds
/// claim a spawn ([`SpawnRowKind::claims_spawn`]); every other kind refuses
/// without claiming one.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum SpawnRowKind {
    /// SPAWNS (S1): the call runs a std thread-creation entry point.
    DirectSpawn,
    /// SPAWNS (S2): the call runs, exactly, a body that reaches a spawn over
    /// calls and drops only (a `const`-false branch and an unwind cleanup path
    /// count: the row says "reaches"). `local`: that body is the crate's own.
    CallSpawns { local: bool },
    /// SPAWNS (S3): the value dropped here has drop glue that reaches a spawn.
    /// `local_drop`: a local `Drop` impl is on the path.
    DropSpawns { local_drop: bool },
    /// ESCAPES: a callable that reaches a spawn is made into a fn pointer or a
    /// `dyn` value here (a reified fn item, a closure cast to a fn pointer, a
    /// vtable method or drop slot, a fn pointer in a constant).
    CreatesSpawning,
    /// ESCAPES: a callable made into a fn pointer or `dyn` value here does not
    /// reach a spawn itself when called, but names, erases or reads one that
    /// does (`fn mk() -> fn() { launch }` reified).
    CreatesEscaping,
    /// ESCAPES: a value handed here to code with no body to walk (foreign
    /// code, MIR-less Rust), which may drop it, has drop glue that reaches a
    /// spawn.
    HandsDropGlue,
    /// ESCAPES: a `const` or `static` (or thread-local) read here holds one.
    ReadsSpawning,
    /// ESCAPES: the callee does one of these.
    CalleeEscapes,
    /// INDIRECT: an indirect call here (a fn pointer, a `dyn` method or drop),
    /// or a hand-off of a callable to external code that calls its key, may
    /// reach a spawn through its pool (`IndirectCallMaySpawn`).
    IndirectCallMaySpawn,
    /// INDIRECT: the callee, value or callable here reaches such a call.
    ReachesIndirect,
    /// UNKNOWN: the site reaches code the census could not enumerate.
    NotEnumerated,
}

impl SpawnRowKind {
    /// Whether a row of this kind claims a spawn (S1-S3).
    pub fn claims_spawn(self) -> bool {
        matches!(
            self,
            SpawnRowKind::DirectSpawn
                | SpawnRowKind::CallSpawns { .. }
                | SpawnRowKind::DropSpawns { .. }
        )
    }

    /// The verdict a row of this kind carries.
    pub fn verdict(self) -> TrustSpawnVerdict {
        match self {
            SpawnRowKind::DirectSpawn
            | SpawnRowKind::CallSpawns { .. }
            | SpawnRowKind::DropSpawns { .. } => TrustSpawnVerdict::Spawns,
            SpawnRowKind::CreatesSpawning
            | SpawnRowKind::CreatesEscaping
            | SpawnRowKind::HandsDropGlue
            | SpawnRowKind::ReadsSpawning
            | SpawnRowKind::CalleeEscapes => TrustSpawnVerdict::Escapes,
            SpawnRowKind::IndirectCallMaySpawn | SpawnRowKind::ReachesIndirect => {
                TrustSpawnVerdict::Indirect
            }
            SpawnRowKind::NotEnumerated => TrustSpawnVerdict::Unknown,
        }
    }

    /// The row detail. `witness` is the shortest admitted path the engine
    /// found from the site's target (empty when there is none to cite).
    pub fn text(self, witness: &str) -> String {
        let via = |prefix: &str| {
            if witness.is_empty() { String::new() } else { format!(" ({prefix}{witness})") }
        };
        match self {
            SpawnRowKind::DirectSpawn => {
                "direct std thread spawn lacks an authenticated execution and race model".into()
            }
            SpawnRowKind::CallSpawns { local: true } => format!(
                "local callee reaches a std thread spawn through calls and drops; caller effect is \
                 unmodeled{}",
                via("via ")
            ),
            SpawnRowKind::CallSpawns { local: false } => format!(
                "callee reaches a std thread spawn through calls and drops; caller effect is \
                 unmodeled{}",
                via("via ")
            ),
            SpawnRowKind::DropSpawns { local_drop: true } => format!(
                "value dropped here has drop glue that may run a local Drop impl that reaches a \
                 std thread spawn through calls and drops; drop effect is unmodeled{}",
                via("via ")
            ),
            SpawnRowKind::DropSpawns { local_drop: false } => format!(
                "value dropped here has drop glue that reaches a std thread spawn through calls \
                 and drops; drop effect is unmodeled{}",
                via("via ")
            ),
            SpawnRowKind::CreatesSpawning => format!(
                "callable made into a fn pointer or `dyn` value here reaches a std thread spawn \
                 when called; the calls through it are not enumerated at this site; effect is \
                 unmodeled (fail-closed; not a spawn claim){}",
                via("via ")
            ),
            SpawnRowKind::CreatesEscaping => format!(
                "callable made into a fn pointer or `dyn` value here, when called, names, erases \
                 or reads a callable that reaches a std thread spawn; the calls through it are \
                 not enumerated at this site; effect is unmodeled (fail-closed; not a spawn \
                 claim){}",
                via("via ")
            ),
            SpawnRowKind::HandsDropGlue => format!(
                "value handed here to code the spawn census cannot walk (foreign or MIR-less) \
                 has drop glue that reaches a std thread spawn; whether that code drops it is \
                 not enumerated; effect is unmodeled (fail-closed; not a spawn claim){}",
                via("via ")
            ),
            SpawnRowKind::ReadsSpawning => format!(
                "const or static read here holds a callable that reaches a std thread spawn; the \
                 calls through it are not enumerated at this site; effect is unmodeled \
                 (fail-closed; not a spawn claim){}",
                via("via ")
            ),
            SpawnRowKind::CalleeEscapes => format!(
                "callee names, erases or reads a callable that reaches a std thread spawn; effect \
                 is unmodeled (fail-closed; not a spawn claim){}",
                via("via ")
            ),
            SpawnRowKind::IndirectCallMaySpawn => format!(
                "may spawn (indirect): an indirect call, or a callable handed to external code \
                 that calls it, may run a callable of its key that reaches a std thread spawn; \
                 effect is unmodeled (fail-closed; not a spawn claim){}",
                via("via ")
            ),
            SpawnRowKind::ReachesIndirect => format!(
                "may spawn (indirect): the callee, value or callable here reaches an indirect \
                 call that may reach a std thread spawn; effect is unmodeled (fail-closed; not a \
                 spawn claim){}",
                via("via ")
            ),
            SpawnRowKind::NotEnumerated => format!(
                "not enumerated (no spawn was found): this site reaches code the spawn census \
                 could not enumerate; effect is unmodeled (fail-closed; not a spawn claim){}",
                via("via ")
            ),
        }
    }
}

/// The row of self-audit check 2 (design §5.6): the codegen body calls, drops,
/// unsizes, reifies, casts or panics into an item the census did not cover, so
/// a fact may be missing. Emitted by TrustVerify, which holds the codegen body.
pub fn uncovered_mention_text(item: &MentionedItem<'_>) -> String {
    format!(
        "not enumerated (no spawn was found): the codegen MIR of this body mentions {}, which \
         the spawn census did not cover (self-audit); effect is unmodeled (fail-closed; not a \
         spawn claim)",
        cut(format!("{item:?}"))
    )
}

/// A rendered item or type cut to 120 characters: drop glue of a type that
/// spans thousands of instantiations renders as hundreds of kilobytes, more
/// than a verifier diagnostic may carry, and every row prints twice.
fn cut(name: String) -> String {
    match name.char_indices().nth(120) {
        Some((end, _)) => format!("{}…", &name[..end]),
        None => name,
    }
}

/// The row for a body whose verdict refuses but none of whose own sites does
/// (a concrete instance whose evidence lies elsewhere).
pub fn unsited_verdict_text(verdict: TrustSpawnVerdict) -> String {
    match verdict {
        TrustSpawnVerdict::Spawns => "a concrete instance of this body reaches a std thread spawn \
             through calls and drops (its rows are at that instance's sites); effect is unmodeled"
            .to_string(),
        other => format!(
            "the spawn census's verdict for this body is {other:?}, with no site in it carrying \
             the evidence; effect is unmodeled (fail-closed; not a spawn claim)"
        ),
    }
}

/// The panic entry point a MIR `Assert` calls when its check fails: the one
/// lang item both the census (an edge) and TrustVerify's self-audit (check 2,
/// on the codegen body) read, so the two cannot disagree on it.
pub fn assert_panic_lang_item(msg: &mir::AssertKind<mir::Operand<'_>>) -> LangItem {
    match msg {
        mir::AssertKind::BoundsCheck { .. } => LangItem::PanicBoundsCheck,
        mir::AssertKind::MisalignedPointerDereference { .. } => {
            LangItem::PanicMisalignedPointerDereference
        }
        mir::AssertKind::NullPointerDereference => LangItem::PanicNullPointerDereference,
        mir::AssertKind::NullReferenceConstructed => LangItem::PanicNullReferenceConstructed,
        mir::AssertKind::InvalidEnumConstruction(_) => LangItem::PanicInvalidEnumConstruction,
        other => other.panic_function(),
    }
}

/// How a panic or unwind-termination lang item a body calls is recorded among
/// the items the census covered in it (self-audit check 2): as a mention of
/// the lang item's fn.
pub fn lang_item_mention<'tcx>(tcx: TyCtxt<'tcx>, item: LangItem) -> Option<MentionedItem<'tcx>> {
    let def = tcx.lang_items().get(item)?;
    Some(MentionedItem::Fn(Ty::new_fn_def(
        tcx,
        def,
        ty::Binder::dummy(GenericArgs::identity_for_item(tcx, def)),
    )))
}

// ---------------------------------------------------------------------------
// What the compiler supplies
// ---------------------------------------------------------------------------

/// What the adapter needs from `rustc_mir_transform`, which depends on this
/// crate and so cannot be named from it.
pub trait CensusHooks<'tcx> {
    /// Run `f` on the PRE-STEAL runtime MIR of the local fn, closure or
    /// coroutine `def` (`mir_drops_elaborated_and_const_checked`, borrowed),
    /// never on its `optimized_mir`. Legal only before any such body is
    /// stolen: the census is forced at the analysis seam.
    fn with_local_body(&self, def: LocalDefId, f: &mut dyn FnMut(&mir::Body<'tcx>));
    /// rustc's own `MentionedItems` enumeration of `body`, with locations
    /// (`mentioned_items::for_each_mentioned_item`).
    fn for_each_mentioned_item(
        &self,
        body: &mir::Body<'tcx>,
        f: &mut dyn FnMut(MentionedItem<'tcx>, Span, Location),
    );
    /// Whether `def` is a Clean-origin def (R5).
    fn is_clean_origin(&self, def: LocalDefId) -> bool;
    /// Whether TrustVerify may install a kernel-certified runtime monitor in
    /// `def` (a contract owner in a monitored test session): a call of
    /// `core::contracts::certified_monitor_check` added after the census read
    /// the body, which the census charges to it.
    fn may_carry_monitor(&self, def: LocalDefId) -> bool;
    /// The field bindings the crate's islands declare ([`FieldBinding`]).
    fn field_bindings(&self) -> Vec<FieldBinding> {
        Vec::new()
    }
}

/// A binding an island declares between a model and the code (design
/// 2026-09-29 §3c.2, the writers check): the field at `path` on a message
/// consumer's argument is written only from the arms for the variants in
/// `writers`, except by the fns in `carried_by`, which the declaration says
/// carry the value over without changing it. The census checks every write
/// site it finds against that ([`check_binding`]) and fails the build at
/// `span` on any other.
#[derive(Clone, Debug)]
pub struct FieldBinding {
    /// The declaration's name in the island (`HarnessPolicy.policy`).
    pub name: String,
    /// The field path, as `-Ztrust-writer-census` takes it (`config.harness`).
    pub path: String,
    /// The message variants whose arms may write the field: a variant's name
    /// (`HarnessPolicyObserved`) or `Enum::Variant`.
    pub writers: Vec<String>,
    /// The fns whose writes are declared carry-overs: a fn's name, or
    /// `Type::method`.
    pub carried_by: Vec<String>,
    /// Where the declaration is.
    pub span: Span,
}

// ---------------------------------------------------------------------------
// The adapter
// ---------------------------------------------------------------------------

/// One node of the MIR lane's graph. `env` names the item whose generics the
/// key may still mention (`None`: fully concrete); identity instances keep
/// their own type parameters (design §5.3, Generics).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum Key<'tcx> {
    /// A body run as a function (`InstanceKind::Item`): a fn, closure,
    /// coroutine or an intrinsic's fallback body.
    Body { def: DefId, args: GenericArgs<'tcx>, env: Option<DefId> },
    /// A shim instance made into a callable value (a vtable slot, a fn
    /// pointer): what calling it runs.
    Shim { instance: Instance<'tcx>, env: Option<DefId> },
    /// A `const`, `static` or thread-local's value: a READ target.
    Value { def: DefId, args: GenericArgs<'tcx>, env: Option<DefId> },
    /// A promoted constant's value.
    Promoted { def: DefId, args: GenericArgs<'tcx>, promoted: mir::Promoted, env: Option<DefId> },
    /// The drop glue of a type, decomposed structurally.
    Drop { ty: Ty<'tcx>, env: Option<DefId> },
    /// The compiler's `Clone` shim of a tuple, array or closure.
    Clone { ty: Ty<'tcx>, env: Option<DefId> },
    /// A std thread-creation entry point.
    Seed(DefId),
    /// Code with no body to walk that the census assumes starts no thread
    /// itself: foreign code (R3), MIR-less external Rust (R2), a Clean-origin
    /// def (R5).
    Opaque(DefId),
    /// Code resolved per concrete instance (R1).
    Param,
    /// What runs when code the census cannot walk runs (design §5.4, rule H;
    /// §12, R2 and R3): every node of that code has a RUN edge here.
    Outside(World),
}

/// What this adapter knows of a node's body: the [`NodeBody`]s it can emit.
///
/// Trust: trust-ir's [`NodeBody`] also has `Primitive` (a body the engine
/// does not walk because the adapter emitted its checked
/// `PrimitiveSummary`'s facts instead; trust-ir C1 §3.2). This adapter
/// classifies no key as a primitive and emits no summary facts, so it never
/// adds such a node. Keeping its own closed enum makes that a property of
/// the type, not of a match arm: a primitive classification here would have
/// to add a variant and the summary walk that goes with it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum MirNodeBody {
    Walked,
    Opaque,
    Param,
    Seed,
}

impl MirNodeBody {
    /// The engine's body for a node of this kind.
    fn reach_body(self) -> NodeBody {
        match self {
            MirNodeBody::Walked => NodeBody::Walked,
            MirNodeBody::Opaque => NodeBody::Opaque,
            MirNodeBody::Param => NodeBody::Param,
            MirNodeBody::Seed => NodeBody::Seed,
        }
    }
}

/// The two kinds of code the census cannot walk, by what they can reach in
/// the program without being handed it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum World {
    /// Foreign code (R3) and module-level assembly: it can call what it is
    /// handed (now or earlier: a callback kept across calls), what it reads
    /// from memory it names or shares without being handed it (an `extern`
    /// static, a static it names by symbol or section, memory behind a
    /// pointer it returned or passed to Rust), and Rust functions it names by
    /// symbol (`#[no_mangle]`, `#[export_name]`).
    Foreign,
    /// Rust code with no MIR here (R2; an `extern "Rust"` declaration the
    /// crate graph does not define): everything foreign code can, and the
    /// crate graph's runtime registries, which Rust code reaches without
    /// being handed them: the global allocator, the alloc error handler and
    /// the panic handler (and through it the panic hook).
    Rust,
}

impl World {
    fn index(self) -> usize {
        match self {
            World::Foreign => 0,
            World::Rust => 1,
        }
    }
}

/// A TEST-ONLY fault the census injects into itself
/// (`TRUST_SPAWN_CENSUS_TEST_FAULT`, read through the tracked `env_var_os`
/// query), so that its self-audits are exercised end to end. Each can only
/// add refusals.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum TestFault {
    /// `forget-coverage`: record no panic lang item as covered, so self-audit
    /// check 2 must refuse every body whose codegen MIR can panic.
    ForgetCoverage,
    /// `defect`: add one malformed fact (an adapter APPROX edge), so the
    /// engine refuses every node UNKNOWN and the census reports its fallback.
    Defect,
}

/// How a body's facts are read.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Mode {
    /// Run time: calls run, drops drop, panics panic.
    Run,
    /// A `const`, `static` or promoted initializer: it runs at compile time,
    /// so only what its VALUE can hold matters. Calls are READ edges (the
    /// callee may return a callable), drops and panics are nothing.
    Const,
}

/// The body being visited.
#[derive(Clone, Copy)]
struct Frame<'tcx> {
    node: ReachNode,
    /// The local body rows are attributed to (a local Body node's own def).
    owner: Option<LocalDefId>,
    /// What MIR types are instantiated with.
    instance: Option<Instance<'tcx>>,
    env: Option<DefId>,
    typing_env: ty::TypingEnv<'tcx>,
    mode: Mode,
    locality: Locality,
}

/// `needs_drop` at the census boundary (RIGID-ALIAS-CENSUS-1): types read
/// from pre-steal elaborated MIR can carry rigid aliases, and the old trait
/// solver's `relate` debug-asserts it never sees one
/// (`compiler/rustc_infer/src/infer/relate/type_relating.rs`: "We don't use
/// the rigid marker in the old solver"), so a debug-assertions stage1 ICEs
/// in `needs_drop_raw -> is_copy_raw -> evaluate_obligation` under
/// `-Znext-solver=coherence`. The census runs post-analysis, where aliases
/// are normalizeable, so state that on the type before asking — the same
/// renormalization `PostAnalysisNormalize` performs before codegen queries.
fn census_needs_drop<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    ty: Ty<'tcx>,
) -> bool {
    ty::set_aliases_to_non_rigid(tcx, ty).skip_norm_wip().needs_drop(tcx, typing_env)
}

/// What a value of a type holds in its OWN bytes, not behind its pointers:
/// the census's model of a reinterpretation (design §10, "typed LAUNDER").
#[derive(Clone, Default)]
struct OwnBytes<'tcx> {
    /// `CarriedKey::Key(PoolKey::Fn(_))` for each fn pointer, and
    /// `CarriedKey::Any` for bytes the census cannot read (past the
    /// recursion limit, a type it cannot normalize, a coroutine whose saved
    /// state it cannot read).
    callables: BTreeSet<CarriedKey>,
    /// The type of each fn pointer: a call through one of them at another
    /// fn-pointer type of a matching shape reads its arguments and return
    /// value at the other's types (route S, [`Walker::signature_positions`]).
    fn_ptrs: Vec<Ty<'tcx>>,
    /// A position that holds no callable: a scalar, a pointer's address or
    /// metadata. A `dyn` pointer's vtable word is no callable in data
    /// (SC-7c): Rust reaches a vtable slot only through the fat pointer's
    /// method or drop call, which its pool charges, and reading a vtable's
    /// bytes is UB (R4).
    other: bool,
    /// The pointee of each pointer.
    pointees: Vec<Ty<'tcx>>,
    /// The principals of `dyn` values held by value (an unsized tail): their
    /// bytes are some concrete object's.
    objects: Vec<PrincipalKey>,
    /// The types `PhantomData`s name: what the value owns behind pointers
    /// that do not name it (`Vec<T>`'s buffer is a `Unique<u8>`).
    phantoms: Vec<Ty<'tcx>>,
    /// A position may hold a pointer's bytes, provenance included, at a type
    /// that names no pointee: a union's (`MaybeUninit`'s), `c_void`, an extern
    /// type ([`Self::untyped_view`]).
    untyped: bool,
    /// Part of the value is a type parameter or an unnormalized alias: its
    /// concrete instances record what that part holds (R1).
    param: bool,
}

impl OwnBytes<'_> {
    /// No byte position the census knows of. An untyped position (`c_void`,
    /// a union's) is one: `[c_void; 8]` has bytes a pointer's may sit in.
    fn positionless(&self) -> bool {
        self.callables.is_empty()
            && !self.other
            && !self.untyped
            && self.pointees.is_empty()
            && self.objects.is_empty()
    }

    /// Memory viewed at this type keeps no pointer's pointee type: it has
    /// untyped positions, or none at all (`()`, a zero-sized type). A pointer
    /// to it may later be re-viewed at any type, and that re-view reads, as
    /// whatever it likes, the pointers the memory holds, so viewing typed
    /// memory this way must record everything behind them.
    fn untyped_view(&self) -> bool {
        self.untyped || (self.positionless() && !self.param)
    }
}

/// A typed LAUNDER's key while the walk runs (design §10, "typed LAUNDER"):
/// resolved to [`CarriedKey`]s by [`Walker::resolve_launder`] once every
/// principal's concrete types are known.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum LaunderKey<'tcx> {
    /// A callable key of the reinterpreted bytes (`Key(Fn(_))` or `Any`).
    Key(CarriedKey),
    /// The concrete objects of a `dyn` principal viewed as `as_`, and `as_`
    /// viewed as them: a thin view of a `dyn` object reads some concrete
    /// object's own bytes, never its vtable (SC-7c).
    Objects { principal: PrincipalKey, as_: Ty<'tcx> },
    /// Every callable a value of this type holds, in its own bytes or behind
    /// its pointers: an exposed allocation (SC-7b), or memory a view keeps no
    /// pointee type of.
    Reach(Ty<'tcx>),
    /// Every callable a `dyn` value of this principal holds ([`Self::Reach`]
    /// of each concrete object).
    ReachObjects(PrincipalKey),
}

/// A held typed LAUNDER's keys and typing environment, as
/// [`Walker::deferred_launders`] files it.
type LaunderEntry<'tcx> = (Rc<Vec<LaunderKey<'tcx>>>, ty::TypingEnv<'tcx>);

/// A type with what a reinterpretation cannot change stripped
/// ([`Walker::peel`]).
#[derive(Clone, Copy, PartialEq, Eq)]
enum Peeled<'tcx> {
    Ty(Ty<'tcx>),
    /// A `dyn` type, by its principal (auto traits ignored).
    Dyn(PrincipalKey),
}

/// How the pointer that reaches a constant allocation types it (route C,
/// design §10, "typed LAUNDER").
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Typing<'tcx> {
    /// Nothing is known: every fn pointer in it may be held as data.
    Untyped,
    /// A fn-pointer position of this fn-pointer type (what a
    /// `GlobalAlloc::Function` is reached from).
    Fn(Ty<'tcx>),
    /// A value of this type at this offset (a reference's pointee, a
    /// static's or constant's value).
    At(Ty<'tcx>, u64),
    /// Values of this type from this offset to the allocation's end (a slice
    /// reference's elements).
    Elements(Ty<'tcx>, u64),
    /// Not checked here: a nested static's bytes, which the pointer its
    /// parent static holds types (they are reached only through it).
    Unchecked,
}

/// One pointer-sized position of a constant's type ([`Walker::slots`]).
#[derive(Clone, Debug, PartialEq, Eq)]
enum Slot<'tcx> {
    /// A fn pointer of this type.
    Fn(Ty<'tcx>),
    /// A reference or raw pointer to this type. The memory behind it is read
    /// at that type: a fn pointer it holds is kept only at a fn-pointer
    /// position of a matching shape, and any other is recorded, so a typing
    /// never hides one (unvalidated memory behind a raw pointer included; a
    /// second pointer that types the same memory otherwise is read again at
    /// its own type).
    Ptr(Ty<'tcx>),
    /// Two variants disagree.
    Conflict,
}

/// The pointer positions of a constant's type, by offset, and the byte
/// ranges of its unions (whose bytes no type names).
#[derive(Default)]
struct Slots<'tcx> {
    at: FxHashMap<u64, Slot<'tcx>>,
    opaque: Vec<(u64, u64)>,
}

impl<'tcx> Slots<'tcx> {
    fn insert(&mut self, offset: u64, slot: Slot<'tcx>) {
        self.at
            .entry(offset)
            .and_modify(|held| {
                if *held != slot {
                    *held = Slot::Conflict
                }
            })
            .or_insert(slot);
    }

    fn get(&self, offset: u64) -> Option<&Slot<'tcx>> {
        if self.opaque.iter().any(|&(start, end)| start <= offset && offset < end) {
            return None;
        }
        self.at.get(&offset)
    }
}

/// SC-7d: the sysroot's own unions whose fields are read only as last
/// written, guarded by state the sysroot keeps (`LazyLock`'s `Once`,
/// `catch_unwind`'s intrinsic contract; `MaybeUninit`, a lang item, its
/// initialization contract). Projected in a sysroot body, they are no pun
/// site. The list is explicit: any other union is a pun site wherever it is
/// projected.
const SYSROOT_STATE_GUARDED_UNIONS: &[&str] =
    &["std::sync::lazy_lock::Data", "std::panicking::catch_unwind::Data"];

/// How many pointee pairs one reinterpretation may expand, how many keys one
/// typed LAUNDER may resolve through, and how many types one reach may visit,
/// before it is a LAUNDER of `Any`.
const LAUNDER_BUDGET: usize = 1 << 14;

/// Run the census over the whole crate: walk every local body and constant
/// and what they reach, solve, and render the answer the
/// `trust_spawn_census` query returns.
pub fn spawn_census<'tcx>(
    tcx: TyCtxt<'tcx>,
    hooks: &dyn CensusHooks<'tcx>,
) -> TrustSpawnCensus<'tcx> {
    let mut walker = Walker::new(tcx, hooks);
    walker.add_roots();
    walker.add_exported_members();
    walker.run();
    walker.finish()
}

struct Walker<'h, 'tcx> {
    tcx: TyCtxt<'tcx>,
    hooks: &'h dyn CensusHooks<'tcx>,
    graph: ReachGraph,
    nodes: FxHashMap<Key<'tcx>, ReachNode>,
    keys: Vec<Key<'tcx>>,
    pending: VecDeque<Key<'tcx>>,
    /// Site id -> (the local body a row lands in, the span).
    sites: Vec<(Option<LocalDefId>, Span)>,
    /// The site of facts no local body owns (inside drop glue, shims, values).
    internal: ReachSite,
    /// Local bodies walked, sorted by `DefIndex` (each gets an answer).
    roots: Vec<LocalDefId>,
    covered: FxHashMap<LocalDefId, Vec<MentionedItem<'tcx>>>,
    /// The Rust definitions the crate graph links under a symbol, by name.
    symbols: Option<SymbolTables>,
    /// [`Self::carried`] by type and typing environment ([`memo_env`]).
    carried: FxHashMap<(Ty<'tcx>, ty::TypingEnv<'tcx>), Rc<[CarriedKey]>>,
    /// The ADT definitions some type walk found polymorphically recursive
    /// ([`Entered::enter`]): no walk enters one again.
    unbounded: FxHashSet<DefId>,
    /// The calls refused for a limit of the census's own (a type near the
    /// recursion limit, too many instances of one body): what such a call
    /// runs is not in the graph, and a check built on the graph says so.
    cuts: Vec<ReachSite>,
    /// The body just asked for was refused for such a limit.
    cut: bool,
    /// Nodes with no body to walk (R2, R3, R5).
    opaque: FxHashSet<ReachNode>,
    /// `(depth, size)` for each measured type: maximal nesting depth and how
    /// many types it is built from, counted as a tree.
    type_metrics: FxHashMap<Ty<'tcx>, (usize, u32)>,
    /// [`TYPE_MEMO_BUDGET`] spent: [`Self::nesting`] answers past-limit for
    /// every type not already measured.
    depth_budget_exhausted: bool,
    /// How many instances of each generic body have a node.
    instances_of: FxHashMap<DefId, usize>,
    limit: usize,
    /// UNKNOWN sinks by reason, with the first node that met one (for the
    /// census's own measurement, design §10 P2m).
    sinks: BTreeMap<String, (usize, String)>,
    /// Each of [`Self::sinks`]' reasons as a row names it ([`sink_text`]), for
    /// the SC-8 root-cause disclosure ([`unclosed_root_cause`]).
    sink_texts: BTreeMap<String, String>,
    /// Which node a key interned to, by handle, for those measurements.
    node_keys: FxHashMap<ReachNode, usize>,
    /// Memoized [`PrincipalKey`] by interned existential predicate list.
    principal_keys:
        std::cell::RefCell<FxHashMap<&'tcx ty::List<ty::PolyExistentialPredicate<'tcx>>, PrincipalKey>>,
    /// The `dyn` predicate list each principal key stands for.
    principals:
        std::cell::RefCell<FxHashMap<u64, &'tcx ty::List<ty::PolyExistentialPredicate<'tcx>>>>,
    /// Principals an invoke or a hand-off names.
    named: BTreeSet<PrincipalKey>,
    /// The node whose fact first named each principal (`TRUST_SPAWN_CENSUS_DEBUG`).
    named_at: FxHashMap<PrincipalKey, ReachNode>,
    /// The first LAUNDER, for the census's own measurement.
    launder_at: Option<String>,
    /// What every monomorphic sysroot body mints, by principal (built on the
    /// first open principal), and the principals already looked up in it.
    sysroot_creates: Option<SysrootCreates<'tcx>>,
    searched: BTreeSet<PrincipalKey>,
    /// Principals some vtable joined (walked or scanned), and every upcast
    /// added: what [`Self::settle_pending`] reads to decide which `dyn` values
    /// can exist.
    minted: BTreeSet<PrincipalKey>,
    upcasts: BTreeSet<(PrincipalKey, PrincipalKey)>,
    /// Scanned vtables and upcasts whose values cannot exist yet.
    pending_creates: Vec<(Ty<'tcx>, &'tcx ty::List<ty::PolyExistentialPredicate<'tcx>>)>,
    pending_upcasts: Vec<(PrincipalKey, PrincipalKey)>,
    /// Principals a value minted outside the walked world may carry into it:
    /// what a local body receives as an argument, what MIR-less or foreign
    /// code returns to one, what a mutable static holds.
    entering: BTreeSet<PrincipalKey>,
    /// Every indirect call and hand-off, held until [`Self::emit_pool_facts`].
    deferred_invokes: Vec<(ReachNode, PoolKey, Vec<CarriedKey>, ReachSite, bool)>,
    deferred_handoffs: Vec<(ReachNode, ReachNode, Vec<CarriedKey>, ReachSite, bool)>,
    /// How many indirect calls named a principal no value of which can exist
    /// (`TRUST_SPAWN_CENSUS_DEBUG`).
    dead_invokes: usize,
    /// Each world's node, once code of that world is reached.
    outside: [Option<ReachNode>; 2],
    /// The opaque nodes that are code of a world (foreign, MIR-less Rust): a
    /// Clean-origin def (R5) is opaque too, but in neither world.
    world_of: FxHashMap<ReachNode, World>,
    /// What each world can call without being handed it: Rust functions the
    /// crate graph exports by symbol and the values of the statics foreign
    /// code names ([`static_named_by_foreign_code`]) (foreign), and the
    /// runtime registries (Rust).
    world_members: [Vec<ReachNode>; 2],
    /// What frames outside the sysroot handed code of a world, which it may
    /// keep and call from any later call into it (a registered callback), and
    /// what Rust may store in memory foreign code reads without being handed
    /// it ([`Self::foreign_memory`]).
    handed_out: BTreeSet<CarriedKey>,
    /// The `extern` statics [`Self::touch_static`] has charged.
    charged_statics: FxHashSet<DefId>,
    /// Pool keys some member of which is code of a world: a local indirect
    /// call that may reach one hands it its operands (rule H at an indirect
    /// call), so they are handed out too.
    world_member_keys: Vec<PoolKey>,
    /// Nodes of local bodies (`Locality::Local`).
    local_nodes: FxHashSet<ReachNode>,
    /// The nodes of every invoke and hand-off fact at a site a local body
    /// owns: the only nodes whose engine-derived edges can be rows.
    fact_owners: FxHashSet<ReachNode>,
    /// The principals some confined vtable joined ([`Self::vtable`]).
    confined_principals: BTreeSet<PrincipalKey>,
    /// Every drop a local frame makes of a value that may carry a `dyn`
    /// value, held until [`Self::emit_pool_facts`] ([`Self::drop_handoff`]).
    deferred_drop_handoffs: Vec<(ReachNode, ReachNode, Vec<CarriedKey>, ReachSite)>,
    /// The principals each type's unions carry ([`Self::erase_lifetimes`]),
    /// by type and typing environment ([`memo_env`]).
    union_principals: FxHashMap<(Ty<'tcx>, ty::TypingEnv<'tcx>), Vec<PrincipalKey>>,
    /// A reinterpretation of a value whose callables the adapter cannot name
    /// (an opaque value, a union past the recursion limit) was seen: every
    /// confined member is demoted ([`Self::emit_pool_facts`]).
    demote_all_confined: bool,
    /// Typed LAUNDERs (design §10, "typed LAUNDER": routes P, U, S, A and
    /// C), held until [`Self::emit_pool_facts`], when every principal's
    /// concrete types are known: by keys and typing environment, the first
    /// site, its node, and what it reinterpreted (`TRUST_SPAWN_CENSUS_DEBUG`).
    deferred_launders: rustc_data_structures::fx::FxIndexMap<
        (Rc<Vec<LaunderKey<'tcx>>>, ty::TypingEnv<'tcx>),
        (ReachSite, ReachNode, Option<String>),
    >,
    /// The concrete types each principal's vtables joined for (walked or
    /// scanned), in the order they joined: what a thin view of a `dyn` object
    /// reads.
    concrete_of: BTreeMap<PrincipalKey, FxIndexSet<Ty<'tcx>>>,
    /// [`OwnBytes`] by type (and typing environment, for a type a generic's
    /// environment normalizes: [`memo_env`]).
    own_bytes: FxHashMap<(Ty<'tcx>, ty::TypingEnv<'tcx>), Rc<OwnBytes<'tcx>>>,
    /// A reinterpreting cast's keys by (source, target, exposes) and typing
    /// environment ([`memo_env`]).
    puns: FxHashMap<(Ty<'tcx>, Ty<'tcx>, bool, ty::TypingEnv<'tcx>), Rc<Vec<LaunderKey<'tcx>>>>,
    /// A field projection's keys (route F) by (base, field) and typing
    /// environment ([`memo_env`]).
    field_views: FxHashMap<(Ty<'tcx>, Ty<'tcx>, ty::TypingEnv<'tcx>), Rc<Vec<LaunderKey<'tcx>>>>,
    /// [`Self::reach`] by type and typing environment ([`memo_env`]): the
    /// callables and the `dyn` principals a value leads to.
    reaches: FxHashMap<
        (Ty<'tcx>, ty::TypingEnv<'tcx>),
        Rc<(BTreeSet<CarriedKey>, BTreeSet<PrincipalKey>)>,
    >,
    /// The last [`Self::name_launder_principals`] round's resolution of each
    /// held typed LAUNDER it resolved, with [`Self::launder_inputs`] as the
    /// round read them: [`Self::emit_pool_facts`] takes a resolution from here
    /// when those inputs have not changed since.
    settled_launders: Option<([usize; 4], FxHashMap<LaunderEntry<'tcx>, BTreeSet<CarriedKey>>)>,
    /// Unions whose fields' pun is recorded (route U), by type and typing
    /// environment ([`memo_env`]).
    punned_unions: FxHashSet<(Ty<'tcx>, ty::TypingEnv<'tcx>)>,
    /// Each laundered key with the first reinterpretation that put it into
    /// data (`TRUST_SPAWN_CENSUS_DEBUG`).
    laundered_at: BTreeMap<CarriedKey, String>,
    /// `TRUST_SPAWN_CENSUS_DEBUG` is set.
    debug: bool,
    /// The test-only fault in force, if any.
    fault: Option<TestFault>,
}

/// The symbol tables of the crate graph (local definitions, and every crate's
/// [`linked_candidates`]): what a foreign declaration links to. Both
/// census lanes resolve foreign symbols with them (the trust-ir lane is
/// `trust_thir_lower::spawn_census`), so the two read one rule.
pub struct SymbolTables {
    /// `#[rustc_std_internal_symbol]` runtime symbols, by item name.
    internal: FxHashMap<Symbol, DefId>,
    /// Functions linked under a name of their own (`#[no_mangle]`,
    /// `#[export_name]`), by that name: what a foreign declaration with that
    /// link name calls, and what foreign code can name.
    exported: FxHashMap<Symbol, DefId>,
}

impl SymbolTables {
    /// The Rust functions the crate graph links under a symbol (the local
    /// crate's definitions and each dependency's exported symbols): the
    /// std-internal runtime symbols by item name, and every function with a
    /// link name of its own (`#[no_mangle]`: its name; `#[export_name]`).
    pub fn new(tcx: TyCtxt<'_>) -> Self {
        let mut tables =
            SymbolTables { internal: FxHashMap::default(), exported: FxHashMap::default() };
        let mut record = |def: DefId| {
            if tcx.is_foreign_item(def)
                || !matches!(tcx.def_kind(def), DefKind::Fn | DefKind::AssocFn)
            {
                return;
            }
            let attrs = tcx.codegen_fn_attrs(def);
            if attrs.flags.contains(CodegenFnAttrFlags::RUSTC_STD_INTERNAL_SYMBOL) {
                tables.internal.entry(tcx.item_name(def)).or_insert(def);
            } else if !in_sysroot(tcx, def.krate) {
                // The sysroot's own exports (`compiler_builtins`' `mem*` and
                // libm intrinsics, the platform shims) are the platform
                // runtime: they start no thread and call nothing they are
                // not handed, like foreign code (R3), and some are inline
                // assembly, which would be an UNKNOWN sink in every crate.
                if let Some(name) = attrs.symbol_name.or_else(|| {
                    attrs.flags.contains(CodegenFnAttrFlags::NO_MANGLE).then(|| tcx.item_name(def))
                }) {
                    tables.exported.entry(name).or_insert(def);
                }
            }
        };
        for def in tcx.hir_crate_items(()).definitions() {
            if matches!(tcx.def_kind(def), DefKind::Fn | DefKind::AssocFn) {
                record(def.to_def_id());
            }
        }
        for &krate in tcx.crates(()) {
            for def in linked_candidates(tcx, krate) {
                record(def);
            }
        }
        tables
    }

    /// The Rust function the foreign declaration `def` links to (design §5.4,
    /// Foreign symbols), if the crate graph defines one; `None` is foreign
    /// code (R3).
    pub fn link_target(&self, tcx: TyCtxt<'_>, def: DefId) -> Option<DefId> {
        // `panic_impl` is the panic handler (std's, or a `#![no_std]` crate's).
        if tcx.item_name(def) == sym::panic_impl && crate::def_is_in_real_sysroot_crate(tcx, def) {
            if let Some(handler) = tcx.lang_items().panic_impl() {
                if handler != def && !tcx.is_foreign_item(handler) {
                    return Some(handler);
                }
            }
        }
        let attrs = tcx.codegen_fn_attrs(def);
        if attrs.flags.contains(CodegenFnAttrFlags::RUSTC_STD_INTERNAL_SYMBOL) {
            return self.runtime_symbol(tcx.item_name(def));
        }
        // Any other declaration links to the Rust function the crate graph
        // exports under its link name (`#[link_name]`, else its own name).
        let name = attrs.symbol_name.unwrap_or_else(|| tcx.item_name(def));
        self.exported.get(&name).copied()
    }

    /// Every function the crate graph outside the sysroot links under a name of
    /// its own: what foreign code may call without being handed it.
    pub fn exported(&self) -> impl Iterator<Item = DefId> + '_ {
        self.exported.values().copied()
    }

    /// The definition of the std-internal runtime symbol `name`. The allocator
    /// shim forwards `__rust_<x>` to std's `__rdl_<x>` when no
    /// `#[global_allocator]` defines `__rust_<x>`.
    fn runtime_symbol(&self, name: Symbol) -> Option<DefId> {
        if let Some(target) = self.internal.get(&name) {
            return Some(*target);
        }
        let default = name
            .as_str()
            .strip_prefix("__rust_")
            .map(|rest| Symbol::intern(&format!("__rdl_{rest}")))?;
        self.internal.get(&default).copied()
    }
}

/// The `dyn` values the sysroot's monomorphic bodies mint: per principal, the
/// concrete types erased to it (and through which pointer), and the upcasts.
struct SysrootCreates<'tcx> {
    creates:
        BTreeMap<PrincipalKey, Vec<(Ty<'tcx>, &'tcx ty::List<ty::PolyExistentialPredicate<'tcx>>)>>,
    upcasts: BTreeSet<(PrincipalKey, PrincipalKey)>,
    bodies: usize,
}

/// How often a type walk may enter one ADT definition again along one path,
/// each time at a more deeply nested type. That is polymorphic recursion: one
/// such field is a chain the recursion limit ends, but two (`Nest<Option<T>>`
/// and `Nest<(T,)>`) are a tree of 2^limit types, which nothing ends. Ordinary
/// nesting enters a definition again at types that do not keep growing
/// (`Option<Box<Node>>` in `Node`, the wrappers inside std's collections).
const REENTRIES: usize = 8;

/// How far below the recursion limit a type's nesting must stay for the
/// census to ask rustc to resolve a call at it.
const RESOLVE_MARGIN: usize = 16;

/// How many instances of one generic body the census walks. A body that
/// calls itself at two larger types, neither of which doubles (`(T, u8)` and
/// `[T; 1]`), is a tree of instances no depth or size limit ends.
const BODY_INSTANCES: usize = 1 << 14;

/// How large a type the census reads: the types it is built from, counted
/// as a tree. No type a program writes comes near; one made by polymorphic
/// recursion that doubles (`(T, T)`) passes it at the 16th step.
const TYPE_NODES: u32 = 1 << 16;

/// How many distinct types the census memoizes a nesting depth for, in all.
/// A polymorphic-recursive family (`census_survives_a_recursive_family_of_arcs`)
/// manufactures distinct instantiations faster than any per-type bound ends
/// them: each is small enough alone, and there are unboundedly many. This
/// budget is a backstop only: the per-type [`TYPE_NODES`] early cut in
/// [`Walker::nesting`] is what ends that family in practice, and ordinary
/// censuses (including the monomorphic-sysroot scan) measure far fewer
/// types than this. Past it, [`Walker::nesting`] answers past-limit for
/// every type it has not already measured — the same fail-closed answer it
/// gives a type that is too large — so the census finishes with `Any`
/// where it would otherwise run until killed (measured on the 1.101
/// stage 1: one such test consumed 47 CPU-minutes and a third of the
/// machine's memory in unbounded distinct-type enumeration).
const TYPE_MEMO_BUDGET: usize = 1 << 22;

/// How many ADT instantiations one type walk enters in all. The re-entry
/// bound ends a path, not the tree: a type with six growing fields has 6^8
/// instantiations within it. No type of a real program comes near this many.
const WALK_ENTRIES: usize = 100_000;

/// The ADT definitions a type walk entered on its way to each type it has
/// pending, with the nesting depth of the type entered: linked lists in one
/// arena, so the walk copies no path per field.
struct Entered {
    links: Vec<(DefId, usize, u32)>,
}

impl Entered {
    /// The path of the walk's root: nothing entered.
    const ROOT: u32 = u32::MAX;

    fn new() -> Self {
        Entered { links: Vec::new() }
    }

    /// The path below `def`, entered at a type of nesting `depth` from
    /// `path`; or `None` when the walk already entered `def` [`REENTRIES`]
    /// times on that path, each at a deeper type than the time before.
    ///
    /// Such a definition goes into `unbounded`, and no walk enters it again:
    /// every walk that reaches it would be cut there and answer "anything",
    /// which is all the answer says however much of the tree was read first.
    /// Without that, each new root type (`A<u8>`, `&A<u8>`, `Box<A<u16>>`)
    /// walks the tree to the bound again, and a body names many.
    fn enter(
        &mut self,
        unbounded: &mut FxHashSet<DefId>,
        path: u32,
        def: DefId,
        depth: usize,
    ) -> Option<u32> {
        if unbounded.contains(&def) {
            return None;
        }
        // The ancestors of this definition that were entered at ever
        // shallower types, nearest first: one that is not shallower is
        // skipped, not the end of the count (a type that grows only every
        // second step, `Z<U, Option<T>>` in `Z<T, U>`, is growing too).
        let mut grown = 0;
        let mut shallower = depth;
        let mut at = path;
        while at != Self::ROOT {
            let (seen, seen_depth, parent) = self.links[at as usize];
            if seen == def && seen_depth < shallower {
                grown += 1;
                shallower = seen_depth;
            }
            at = parent;
        }
        if grown >= REENTRIES {
            unbounded.insert(def);
            return None;
        }
        // A backstop for what the rule above does not end. The definition
        // the walk entered most is what multiplied: it is not entered again,
        // or every root type would walk to the backstop once more.
        if self.links.len() >= WALK_ENTRIES {
            let mut entries: FxHashMap<DefId, usize> = FxHashMap::default();
            for (entered, _, _) in &self.links {
                *entries.entry(*entered).or_default() += 1;
            }
            let most = entries.into_iter().max_by_key(|(entered, count)| {
                (*count, entered.krate.as_u32(), entered.index.as_u32())
            });
            if let Some((most, _)) = most {
                unbounded.insert(most);
            }
            return None;
        }
        self.links.push((def, depth, path));
        Some((self.links.len() - 1) as u32)
    }
}

fn spawn_census_debug_enabled() -> bool {
    static ENABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ENABLED.get_or_init(|| std::env::var_os("TRUST_SPAWN_CENSUS_DEBUG").is_some())
}

impl<'h, 'tcx> Walker<'h, 'tcx> {
    fn new(tcx: TyCtxt<'tcx>, hooks: &'h dyn CensusHooks<'tcx>) -> Self {
        Walker {
            tcx,
            hooks,
            graph: ReachGraph::new(),
            nodes: FxHashMap::default(),
            keys: Vec::new(),
            pending: VecDeque::new(),
            sites: vec![(None, DUMMY_SP)],
            internal: ReachSite::Mir(0),
            roots: Vec::new(),
            covered: FxHashMap::default(),
            symbols: None,
            carried: FxHashMap::default(),
            unbounded: FxHashSet::default(),
            cuts: Vec::new(),
            cut: false,
            opaque: FxHashSet::default(),
            type_metrics: FxHashMap::default(),
            depth_budget_exhausted: false,
            instances_of: FxHashMap::default(),
            limit: tcx.recursion_limit().0,
            sinks: BTreeMap::new(),
            sink_texts: BTreeMap::new(),
            node_keys: FxHashMap::default(),
            principal_keys: Default::default(),
            principals: Default::default(),
            named: BTreeSet::new(),
            named_at: FxHashMap::default(),
            launder_at: None,
            sysroot_creates: None,
            minted: BTreeSet::new(),
            upcasts: BTreeSet::new(),
            pending_creates: Vec::new(),
            pending_upcasts: Vec::new(),
            entering: BTreeSet::new(),
            deferred_invokes: Vec::new(),
            deferred_handoffs: Vec::new(),
            dead_invokes: 0,
            searched: BTreeSet::new(),
            outside: [None, None],
            world_of: FxHashMap::default(),
            world_members: [Vec::new(), Vec::new()],
            handed_out: BTreeSet::new(),
            charged_statics: FxHashSet::default(),
            world_member_keys: Vec::new(),
            local_nodes: FxHashSet::default(),
            fact_owners: FxHashSet::default(),
            confined_principals: BTreeSet::new(),
            deferred_drop_handoffs: Vec::new(),
            union_principals: FxHashMap::default(),
            demote_all_confined: false,
            deferred_launders: Default::default(),
            concrete_of: BTreeMap::new(),
            own_bytes: FxHashMap::default(),
            puns: FxHashMap::default(),
            field_views: FxHashMap::default(),
            reaches: FxHashMap::default(),
            settled_launders: None,
            punned_unions: FxHashSet::default(),
            laundered_at: BTreeMap::new(),
            debug: spawn_census_debug_enabled(),
            fault: tcx.env_var_os(std::ffi::OsStr::new("TRUST_SPAWN_CENSUS_TEST_FAULT")).and_then(
                |value| match value.to_str() {
                    Some("forget-coverage") => Some(TestFault::ForgetCoverage),
                    Some("defect") => Some(TestFault::Defect),
                    _ => None,
                },
            ),
        }
    }

    // ----- roots ------------------------------------------------------------

    /// Every local body and constant is a root: bodies so each gets a
    /// verdict, constants so every callable they hold joins its pool.
    fn add_roots(&mut self) {
        let tcx = self.tcx;
        let mut defs: Vec<LocalDefId> = tcx.mir_keys(()).iter().copied().collect();
        defs.sort_unstable_by_key(|def| def.local_def_index.as_u32());
        for def in defs {
            match tcx.def_kind(def) {
                DefKind::Fn
                | DefKind::AssocFn
                | DefKind::Closure
                | DefKind::SyntheticCoroutineBody => {
                    if tcx.is_foreign_item(def) {
                        continue;
                    }
                    let args = self.identity_args(def.to_def_id());
                    let env = args.has_param().then(|| tcx.typeck_root_def_id(def.to_def_id()));
                    self.node(Key::Body { def: def.to_def_id(), args, env });
                    self.roots.push(def);
                }
                DefKind::Const
                | DefKind::AssocConst
                | DefKind::AnonConst
                | DefKind::Static { nested: false, .. } => {
                    if tcx.is_foreign_item(def) || self.hooks.is_clean_origin(def) {
                        continue;
                    }
                    let args = self.identity_args(def.to_def_id());
                    let env = args.has_param().then(|| tcx.typeck_root_def_id(def.to_def_id()));
                    self.node(Key::Value { def: def.to_def_id(), args, env });
                }
                _ => {}
            }
        }
    }

    fn identity_args(&self, def: DefId) -> GenericArgs<'tcx> {
        let tcx = self.tcx;
        // A closure-like body's instance arguments are its type's (the parent's
        // plus the closure's own synthetic ones); every other body's are its
        // own generics'.
        let closure_args = if tcx.is_closure_like(def) {
            match *tcx.type_of(def).instantiate_identity().skip_norm_wip().kind() {
                ty::Closure(_, args) | ty::Coroutine(_, args) | ty::CoroutineClosure(_, args) => {
                    Some(args)
                }
                _ => None,
            }
        } else {
            None
        };
        let args = closure_args.unwrap_or_else(|| GenericArgs::identity_for_item(tcx, def));
        tcx.erase_and_anonymize_regions(args)
    }

    // ----- nodes and sites ----------------------------------------------------

    fn node(&mut self, key: Key<'tcx>) -> ReachNode {
        if let Some(&node) = self.nodes.get(&key) {
            return node;
        }
        let (definition, locality, body) = self.spec(key);
        let origin = NodeOrigin::Mir(u32::try_from(self.keys.len()).unwrap_or(u32::MAX));
        let node = self.graph.add_node(ReachNodeSpec {
            origin,
            definition,
            locality,
            body: body.reach_body(),
        });
        self.nodes.insert(key, node);
        self.node_keys.insert(node, self.keys.len());
        self.keys.push(key);
        if locality == Locality::Local {
            self.local_nodes.insert(node);
        }
        match body {
            MirNodeBody::Walked => self.pending.push_back(key),
            MirNodeBody::Opaque => {
                self.opaque.insert(node);
                self.enter_world(node, key);
            }
            MirNodeBody::Param | MirNodeBody::Seed => {}
        }
        node
    }

    /// An opaque node of foreign or MIR-less Rust code RUNs its world's node
    /// (what that code can reach that the census cannot see it call). A
    /// MIR-less Rust body whose signature can carry a callable out (its
    /// return, or what it is handed by `&mut`, raw pointer or `&` to interior
    /// mutability) may hand back one it minted out of sight, which no pool
    /// records: an UNKNOWN sink (R2 covers only what such code does itself).
    fn enter_world(&mut self, node: ReachNode, key: Key<'tcx>) {
        let tcx = self.tcx;
        let world = match key {
            Key::Opaque(def) => {
                if tcx.fn_sig(def).skip_binder().abi().is_rustic_abi() {
                    World::Rust
                } else {
                    World::Foreign
                }
            }
            Key::Body { def, .. }
                if !def.as_local().is_some_and(|local| self.hooks.is_clean_origin(local)) =>
            {
                World::Rust
            }
            _ => return,
        };
        self.world_of.insert(node, world);
        let outside = self.outside_node(world);
        let site = self.internal;
        self.graph.add_edge(node, outside, EdgeClass::Run, site, false);
        if let Key::Body { def, args, .. } = key {
            if self.mints_out_of_sight(def, args) {
                self.unknown(node, DependencyRefusalKind::UnresolvedExtern, site);
            }
        }
    }

    /// Whether MIR-less Rust code `def` can carry a callable out to its caller.
    fn mints_out_of_sight(&mut self, def: DefId, args: GenericArgs<'tcx>) -> bool {
        let tcx = self.tcx;
        let typing_env = ty::TypingEnv::fully_monomorphized();
        if !matches!(tcx.def_kind(def), DefKind::Fn | DefKind::AssocFn) || args.has_param() {
            // A closure or a shim with no MIR: no signature to read.
            return true;
        }
        let sig = tcx.fn_sig(def).instantiate(tcx, args).skip_norm_wip();
        let sig = tcx.instantiate_bound_regions_with_erased(sig);
        let mut outward = vec![sig.output()];
        for &input in sig.inputs() {
            match *input.kind() {
                ty::Ref(_, pointee, ty::Mutability::Mut) | ty::RawPtr(pointee, _) => {
                    outward.push(pointee)
                }
                ty::Ref(_, pointee, ty::Mutability::Not) if !pointee.is_freeze(tcx, typing_env) => {
                    outward.push(pointee)
                }
                _ => {}
            }
        }
        // Plain data (`Laundered`) holds a callable only after a LAUNDER, and
        // R2 assumes MIR-less code launders none (design §12).
        self.carried_all(&outward, typing_env)
            .iter()
            .any(|carried| !matches!(carried, CarriedKey::Laundered))
    }

    /// The node of `world`, created on first use with its edges.
    fn outside_node(&mut self, world: World) -> ReachNode {
        if let Some(node) = self.outside[world.index()] {
            return node;
        }
        let node = self.node(Key::Outside(world));
        self.outside[world.index()] = Some(node);
        let site = self.internal;
        match world {
            World::Foreign => {
                // Module-level assembly is foreign code that may call any
                // function it names by `sym` (design §14: crates using asm
                // are refused wholesale).
                let tcx = self.tcx;
                // A Clean island also takes `DefKind::GlobalAsm` (`DefKind` has no
                // island variant); it is not assembly.
                if tcx.hir_crate_items(()).definitions().any(|def| {
                    tcx.def_kind(def) == DefKind::GlobalAsm
                        && !tcx.trust_def_is_clean_island(def.to_def_id())
                }) {
                    self.unknown(node, DependencyRefusalKind::GlobalAssembly, site);
                }
            }
            World::Rust => {
                // MIR-less Rust can call anything foreign code can.
                let foreign = self.outside_node(World::Foreign);
                self.graph.add_edge(node, foreign, EdgeClass::Run, site, false);
                self.add_registry_members();
            }
        }
        node
    }

    /// The runtime registries MIR-less Rust reaches without being handed
    /// them: the global allocator's four entry points and the alloc error
    /// handler (by their link names, as a call of them resolves), and the
    /// panic handler.
    fn add_registry_members(&mut self) {
        let tcx = self.tcx;
        let mut members = Vec::new();
        for name in [
            "__rust_alloc",
            "__rust_dealloc",
            "__rust_realloc",
            "__rust_alloc_zeroed",
            "__rust_alloc_error_handler",
        ] {
            if let Some(def) = self.runtime_symbol(Symbol::intern(name)) {
                members.push(def);
            }
        }
        if let Some(handler) = tcx.lang_items().panic_impl().filter(|h| !tcx.is_foreign_item(*h)) {
            members.push(handler);
        }
        for def in members {
            let args = GenericArgs::identity_for_item(tcx, def);
            if let Ok(node) = self.body_node(def, args, None) {
                self.world_members[World::Rust.index()].push(node);
            }
        }
    }

    /// Every function of the crate graph outside the sysroot that is linked
    /// under a name of its own: foreign code can name it, so it is a member of
    /// the foreign world's pool and of the FnPool of its shape (foreign code
    /// may hand its address back as a function pointer). Every static foreign
    /// code names ([`static_named_by_foreign_code`]) is foreign memory: its
    /// value node is a member of the foreign world's pool (foreign code may
    /// read it and call what its walked contents hold), and what Rust may
    /// store in it later, or behind its pointers, is handed out
    /// ([`Self::foreign_memory`]), whoever stores it.
    fn add_exported_members(&mut self) {
        let tcx = self.tcx;
        let mut exported: Vec<DefId> = self.symbols().exported().collect();
        exported.sort_unstable_by_key(|def| (def.krate.as_u32(), def.index.as_u32()));
        for def in exported {
            let instance = Instance::mono(tcx, def);
            let shape = self.instance_shape(instance);
            let Ok(node) = self.member(instance, None) else { continue };
            self.pool_member(node, PoolKey::Fn(shape), false);
            self.world_members[World::Foreign.index()].push(node);
        }
        // The local crate's from HIR (a check build encodes no export list;
        // a Clean-origin static is R5, as in `add_roots`), each dependency's
        // from its `linked_candidates` (an export list also holds `#[used]`
        // statics; the predicate keeps the ones foreign code names).
        let hooks = self.hooks;
        let mut statics: Vec<DefId> = tcx
            .hir_crate_items(())
            .definitions()
            .filter(|def| {
                static_named_by_foreign_code(tcx, def.to_def_id()) && !hooks.is_clean_origin(*def)
            })
            .map(LocalDefId::to_def_id)
            .collect();
        for &krate in tcx.crates(()) {
            if in_sysroot(tcx, krate) {
                continue;
            }
            statics.extend(
                linked_candidates(tcx, krate)
                    .into_iter()
                    .filter(|&def| static_named_by_foreign_code(tcx, def)),
            );
        }
        let typing_env = ty::TypingEnv::fully_monomorphized();
        for def in statics {
            let node = self.node(Key::Value { def, args: ty::GenericArgs::empty(), env: None });
            self.world_members[World::Foreign.index()].push(node);
            let ty = tcx.type_of(def).instantiate_identity().skip_norm_wip();
            let own_bytes = tcx.static_mutability(def) == Some(rustc_hir::Mutability::Mut)
                || !ty.is_freeze(tcx, typing_env);
            self.foreign_memory(node, ty, own_bytes, typing_env);
        }
    }

    /// `node` names the address of the static `def` (a constant's provenance,
    /// a thread-local reference, a TLS shim, a `sym` operand). An `extern`
    /// static's memory is foreign code's: what Rust stores there, or behind
    /// the pointers it holds, foreign code may read and call during any later
    /// call into it, as a callback it was handed (rule H; R3). The charge sits
    /// at the address's source, so it holds however the address flows on (a
    /// helper, a cast, a struct, another static, `ptr::write`, `Cell::set`);
    /// naming the address runs nothing, so `node` gets no edge. The sysroot's
    /// own `extern` statics are exempt, as its calls into the platform's C
    /// library are (R3, R6).
    fn touch_static(&mut self, node: ReachNode, def: DefId) {
        let tcx = self.tcx;
        if !tcx.is_foreign_item(def)
            || !self.outside_sysroot(node)
            || !self.charged_statics.insert(def)
        {
            return;
        }
        let typing_env = ty::TypingEnv::fully_monomorphized();
        let ty = tcx.type_of(def).instantiate_identity().skip_norm_wip();
        let own_bytes = tcx.static_mutability(def) == Some(rustc_hir::Mutability::Mut)
            || !ty.is_freeze(tcx, typing_env);
        self.foreign_memory(node, ty, own_bytes, typing_env);
    }

    /// Memory of type `ty` that foreign code reads without being handed it
    /// (an `extern` or exported static, what a pointer foreign code returned
    /// or passed in leads to): what Rust may store there joins the foreign
    /// world's hand-out set, keyed by type as rule H keys an operand. With
    /// `own_bytes` (a `static mut`, interior mutability, a pointee) that is
    /// everything `ty` carries; otherwise only what the memory behind its
    /// pointers can hold ([`Self::writable_reach`]): writing an immutable
    /// static's own bytes is UB, from Rust or from foreign code (R4).
    fn foreign_memory(
        &mut self,
        node: ReachNode,
        ty: Ty<'tcx>,
        own_bytes: bool,
        typing_env: ty::TypingEnv<'tcx>,
    ) {
        if own_bytes {
            let keys = self.carried(ty, typing_env);
            if !keys.is_empty() {
                self.note_carried(node, &keys);
                self.handed_out.extend(keys.iter().cloned());
            }
        } else {
            let keys = self.writable_reach(ty, typing_env);
            if !keys.is_empty() {
                self.note_carried(node, &keys);
                self.handed_out.extend(keys);
            }
        }
    }

    /// What a store through the pointers a value of `ty` holds may deposit,
    /// the value's own bytes excluded. A raw pointer, a `&mut` or owning
    /// pointer, or a `&` to memory with interior mutability leads to memory
    /// that may be written, so it contributes all it carries
    /// ([`Self::carried`]); a `&` to a `Freeze` place contributes only what
    /// the pointers in that place lead to.
    fn writable_reach(&mut self, ty: Ty<'tcx>, typing_env: ty::TypingEnv<'tcx>) -> Vec<CarriedKey> {
        let tcx = self.tcx;
        let mut out: BTreeSet<CarriedKey> = BTreeSet::new();
        let mut entered = Entered::new();
        let mut stack = vec![(ty, Entered::ROOT)];
        let mut seen: FxHashSet<Ty<'tcx>> = FxHashSet::default();
        while let Some((ty, path)) = stack.pop() {
            if !seen.insert(ty) {
                continue;
            }
            if self.depth(ty) > self.limit {
                out.insert(CarriedKey::Any);
                continue;
            }
            let Ok(ty) = normalize(tcx, typing_env, ty) else {
                out.insert(CarriedKey::Any);
                continue;
            };
            match *ty.kind() {
                // Its own bytes, which are not written; nothing behind them.
                ty::Bool
                | ty::Char
                | ty::Int(_)
                | ty::Uint(_)
                | ty::Float(_)
                | ty::Str
                | ty::Never
                | ty::FnDef(..)
                | ty::FnPtr(..) => {}
                ty::Ref(_, inner, ty::Mutability::Not) if inner.is_freeze(tcx, typing_env) => {
                    stack.push((inner, path))
                }
                ty::Ref(..) | ty::RawPtr(..) => {
                    out.extend(self.carried(ty, typing_env).iter().cloned())
                }
                ty::Array(inner, _) | ty::Slice(inner) | ty::Pat(inner, _) => {
                    stack.push((inner, path))
                }
                ty::Tuple(elements) => stack.extend(elements.iter().map(|element| (element, path))),
                // A `PhantomData<T>` is the value's claim to own a `T` through
                // pointers that do not name it (`Vec<T>`'s buffer is a
                // `Unique<u8>`): owned memory, so writable.
                ty::Adt(adt, args) if adt.is_phantom_data() => {
                    out.extend(self.carried(args.type_at(0), typing_env).iter().cloned())
                }
                ty::Adt(adt, args) => {
                    let depth = self.depth(ty);
                    match entered.enter(&mut self.unbounded, path, adt.did(), depth) {
                        Some(below) => stack.extend(
                            adt.all_fields().map(|f| (f.ty(tcx, args).skip_norm_wip(), below)),
                        ),
                        // Polymorphic recursion ([`REENTRIES`]).
                        None => {
                            out.insert(CarriedKey::Any);
                        }
                    }
                }
                // Anything else (a closure's or coroutine's state, a `dyn` or
                // foreign type, an alias left unnormalized): all it carries.
                _ => out.extend(self.carried(ty, typing_env).iter().cloned()),
            }
        }
        out.into_iter().collect()
    }

    /// Whether `node` is code or a value of the crate graph outside the
    /// sysroot. Fail-closed: a node of no definition counts.
    fn outside_sysroot(&self, node: ReachNode) -> bool {
        let tcx = self.tcx;
        match self.node_keys.get(&node).map(|index| self.keys[*index]) {
            Some(Key::Body { def, .. } | Key::Value { def, .. } | Key::Promoted { def, .. }) => {
                !in_sysroot(tcx, def.krate)
            }
            Some(Key::Shim { instance, .. }) => !in_sysroot(tcx, instance.def_id().krate),
            _ => true,
        }
    }

    /// `creator` makes `member` into a callable value of `key` (CREATE and
    /// pool membership).
    fn create(
        &mut self,
        creator: ReachNode,
        member: ReachNode,
        key: PoolKey,
        confined: bool,
        site: ReachSite,
    ) {
        self.note_member(member, &key);
        self.graph.add_create(creator, member, key, confined, site);
    }

    /// Pool membership with no CREATE edge.
    fn pool_member(&mut self, member: ReachNode, key: PoolKey, confined: bool) {
        self.note_member(member, &key);
        self.graph.add_pool_member(member, key, confined);
    }

    /// Record that `member` joined the pool of `key`: when it is code of a
    /// world, a local indirect call of that key hands it its operands.
    fn note_member(&mut self, member: ReachNode, key: &PoolKey) {
        if self.world_of.contains_key(&member) && !self.world_member_keys.contains(key) {
            self.world_member_keys.push(key.clone());
        }
    }

    fn spec(&self, key: Key<'tcx>) -> (Option<DefinitionKey>, Locality, MirNodeBody) {
        let tcx = self.tcx;
        let definition = |def: DefId| {
            def.as_local().map(|local| DefinitionKey(u128::from(local.local_def_index.as_u32())))
        };
        let locality =
            |def: DefId| if def.is_local() { Locality::Local } else { Locality::External };
        match key {
            Key::Body { def, .. } => {
                let body = if def.as_local().is_some_and(|local| self.hooks.is_clean_origin(local))
                {
                    MirNodeBody::Opaque
                } else if tcx.is_constructor(def) {
                    // A struct or variant constructor only builds its value
                    // from its arguments: it runs nothing and mints nothing,
                    // with MIR here or not (a dependency's tuple variant
                    // reified to a fn pointer, P2m cost 5). `walk_body` adds
                    // no fact for it.
                    MirNodeBody::Walked
                } else if !def.is_local()
                    && !tcx.is_mir_available(def)
                    && !crate::def_is_in_real_sysroot_crate(tcx, def)
                {
                    // R2: another crate's Rust with no MIR here.
                    MirNodeBody::Opaque
                } else {
                    MirNodeBody::Walked
                };
                (definition(def), locality(def), body)
            }
            Key::Shim { instance, .. } => (None, locality(instance.def_id()), MirNodeBody::Walked),
            Key::Value { def, .. } => (definition(def), locality(def), MirNodeBody::Walked),
            Key::Promoted { def, .. } => (None, locality(def), MirNodeBody::Walked),
            Key::Drop { .. } | Key::Clone { .. } => (None, Locality::External, MirNodeBody::Walked),
            Key::Seed(_) => (None, Locality::External, MirNodeBody::Seed),
            Key::Opaque(_) | Key::Outside(_) => (None, Locality::External, MirNodeBody::Opaque),
            Key::Param => (None, Locality::External, MirNodeBody::Param),
        }
    }

    fn site(&mut self, owner: Option<LocalDefId>, span: Span) -> ReachSite {
        if owner.is_none() {
            return self.internal;
        }
        self.sites.push((owner, span));
        ReachSite::Mir((self.sites.len() - 1) as u64)
    }

    fn typing_env(&self, env: Option<DefId>) -> ty::TypingEnv<'tcx> {
        match env {
            Some(def) => ty::TypingEnv::post_analysis(self.tcx, def),
            None => ty::TypingEnv::fully_monomorphized(),
        }
    }

    /// The env a key minted in `frame` keeps: its own, while the key still
    /// mentions a type parameter.
    fn env_of<T: TypeVisitableExt<TyCtxt<'tcx>>>(
        frame_env: Option<DefId>,
        value: T,
    ) -> Option<DefId> {
        if value.has_param() { frame_env } else { None }
    }

    fn unknown(&mut self, from: ReachNode, reason: DependencyRefusalKind, site: ReachSite) {
        let tcx = self.tcx;
        if std::mem::take(&mut self.cut) {
            self.cuts.push(site);
        }
        let reason_key = format!("{reason:?}");
        if let Some(entry) = self.sinks.get_mut(&reason_key) {
            entry.0 += 1;
        } else {
            self.sink_texts.entry(reason_key.clone()).or_insert_with(|| sink_text(&reason));
            let at = rustc_middle::ty::print::with_no_trimmed_paths!({
                match self.node_keys.get(&from).map(|index| self.keys[*index]) {
                    Some(
                        Key::Body { def, .. } | Key::Value { def, .. } | Key::Promoted { def, .. },
                    ) => tcx.def_path_str(def),
                    Some(Key::Drop { ty, .. }) => format!("drop glue of `{ty}`"),
                    Some(Key::Clone { ty, .. }) => format!("clone of `{ty}`"),
                    Some(Key::Shim { instance, .. }) => format!("{instance}"),
                    Some(Key::Seed(def) | Key::Opaque(def)) => tcx.def_path_str(def),
                    Some(Key::Outside(world)) => world_name(world).to_string(),
                    Some(Key::Param) | None => String::from("?"),
                }
            });
            self.sinks.insert(reason_key, (1, at));
        }
        self.graph.add_unknown(from, reason, EdgeClass::Run, site, false);
    }

    fn param(&mut self, from: ReachNode, site: ReachSite) {
        let param = self.node(Key::Param);
        self.graph.add_edge(from, param, EdgeClass::Param, site, false);
    }

    /// The maximal nesting depth of `ty`'s type structure, memoized. An
    /// instance nested deeper than `recursion_limit` is UNKNOWN (`Widened`):
    /// polymorphic recursion makes the instance set infinite.
    /// The nesting depth of `ty`; past the limit for a type that is too
    /// LARGE as well ([`TYPE_NODES`]). A fn that recurses at `(T, T)` makes a
    /// type of 2^n leaves at depth n, and rustc's own questions about a
    /// type (`needs_drop`) are linear in its leaves with no memo: such a type
    /// is refused like one too deep, before any of them is asked.
    fn depth(&mut self, ty: Ty<'tcx>) -> usize {
        let (depth, size) = self.nesting(ty);
        if size > TYPE_NODES {
            return depth.max(self.limit + 1);
        }
        depth
    }

    fn nesting(&mut self, ty: Ty<'tcx>) -> (usize, u32) {
        if let Some(&metrics) = self.type_metrics.get(&ty) {
            return metrics;
        }
        if self.depth_budget_exhausted || self.type_metrics.len() >= TYPE_MEMO_BUDGET {
            self.depth_budget_exhausted = true;
            return (self.limit + 1, 1);
        }
        // Bounded: a child is reached only by descending, so recursion is no
        // deeper than the type, and the cut below stops the climb. The size
        // cut is the same one [`Self::depth`] applies to the finished size:
        // stop counting as soon as it passes, instead of first enumerating
        // every distinct subterm of a manufactured type tree.
        let mut deepest = 0;
        let mut size: u32 = 1;
        let mut visit = |this: &mut Self, children: &mut dyn Iterator<Item = Ty<'tcx>>| {
            for child in children {
                if deepest > this.limit || size > TYPE_NODES {
                    break;
                }
                let (child_depth, child_size) =
                    rustc_data_structures::stack::ensure_sufficient_stack(|| this.nesting(child));
                deepest = deepest.max(child_depth);
                size = size.saturating_add(child_size);
            }
        };
        match *ty.kind() {
            ty::Adt(_, args)
            | ty::Closure(_, args)
            | ty::CoroutineClosure(_, args)
            | ty::Coroutine(_, args) => visit(self, &mut args.types()),
            // Upstream 1.101: only FnDef args are Binder-wrapped.
            ty::FnDef(_, args) => visit(self, &mut args.skip_binder().types()),
            ty::Alias(_, alias) => visit(self, &mut alias.args.types()),
            ty::Ref(_, inner, _)
            | ty::RawPtr(inner, _)
            | ty::Slice(inner)
            | ty::Array(inner, _)
            | ty::Pat(inner, _) => visit(self, &mut std::iter::once(inner)),
            ty::Tuple(elements) => visit(self, &mut elements.iter()),
            ty::FnPtr(sig_tys, _) => {
                visit(self, &mut sig_tys.skip_binder().inputs_and_output.iter())
            }
            ty::Dynamic(predicates, ..) => {
                if let Some(principal) = predicates.principal() {
                    visit(self, &mut principal.skip_binder().args.types());
                }
            }
            _ => {}
        }
        let metrics = (deepest + 1, size);
        self.type_metrics.insert(ty, metrics);
        metrics
    }

    fn too_deep(&mut self, args: GenericArgs<'tcx>) -> bool {
        args.types().any(|ty| self.depth(ty) > self.limit)
    }

    /// Whether resolving a call at `args` could overflow rustc's own
    /// recursion limit: a type argument nested within [`RESOLVE_MARGIN`] of
    /// it (or past the size limit, [`Self::depth`]).
    fn near_limit(&mut self, args: GenericArgs<'tcx>) -> bool {
        // (Under a small `#![recursion_limit]` the margin is half of it: a
        // fixed one would refuse every call.)
        let margin = RESOLVE_MARGIN.min(self.limit / 2);
        args.types().any(|ty| self.depth(ty) + margin > self.limit)
    }

    // ----- pool facts ------------------------------------------------------------

    fn name_principal(&mut self, node: ReachNode, principal: PrincipalKey) {
        self.named.insert(principal);
        self.named_at.entry(principal).or_insert(node);
    }

    fn note_carried(&mut self, node: ReachNode, carried: &[CarriedKey]) {
        for key in carried {
            match key {
                CarriedKey::Principal(principal) => self.name_principal(node, *principal),
                CarriedKey::Key(key) => {
                    if let Some(principal) = key.principal() {
                        self.name_principal(node, principal);
                    }
                }
                CarriedKey::AnyFn
                | CarriedKey::AnyDyn
                | CarriedKey::Any
                | CarriedKey::Untyped
                | CarriedKey::Laundered => {}
            }
        }
    }

    fn invoke(
        &mut self,
        node: ReachNode,
        key: PoolKey,
        carried: Vec<CarriedKey>,
        site: ReachSite,
        via_drop: bool,
    ) {
        if let Some(principal) = key.principal() {
            self.name_principal(node, principal);
        }
        self.note_carried(node, &carried);
        self.deferred_invokes.push((node, key, carried, site, via_drop));
    }

    /// The principals a value of `ty` a local body receives from outside the
    /// walked world (an argument, a static, what MIR-less or foreign code
    /// returns) may carry.
    fn name_local_type(&mut self, ty: Ty<'tcx>, typing_env: ty::TypingEnv<'tcx>) {
        for key in self.carried(ty, typing_env).iter() {
            match key {
                CarriedKey::Principal(principal) => {
                    self.entering.insert(*principal);
                }
                CarriedKey::Key(key) => {
                    if let Some(principal) = key.principal() {
                        self.entering.insert(principal);
                    }
                }
                CarriedKey::AnyFn
                | CarriedKey::AnyDyn
                | CarriedKey::Any
                | CarriedKey::Untyped
                | CarriedKey::Laundered => {}
            }
        }
    }

    /// The indirect calls and hand-offs, once the walk is done. A `dyn` value
    /// exists in the census's world only if a vtable of its principal joined
    /// (walked code, the sysroot scan, constant allocations), or it entered
    /// from out of sight ([`Self::entering`]), or an upcast made it from such
    /// a value. An indirect call on a principal with no such value cannot run
    /// and is no fact (it would only open that principal and, with it, every
    /// pool: std's `Command` machinery invokes `pre_exec` closures that only a
    /// generic `pre_exec::<F>` mints, and libtest's runner bench closures that
    /// a harness built from static descriptors never holds); a carried key of
    /// such a principal is dropped from every fact, since no value carries it.
    fn emit_pool_facts(&mut self) {
        let live = self.live_principals();
        // The walk's last round resolved every held LAUNDER that names a type
        // or a principal ([`Self::name_launder_principals`]). Unless something
        // it read has grown since, resolving one again retraces that round
        // and returns its set, so the set is taken from there.
        let mut settled = match self.settled_launders.take() {
            Some((inputs, settled)) if inputs == self.launder_inputs() => settled,
            _ => FxHashMap::default(),
        };
        // Typed LAUNDERs (design §10, "typed LAUNDER"): data holds what their
        // keys admit. Value LAUNDERs are recorded as LAUNDERs of `Any` where
        // they are seen ([`Self::launder`]).
        for (entry, (site, _, what)) in std::mem::take(&mut self.deferred_launders) {
            let resolved = match settled.remove(&entry) {
                Some(resolved) => resolved,
                None => self.resolve_launder(&entry.0, entry.1, None, &live),
            };
            if resolved.is_empty() {
                continue;
            }
            if self.debug {
                let what = what.unwrap_or_default();
                let keys: Vec<String> = resolved.iter().map(key_text).collect();
                eprintln!("TRUST_SPAWN_CENSUS_DEBUG launder {keys:?} at {what}");
                for key in &resolved {
                    self.laundered_at.entry(key.clone()).or_insert_with(|| what.clone());
                }
            }
            self.graph.add_launder_keys(site, resolved.into_iter().collect());
        }
        let keep = |key: &CarriedKey| match key {
            CarriedKey::Principal(principal) => live.contains(principal),
            CarriedKey::Key(key) => {
                key.principal().is_none_or(|principal| live.contains(&principal))
            }
            CarriedKey::AnyFn
            | CarriedKey::AnyDyn
            | CarriedKey::Any
            | CarriedKey::Untyped
            | CarriedKey::Laundered => true,
        };
        for (node, key, carried, site, via_drop) in std::mem::take(&mut self.deferred_invokes) {
            if key.principal().is_some_and(|principal| !live.contains(&principal)) {
                self.dead_invokes += 1;
                continue;
            }
            let carried: Vec<CarriedKey> = carried.into_iter().filter(keep).collect();
            // A local indirect call whose pool may hold code of a world hands
            // that code its operands (rule H at an indirect call), which it
            // may keep.
            if !carried.is_empty()
                && self.local_nodes.contains(&node)
                && self.world_member_keys.iter().any(|member| keys_meet(member, &key))
            {
                self.handed_out.extend(carried.iter().cloned());
            }
            self.note_fact_owner(node, site);
            self.graph.add_invoke(node, key, carried, site, via_drop);
        }
        for (node, callee, carried, site, via_drop) in std::mem::take(&mut self.deferred_handoffs) {
            let carried: Vec<CarriedKey> = carried.into_iter().filter(keep).collect();
            self.note_fact_owner(node, site);
            self.graph.add_handoff(node, callee, carried, site, via_drop);
        }
        // A drop hands the dropped value to its glue. Only a confined member
        // makes that a fact the RUN edge to the glue does not already give, so
        // a drop is charged only with the principals that hold one (and those
        // an upcast makes of them): each has a recorded member, so naming it
        // here opens nothing.
        if self.demote_all_confined {
            for principal in &self.confined_principals {
                self.graph.add_lifetime_erase(*principal);
            }
        }
        let drops = std::mem::take(&mut self.deferred_drop_handoffs);
        if !self.confined_principals.is_empty() {
            let mut confining = self.confined_principals.clone();
            loop {
                let before = confining.len();
                for (from, to) in &self.upcasts {
                    if confining.contains(from) {
                        confining.insert(*to);
                    }
                }
                if confining.len() == before {
                    break;
                }
            }
            for (node, glue, carried, site) in drops {
                let carried: Vec<CarriedKey> = carried
                    .into_iter()
                    .filter(|key| match key {
                        CarriedKey::Principal(principal) => confining.contains(principal),
                        CarriedKey::Key(key) => {
                            key.principal().is_some_and(|principal| confining.contains(&principal))
                        }
                        // An opaque value may hold a confined erasure; an
                        // untyped pointer reaches one only after a demoting
                        // cast (`CarriedKey::Untyped`).
                        CarriedKey::AnyDyn | CarriedKey::Any => true,
                        CarriedKey::AnyFn | CarriedKey::Untyped | CarriedKey::Laundered => false,
                    })
                    .collect();
                if carried.is_empty() {
                    continue;
                }
                self.note_carried(node, &carried);
                self.note_fact_owner(node, site);
                self.graph.add_handoff(node, glue, carried, site, true);
            }
        }
        // The worlds (design §5.4, rule H; §12, R2 and R3). Each world's node
        // calls its members (an invoke of its own pool, so the edges are
        // APPROX: such code MAY call them), and the foreign world's node is
        // handed everything any frame outside the sysroot handed such code.
        let site = self.internal;
        for world in [World::Foreign, World::Rust] {
            let Some(node) = self.outside[world.index()] else { continue };
            let members = std::mem::take(&mut self.world_members[world.index()]);
            if members.is_empty() {
                continue;
            }
            let key =
                PoolKey::DynMethod { principal: world_principal(world), method: MethodKey(0) };
            for member in members {
                self.graph.add_pool_member(member, key.clone(), false);
            }
            self.note_fact_owner(node, site);
            self.graph.add_invoke(node, key, Vec::new(), site, false);
        }
        if let Some(node) = self.outside[World::Foreign.index()] {
            let carried: Vec<CarriedKey> =
                std::mem::take(&mut self.handed_out).into_iter().filter(keep).collect();
            if !carried.is_empty() {
                self.note_fact_owner(node, site);
                self.graph.add_handoff(node, node, carried, site, false);
            }
        }
    }

    /// Record `node` as the node of a fact at `site` when a local body owns
    /// `site`: the engine derives edges at a fact's site, so these are the
    /// only nodes the rows read derived edges from.
    fn note_fact_owner(&mut self, node: ReachNode, site: ReachSite) {
        let ReachSite::Mir(index) = site else { return };
        if matches!(self.sites.get(index as usize), Some((Some(_), _))) {
            self.fact_owners.insert(node);
        }
    }

    /// The principals a `dyn` value of which can exist: every one a vtable
    /// joined or a value entering from out of sight carries, closed under the
    /// upcasts added.
    fn live_principals(&self) -> BTreeSet<PrincipalKey> {
        let mut live: BTreeSet<PrincipalKey> = self.minted.union(&self.entering).copied().collect();
        loop {
            let before = live.len();
            for (from, to) in &self.upcasts {
                if live.contains(from) {
                    live.insert(*to);
                }
            }
            if live.len() == before {
                return live;
            }
        }
    }

    fn handoff_fact(
        &mut self,
        node: ReachNode,
        callee: ReachNode,
        carried: Vec<CarriedKey>,
        site: ReachSite,
        via_drop: bool,
    ) {
        self.note_carried(node, &carried);
        self.deferred_handoffs.push((node, callee, carried, site, via_drop));
    }

    /// Membership is every CREATE in walked code: local code, STD, and
    /// constant allocations (design §5.4). Every principal the walk names is
    /// looked up in what the sysroot's monomorphic bodies mint (their stored
    /// `mentioned_items`, so an unsize optimized away still counts), whether
    /// or not a walked body reaches the minting code: each concrete type found
    /// joins the pools (its vtable methods and drop slot, walked like any
    /// member), with no CREATE edge, once the values it needs can exist
    /// ([`Self::settle_pending`]). A principal the walk names that neither
    /// walked code nor the sysroot mints stays open, and the engine leaves
    /// every pool unclosed (UNKNOWN), as trust-ir P1 rules.
    fn add_sysroot_members(&mut self) -> bool {
        let open: Vec<PrincipalKey> = self.named.difference(&self.searched).copied().collect();
        if !open.is_empty() && self.sysroot_creates.is_none() {
            self.sysroot_creates = Some(self.scan_sysroot());
        }
        for principal in open {
            self.searched.insert(principal);
            let Some(index) = &self.sysroot_creates else { break };
            let creates = index.creates.get(&principal).cloned().unwrap_or_default();
            let upcasts: Vec<(PrincipalKey, PrincipalKey)> =
                index.upcasts.iter().filter(|(_, to)| *to == principal).copied().collect();
            self.pending_upcasts.extend(upcasts);
            self.pending_creates.extend(creates);
        }
        self.settle_pending()
    }

    /// A scanned vtable or upcast joins the pools only once the values it
    /// needs can exist. The sysroot code that erases a `&dyn Error` to `dyn
    /// Debug` runs only on a `dyn Error` value, and such a value exists only if
    /// its principal is live ([`Self::live_principals`]). So a vtable whose
    /// concrete type carries a principal that is not live, and an upcast from
    /// such a principal, wait; whatever still waits when nothing more joins is
    /// never added. Returns whether anything joined.
    fn settle_pending(&mut self) -> bool {
        let typing_env = ty::TypingEnv::fully_monomorphized();
        let mut added = false;
        loop {
            let minted = self.live_principals();
            let mut progress = false;
            for (from, to) in std::mem::take(&mut self.pending_upcasts) {
                if minted.contains(&from) {
                    self.add_upcast(from, to);
                    progress = true;
                } else {
                    self.pending_upcasts.push((from, to));
                }
            }
            for (concrete, predicates) in std::mem::take(&mut self.pending_creates) {
                let carried = self.carried(concrete, typing_env);
                let exists = carried.iter().all(|key| match key {
                    CarriedKey::Principal(principal) => minted.contains(principal),
                    CarriedKey::Key(key) => {
                        key.principal().is_none_or(|principal| minted.contains(&principal))
                    }
                    CarriedKey::AnyFn
                    | CarriedKey::AnyDyn
                    | CarriedKey::Any
                    | CarriedKey::Untyped
                    | CarriedKey::Laundered => true,
                });
                if exists {
                    self.vtable_members(concrete, predicates);
                    progress = true;
                } else {
                    self.pending_creates.push((concrete, predicates));
                }
            }
            if !progress {
                return added;
            }
            added = true;
        }
    }

    fn add_upcast(&mut self, from: PrincipalKey, to: PrincipalKey) {
        self.upcasts.insert((from, to));
        self.graph.add_upcast(from, to);
    }

    /// Every monomorphic body of the real sysroot with MIR, scanned once for
    /// the `dyn` values it mints.
    fn scan_sysroot(&mut self) -> SysrootCreates<'tcx> {
        let tcx = self.tcx;
        let typing_env = ty::TypingEnv::fully_monomorphized();
        let mut index =
            SysrootCreates { creates: BTreeMap::new(), upcasts: BTreeSet::new(), bodies: 0 };
        for &krate in tcx.crates(()) {
            // Every crate this compiler's sysroot supplies (libtest's runner
            // and its dependencies too): more members never hide a spawn.
            if !in_sysroot(tcx, krate) {
                continue;
            }
            if tcx.crate_dep_kind(krate).macros_only() {
                // Linked into nothing this crate runs.
                continue;
            }
            for position in 0..tcx.num_extern_def_ids(krate) {
                let def =
                    DefId { krate, index: rustc_span::def_id::DefIndex::from_usize(position) };
                // `is_mir_available` first: it answers for every index, while
                // a proc-macro crate (rustc-dev's `librustc_macros` sits in the
                // sysroot's directory) encodes a `def_kind` for its root and
                // macros only, and has no MIR.
                if !tcx.is_mir_available(def)
                    || !matches!(
                        tcx.def_kind(def),
                        DefKind::Fn | DefKind::AssocFn | DefKind::Closure
                    )
                    || tcx.generics_of(def).requires_monomorphization(tcx)
                {
                    continue;
                }
                // The body's `mentioned_items` alone, read from the producer's
                // `trust_mentioned_items` table: the field itself, unfiltered, so
                // every filter here is this reader's. Decoding each body whole for
                // this one field cost about 0.4 s and 250 MB per crate (PKG-C5d).
                let Some(mentioned) = tcx.trust_mentioned_items(def) else { continue };
                index.bodies += 1;
                for item in mentioned {
                    let MentionedItem::UnsizeCast { source_ty, target_ty } = *item else {
                        continue;
                    };
                    if source_ty.has_param() || target_ty.has_param() || source_ty.has_aliases() {
                        continue;
                    }
                    let source = tcx.erase_and_anonymize_regions(source_ty);
                    let target = tcx.erase_and_anonymize_regions(target_ty);
                    for (concrete, predicates, _) in self.unsize_pairs(typing_env, source, target) {
                        let to = self.principal_key(predicates);
                        if let ty::Dynamic(from, ..) = *concrete.kind() {
                            let from = self.principal_key(from);
                            if from != to {
                                index.upcasts.insert((from, to));
                            }
                        } else if !concrete.has_param() && !concrete.has_aliases() {
                            let entry = index.creates.entry(to).or_default();
                            if !entry.iter().any(|(ty, _)| *ty == concrete) {
                                entry.push((concrete, predicates));
                            }
                        }
                    }
                }
            }
        }
        index
    }

    // ----- keys of callables ---------------------------------------------------

    /// The node of a body run as a function, or UNKNOWN (`Widened`) past the
    /// recursion limit.
    fn body_node(
        &mut self,
        def: DefId,
        args: GenericArgs<'tcx>,
        env: Option<DefId>,
    ) -> Result<ReachNode, DependencyRefusalKind> {
        let args = self.tcx.erase_and_anonymize_regions(args);
        self.cut = false;
        if self.too_deep(args) {
            self.cut = true;
            return Err(DependencyRefusalKind::Widened);
        }
        if args.has_param() && env.is_none() {
            return Err(DependencyRefusalKind::ResolutionError);
        }
        let key = Key::Body { def, args, env: Self::env_of(env, args) };
        if !args.is_empty() && !self.nodes.contains_key(&key) {
            let made = self.instances_of.entry(def).or_default();
            if *made >= BODY_INSTANCES {
                self.cut = true;
                return Err(DependencyRefusalKind::Widened);
            }
            *made += 1;
        }
        Ok(self.node(key))
    }

    /// The node a callable VALUE stands for: what calling `instance` runs.
    fn member(
        &mut self,
        instance: Instance<'tcx>,
        env: Option<DefId>,
    ) -> Result<ReachNode, DependencyRefusalKind> {
        let tcx = self.tcx;
        match instance.def {
            InstanceKind::Item(def) if is_std_thread_spawn(tcx, def) => {
                Ok(self.node(Key::Seed(def)))
            }
            InstanceKind::Item(def) if tcx.is_foreign_item(def) => Ok(self.foreign_target(def)),
            InstanceKind::Item(def) => self.body_node(def, instance.args, env),
            InstanceKind::Intrinsic(_)
            | InstanceKind::LlvmIntrinsic(_)
            | InstanceKind::Virtual(..)
            | InstanceKind::Shim(_) => {
                let instance = tcx.erase_and_anonymize_regions(instance);
                self.cut = false;
                if self.too_deep(instance.args) {
                    self.cut = true;
                    return Err(DependencyRefusalKind::Widened);
                }
                Ok(self.node(Key::Shim { instance, env: Self::env_of(env, instance) }))
            }
        }
    }

    // ----- the walk ------------------------------------------------------------

    fn run(&mut self) {
        loop {
            self.drain();
            // The principals a typed LAUNDER's objects resolve through: the
            // sysroot scan looks them up like any other named principal.
            self.name_launder_principals();
            if !self.add_sysroot_members() {
                break;
            }
        }
    }

    fn drain(&mut self) {
        while let Some(key) = self.pending.pop_front() {
            let node = self.nodes[&key];
            match key {
                Key::Body { def, args, env } => self.walk_body(node, def, args, env),
                Key::Shim { instance, env } => {
                    let frame = self.bare_frame(node, env, Locality::External);
                    let site = self.internal;
                    self.run_instance(&frame, instance, &[], site, false);
                }
                Key::Value { def, args, env } => self.walk_value(node, def, args, env),
                Key::Promoted { def, args, promoted, env } => {
                    let frame = Frame {
                        node,
                        owner: None,
                        instance: Some(Instance { def: InstanceKind::Item(def), args }),
                        env,
                        typing_env: self.typing_env(env),
                        mode: Mode::Const,
                        locality: Locality::External,
                    };
                    let bodies = self.tcx.promoted_mir(def);
                    match bodies.get(promoted) {
                        Some(body) => self.visit(&frame, body),
                        None => {
                            let site = self.internal;
                            self.unknown(node, DependencyRefusalKind::ResolutionError, site)
                        }
                    }
                }
                Key::Drop { ty, env } => self.walk_drop(node, ty, env),
                Key::Clone { ty, env } => self.walk_clone(node, ty, env),
                Key::Seed(_) | Key::Opaque(_) | Key::Outside(_) | Key::Param => {}
            }
        }
    }

    fn bare_frame(&self, node: ReachNode, env: Option<DefId>, locality: Locality) -> Frame<'tcx> {
        Frame {
            node,
            owner: None,
            instance: None,
            env,
            typing_env: self.typing_env(env),
            mode: Mode::Run,
            locality,
        }
    }

    fn walk_body(
        &mut self,
        node: ReachNode,
        def: DefId,
        args: GenericArgs<'tcx>,
        env: Option<DefId>,
    ) {
        let tcx = self.tcx;
        if tcx.is_constructor(def) {
            // A constructor only builds its value.
            return;
        }
        let frame = Frame {
            node,
            owner: def.as_local(),
            instance: Some(Instance { def: InstanceKind::Item(def), args }),
            env,
            typing_env: self.typing_env(env),
            mode: Mode::Run,
            locality: if def.is_local() { Locality::Local } else { Locality::External },
        };
        if let Some(local) = def.as_local() {
            if matches!(
                tcx.hir_body_const_context(local),
                Some(rustc_hir::ConstContext::Const { .. } | rustc_hir::ConstContext::Static(_))
            ) {
                // A `#[rustc_comptime]` fn: its elaborated MIR is CTFE's.
                self.visit(&frame, tcx.mir_for_ctfe(def));
                return;
            }
            if self.hooks.may_carry_monitor(local) {
                self.monitor_call(&frame);
            }
            self.foreign_entry(&frame, def, args);
            let hooks = self.hooks;
            hooks.with_local_body(local, &mut |body| self.visit(&frame, body));
            return;
        }
        if tcx.is_mir_available(def) {
            self.foreign_entry(&frame, def, args);
            let body = tcx.optimized_mir(def);
            self.visit(&frame, body);
        } else {
            // A MIR-less sysroot item (R2 never applies to the sysroot).
            let site = self.internal;
            self.unknown(node, DependencyRefusalKind::UnresolvedExtern, site);
        }
    }

    /// A body with a foreign calling convention may be called by foreign code
    /// (it is exported, or handed over as a callback; a call through a
    /// Rust-ABI pointer from foreign code is R4). What foreign code passes it
    /// may point to memory foreign code reads later, so a store through it is
    /// handed out ([`Self::foreign_memory`]), and what it returns is handed
    /// to foreign code, as rule H hands a call's operands. The sysroot's own
    /// are exempt (R3, R6).
    fn foreign_entry(&mut self, frame: &Frame<'tcx>, def: DefId, args: GenericArgs<'tcx>) {
        let tcx = self.tcx;
        if !matches!(tcx.def_kind(def), DefKind::Fn | DefKind::AssocFn)
            || in_sysroot(tcx, def.krate)
            || tcx.fn_sig(def).skip_binder().abi().is_rustic_abi()
        {
            return;
        }
        let sig = tcx.fn_sig(def).instantiate(tcx, args).skip_norm_wip();
        let sig = tcx.instantiate_bound_regions_with_erased(sig);
        for &input in sig.inputs() {
            self.foreign_memory(frame.node, input, false, frame.typing_env);
        }
        let returned = self.carried(sig.output(), frame.typing_env);
        if !returned.is_empty() {
            self.note_carried(frame.node, &returned);
            self.handed_out.extend(returned.iter().cloned());
        }
    }

    /// TrustVerify installs a kernel-certified runtime monitor in a contract
    /// owner of a monitored test session after the census read the body: a
    /// call of `core::contracts::certified_monitor_check`, which panics when
    /// the clause fails. The census charges it to the body, and records it as
    /// covered there (self-audit check 2).
    fn monitor_call(&mut self, frame: &Frame<'tcx>) {
        let tcx = self.tcx;
        let Some(owner) = frame.owner else { return };
        let Some(helper) = tcx.get_diagnostic_item(sym::trust_certified_monitor_check) else {
            return;
        };
        let site = self.site(frame.owner, tcx.def_span(owner));
        let args = GenericArgs::identity_for_item(tcx, helper);
        self.cover(
            frame.owner,
            MentionedItem::Fn(Ty::new_fn_def(tcx, helper, ty::Binder::dummy(args))),
        );
        match self.body_node(helper, args, None) {
            Ok(callee) => self.graph.add_edge(frame.node, callee, EdgeClass::Run, site, false),
            Err(reason) => self.unknown(frame.node, reason, site),
        }
    }

    fn walk_value(
        &mut self,
        node: ReachNode,
        def: DefId,
        args: GenericArgs<'tcx>,
        env: Option<DefId>,
    ) {
        let tcx = self.tcx;
        let site = self.internal;
        if tcx.is_foreign_item(def) {
            // R3: a foreign static holds no callable a Rust CREATE did not
            // make; what Rust stores there is handed to foreign code where a
            // walked node names it ([`Self::touch_static`]).
            return;
        }
        if matches!(tcx.def_kind(def), DefKind::Static { nested: false, .. }) {
            // What code out of sight stores in a mutable static reaches every
            // reader; an immutable one holds its walked initializer. A nested
            // static (memory const evaluation interned out of a static's
            // initializer) has no type: it is reached, and written, only
            // through its parent static, whose type is named here.
            let typing_env = ty::TypingEnv::fully_monomorphized();
            let ty = tcx.type_of(def).instantiate_identity().skip_norm_wip();
            if tcx.static_mutability(def) == Some(rustc_hir::Mutability::Mut)
                || !ty.is_freeze(tcx, typing_env)
            {
                self.name_local_type(ty, typing_env);
            }
        }
        match tcx.def_kind(def) {
            DefKind::Static { nested, .. } => match tcx.eval_static_initializer(def) {
                // Already evaluated by `check_crate` (a cache hit), or from metadata.
                Ok(allocation) => {
                    // Route C reads the static's bytes at its type; a nested
                    // static's are read through the pointer its parent holds.
                    let typing = if nested {
                        Typing::Unchecked
                    } else {
                        let ty = tcx.type_of(def).instantiate_identity().skip_norm_wip();
                        Typing::At(tcx.erase_and_anonymize_regions(ty), 0)
                    };
                    let mut roots = Vec::new();
                    self.allocation_provenance(allocation.inner(), &typing, &mut roots);
                    self.allocations(node, roots, site);
                }
                Err(_) => self.unknown(node, DependencyRefusalKind::ResolutionError, site),
            },
            DefKind::Const { .. } | DefKind::AssocConst { .. } | DefKind::AnonConst => {
                // A trivial const's value is already known, and it has no
                // `mir_for_ctfe` (asking is a debug assertion).
                if let Some((value, ty)) = tcx.trivial_const(def) {
                    self.const_value(node, value, ty, site);
                    return;
                }
                {
                    // Every constant's CTFE MIR is encoded in metadata.
                    let frame = Frame {
                        node,
                        owner: None,
                        instance: Some(Instance { def: InstanceKind::Item(def), args }),
                        env,
                        typing_env: self.typing_env(env),
                        mode: Mode::Const,
                        locality: if def.is_local() { Locality::Local } else { Locality::External },
                    };
                    self.visit(&frame, tcx.mir_for_ctfe(def));
                }
            }
            _ => self.unknown(node, DependencyRefusalKind::ResolutionError, site),
        }
    }

    // ----- one body ---------------------------------------------------------------

    fn mono<T: rustc_middle::ty::TypeFoldable<TyCtxt<'tcx>>>(
        &self,
        frame: &Frame<'tcx>,
        value: T,
    ) -> Option<T> {
        let instance = frame.instance?;
        instance
            .try_instantiate_mir_and_normalize_erasing_regions(
                self.tcx,
                frame.typing_env,
                ty::EarlyBinder::bind(self.tcx, value),
            )
            .ok()
    }

    /// A type the visited body's MIR spells, as the frame's instance has it,
    /// for a question the census asks of it ([`Self::mono`]). The MIR spells
    /// the body's own generics, which the frame's environment need not hold:
    /// a body walked at a concrete instance has the empty one. Walked at
    /// `f::<2>`, a drop of `[SmtValue; N]` in `fn f<const N: usize>` is a
    /// drop of `[SmtValue; 2]`; `needs_drop` asked of `[SmtValue; N]` in the
    /// empty environment was a compiler panic (no `N` there; 0.11.0's
    /// consumer check, ay-chc's `dt`). A type that does not instantiate is
    /// judged at its worst ([`Self::untypeable`]), never skipped.
    fn instance_ty(&mut self, frame: &Frame<'tcx>, ty: Ty<'tcx>, span: Span) -> Option<Ty<'tcx>> {
        let instantiated = self.mono(frame, ty);
        if instantiated.is_none() {
            let site = self.site(frame.owner, span);
            self.untypeable(frame, site);
        }
        instantiated
    }

    /// A type of the visited body that does not instantiate at the frame's
    /// instance: nothing the census asks of it can be answered, so the body
    /// reaches code it could not enumerate (an UNKNOWN sink), and memory it
    /// names, views or reinterprets at that type may hold any callable (a
    /// LAUNDER of `Any`, as running inline assembly's is, which demotes every
    /// confined member).
    fn untypeable(&mut self, frame: &Frame<'tcx>, site: ReachSite) {
        self.unknown(frame.node, DependencyRefusalKind::ResolutionError, site);
        self.note_launder(frame, || "a type that does not instantiate".to_owned());
        if self.debug && !self.laundered_at.contains_key(&CarriedKey::Any) {
            let at = self.describe_node(frame.node);
            self.laundered_at
                .insert(CarriedKey::Any, format!("{at} (a type that does not instantiate)"));
        }
        self.graph.add_launder(site);
    }

    fn visit(&mut self, frame: &Frame<'tcx>, body: &mir::Body<'tcx>) {
        if frame.locality == Locality::Local {
            // A value minted outside the walked world enters a local body
            // through its arguments (closures: their captures too).
            for arg in body.args_iter() {
                let decl = &body.local_decls[arg];
                if let Some(ty) = self.instance_ty(frame, decl.ty, decl.source_info.span) {
                    self.name_local_type(ty, frame.typing_env);
                }
            }
        }
        // Every union a place of this body can reach is a local's or a saved
        // coroutine local's, in its own bytes or behind a pointer it holds.
        let saved = body
            .coroutine_layout_raw()
            .map(|layout| layout.field_tys.iter().map(|saved| (saved.ty, saved.source_info.span)));
        let types: Vec<(Ty<'tcx>, Span)> = body
            .local_decls
            .iter()
            .map(|decl| (decl.ty, decl.source_info.span))
            .chain(saved.into_iter().flatten())
            .collect();
        for (ty, span) in types {
            if let Some(ty) = self.instance_ty(frame, ty, span) {
                self.erase_union_lifetimes(ty, frame.typing_env);
            }
        }
        // Route U (design §10, "typed LAUNDER"): a union whose field a place of
        // this body projects, or which an aggregate builds, has its bytes read
        // through another field than the one that wrote them.
        for (union_ty, location) in union_projections(self.tcx, body) {
            let span = body.source_info(location).span;
            if let Some(union_ty) = self.instance_ty(frame, union_ty, span) {
                self.union_pun(frame, body.source.def_id(), union_ty, span);
            }
        }
        let hooks = self.hooks;
        let mut mentions: Vec<(MentionedItem<'tcx>, Span, Location)> = Vec::new();
        hooks.for_each_mentioned_item(body, &mut |item, span, location| {
            mentions.push((item, span, location))
        });
        let assignments = SingleAssignments::of(body);
        for &(item, span, location) in &mentions {
            self.mention(frame, body, &assignments, item, span, location);
        }
        for &(item, _, _) in &mentions {
            self.cover(frame.owner, item);
        }
        for (block, data) in body.basic_blocks.iter_enumerated() {
            for (statement_index, statement) in data.statements.iter().enumerate() {
                let location = Location { block, statement_index };
                self.statement(frame, body, statement, location);
            }
            let location = Location { block, statement_index: data.statements.len() };
            self.terminator(frame, body, data.terminator(), location);
        }
        // Self-audit check 2 (design §5.6), for a body read from metadata: its
        // `mentioned_items` were recorded before that crate optimized it, so
        // what optimization removed is covered here, as an edge that claims
        // nothing (a local body's codegen list is audited by TrustVerify).
        if let (false, Some(stored)) = (body.source.def_id().is_local(), &body.mentioned_items) {
            let seen: FxHashSet<MentionedItem<'tcx>> =
                mentions.iter().map(|&(item, _, _)| item).collect();
            for spanned in stored {
                if !seen.contains(&spanned.node) {
                    self.uncovered(frame, spanned.node);
                }
            }
        }
    }

    /// A stored mention the walk of an optimized body did not find: it was
    /// optimized away. Covered without a spawn claim (CREATE caps at ESCAPES):
    /// its callee joins the coarsest fn pool, its drop glue is an edge.
    fn uncovered(&mut self, frame: &Frame<'tcx>, item: MentionedItem<'tcx>) {
        let site = self.internal;
        let node = frame.node;
        match item {
            MentionedItem::Fn(callee) => {
                let Some(callee) = self.mono(frame, callee) else {
                    return self.unknown(node, DependencyRefusalKind::ResolutionError, site);
                };
                match *callee.kind() {
                    ty::FnDef(def, args)
                        if drop_glue_call(self.tcx, def, args.skip_binder()).is_some() =>
                    {
                        let dropped =
                            drop_glue_call(self.tcx, def, args.skip_binder()).filter(|dropped| {
                                census_needs_drop(self.tcx, frame.typing_env, *dropped)
                            });
                        if let Some(dropped) = dropped {
                            match self.drop_node(dropped, frame.env) {
                                Ok(glue) => {
                                    self.graph.add_edge(node, glue, EdgeClass::Create, site, true)
                                }
                                Err(reason) => self.unknown(node, reason, site),
                            }
                        }
                    }
                    ty::FnDef(def, args) if !self.tcx.intrinsic(def).is_some() => {
                        match ty::Instance::try_resolve(
                            self.tcx,
                            frame.typing_env,
                            def,
                            args.skip_binder(),
                        ) {
                            Ok(Some(instance)) => match self.member(instance, frame.env) {
                                Ok(member) => self.create(
                                    node,
                                    member,
                                    PoolKey::Fn(FnShape::unclassified()),
                                    false,
                                    site,
                                ),
                                Err(reason) => self.unknown(node, reason, site),
                            },
                            Ok(None) if args.has_param() => self.param(node, site),
                            Ok(None) | Err(_) => {
                                self.unknown(node, DependencyRefusalKind::ResolutionError, site)
                            }
                        }
                    }
                    ty::FnDef(..) => {}
                    ty::FnPtr(..) => {
                        let shape = self.fn_shape(callee.fn_sig(self.tcx));
                        self.invoke(node, PoolKey::Fn(shape), Vec::new(), site, false);
                    }
                    _ => self.unknown(node, DependencyRefusalKind::ResolutionError, site),
                }
            }
            MentionedItem::Drop(ty) => {
                let Some(ty) = self.mono(frame, ty) else {
                    return self.unknown(node, DependencyRefusalKind::ResolutionError, site);
                };
                if census_needs_drop(self.tcx, frame.typing_env, ty) {
                    match self.drop_node(ty, frame.env) {
                        Ok(glue) => self.graph.add_edge(node, glue, EdgeClass::Create, site, true),
                        Err(reason) => self.unknown(node, reason, site),
                    }
                }
            }
            MentionedItem::UnsizeCast { source_ty, target_ty } => {
                self.unsize(frame, source_ty, target_ty, site, false)
            }
            MentionedItem::Closure(closure) => self.closure_pointer(frame, closure, None, site),
        }
    }

    fn mention(
        &mut self,
        frame: &Frame<'tcx>,
        body: &mir::Body<'tcx>,
        assignments: &SingleAssignments,
        item: MentionedItem<'tcx>,
        span: Span,
        location: Location,
    ) {
        let site = self.site(frame.owner, span);
        match item {
            MentionedItem::Fn(callee) => {
                let call_args =
                    body.stmt_at(location).right().and_then(|terminator| match &terminator.kind {
                        TerminatorKind::Call { args, .. }
                        | TerminatorKind::TailCall { args, .. } => Some(args),
                        _ => None,
                    });
                if let Some(args) = call_args {
                    let tcx = self.tcx;
                    let arg_tys: Vec<Ty<'tcx>> =
                        args.iter().map(|arg| arg.node.ty(body, tcx)).collect();
                    self.record_const_eval_select(frame, callee);
                    if self.catch_unwind_call(
                        frame,
                        body,
                        assignments,
                        callee,
                        args,
                        &arg_tys,
                        site,
                    ) {
                        return;
                    }
                    self.call(frame, callee, &arg_tys, site);
                    return;
                }
                // A reified fn item, or a `sym` operand of inline assembly.
                let target =
                    body.stmt_at(location).left().and_then(|statement| match &statement.kind {
                        mir::StatementKind::Assign((_, mir::Rvalue::Cast(_, _, target))) => {
                            Some(*target)
                        }
                        _ => None,
                    });
                // A temporary reified only to be `catch_unwind`'s `try_fn` or
                // `catch_fn` (std's `do_call`, `do_catch`): the intrinsic only
                // calls it, which [`Self::catch_unwind_call`] charges as a RUN
                // of the item, and no other code ever holds its address, so it
                // is no FnPool member (DECISION_QUEUE SC-7h).
                if reified_for_catch_unwind_only(self.tcx, body, assignments, location) {
                    return;
                }
                self.reify(frame, callee, target, site);
            }
            MentionedItem::Drop(ty) => {
                let async_drop = body.stmt_at(location).right().is_some_and(|terminator| {
                    matches!(terminator.kind, TerminatorKind::Drop { drop: Some(_), .. })
                });
                self.drop(frame, ty, async_drop, site);
            }
            MentionedItem::UnsizeCast { source_ty, target_ty } => {
                let confined =
                    frame.mode == Mode::Run && erases_local_reference(body, assignments, location);
                self.unsize(frame, source_ty, target_ty, site, confined)
            }
            MentionedItem::Closure(closure) => {
                let target =
                    body.stmt_at(location).left().and_then(|statement| match &statement.kind {
                        mir::StatementKind::Assign((_, mir::Rvalue::Cast(_, _, target))) => {
                            Some(*target)
                        }
                        _ => None,
                    });
                self.closure_pointer(frame, closure, target, site)
            }
        }
    }

    /// `catch_unwind(try_fn, data, catch_fn)` calls `try_fn` and, on unwind,
    /// `catch_fn`. std hands it temporaries reified from one fn item each
    /// (`do_call::<F, R>`, `do_catch::<F, R>`), so each such operand is a RUN
    /// of that item (S2), not an invoke of the FnPool of `fn(*mut u8)`, which
    /// holds the `do_call` of every closure the crate runs under
    /// `catch_unwind` (`std::thread::scope`, `panic::catch_unwind`, every
    /// spawned thread's main). An operand [`reified_operand`] cannot pin is
    /// invoked through its pool. Returns whether the call was this intrinsic.
    fn catch_unwind_call(
        &mut self,
        frame: &Frame<'tcx>,
        body: &mir::Body<'tcx>,
        assignments: &SingleAssignments,
        callee: Ty<'tcx>,
        args: &[rustc_span::Spanned<mir::Operand<'tcx>>],
        arg_tys: &[Ty<'tcx>],
        site: ReachSite,
    ) -> bool {
        let tcx = self.tcx;
        let ty::FnDef(def, _) = *callee.kind() else { return false };
        if !tcx.intrinsic(def).is_some_and(|intrinsic| intrinsic.name == sym::catch_unwind) {
            return false;
        }
        if frame.mode == Mode::Const {
            self.unknown(frame.node, DependencyRefusalKind::ResolutionError, site);
            return true;
        }
        // `try_fn` is called with `data`, `catch_fn` with `data` and the panic
        // payload (`*mut u8`); both carry what `data` carries (the payload is
        // std's own `Box<dyn Any + Send>`, which the panic machinery drops or
        // hands back, walked in std).
        let data: Vec<Ty<'tcx>> = arg_tys.get(1).copied().into_iter().collect();
        for (arg, &ty) in args.iter().zip(arg_tys) {
            if !matches!(ty.kind(), ty::FnPtr(..)) {
                continue;
            }
            match reified_operand(body, assignments, &arg.node) {
                Some(item) => self.call(frame, item, &data, site),
                None => self.call(frame, ty, &data, site),
            }
        }
        true
    }

    /// `remap_mir_for_const_eval_select` turns a `const_eval_select` call into
    /// a call of its runtime function before `MentionedItems` runs on the
    /// codegen body, so that function's type is covered too (check 2).
    fn record_const_eval_select(&mut self, frame: &Frame<'tcx>, callee: Ty<'tcx>) {
        let ty::FnDef(def, args) = *callee.kind() else { return };
        if !self
            .tcx
            .intrinsic(def)
            .is_some_and(|intrinsic| intrinsic.name == sym::const_eval_select)
        {
            return;
        }
        if let Some(runtime) = args.skip_binder().types().nth(2) {
            self.cover(frame.owner, MentionedItem::Fn(runtime));
        }
    }

    fn statement(
        &mut self,
        frame: &Frame<'tcx>,
        body: &mir::Body<'tcx>,
        statement: &mir::Statement<'tcx>,
        location: Location,
    ) {
        match &statement.kind {
            mir::StatementKind::Assign((_, rvalue)) => self.rvalue(frame, body, rvalue, location),
            mir::StatementKind::Intrinsic(intrinsic) => match intrinsic {
                mir::NonDivergingIntrinsic::Assume(operand) => {
                    self.operand(frame, body, operand, location)
                }
                mir::NonDivergingIntrinsic::CopyNonOverlapping(copy) => {
                    self.operand(frame, body, &copy.src, location);
                    self.operand(frame, body, &copy.dst, location);
                    self.operand(frame, body, &copy.count, location);
                }
            },
            mir::StatementKind::FakeRead(..)
            | mir::StatementKind::SetDiscriminant { .. }
            | mir::StatementKind::StorageLive(_)
            | mir::StatementKind::StorageDead(_)
            | mir::StatementKind::PlaceMention(_)
            | mir::StatementKind::AscribeUserType(..)
            | mir::StatementKind::Coverage(_)
            | mir::StatementKind::ConstEvalCounter
            | mir::StatementKind::Nop
            | mir::StatementKind::BackwardIncompatibleDropHint { .. } => {}
        }
    }

    fn rvalue(
        &mut self,
        frame: &Frame<'tcx>,
        body: &mir::Body<'tcx>,
        rvalue: &mir::Rvalue<'tcx>,
        location: Location,
    ) {
        match rvalue {
            mir::Rvalue::Use(operand, _)
            | mir::Rvalue::Repeat(operand, _)
            | mir::Rvalue::UnaryOp(_, operand)
            | mir::Rvalue::WrapUnsafeBinder(operand, _) => {
                self.operand(frame, body, operand, location)
            }
            mir::Rvalue::BinaryOp(_, (left, right)) => {
                self.operand(frame, body, left, location);
                self.operand(frame, body, right, location);
            }
            mir::Rvalue::Aggregate(kind, operands) => {
                for operand in operands {
                    self.operand(frame, body, operand, location);
                }
                // `ptr::from_raw_parts` and `with_metadata_of`: a thin data
                // pointer re-viewed at `pointee` with no cast (route P).
                if let (mir::AggregateKind::RawPtr(pointee, mutability), Some(data)) =
                    (&**kind, operands.iter().next())
                {
                    let span = body.source_info(location).span;
                    let source = data.ty(body, self.tcx);
                    let target = Ty::new_ptr(self.tcx, *pointee, *mutability);
                    if let (Some(source), Some(target)) = (
                        self.instance_ty(frame, source, span),
                        self.instance_ty(frame, target, span),
                    ) {
                        let site = self.site(frame.owner, span);
                        self.pun(frame, mir::CastKind::PtrToPtr, source, target, site);
                    }
                }
            }
            mir::Rvalue::Cast(kind, operand, target) => {
                self.operand(frame, body, operand, location);
                self.cast(frame, body, *kind, operand, *target, location);
            }
            mir::Rvalue::ThreadLocalRef(def) => {
                let site = self.site(frame.owner, body.source_info(location).span);
                self.read_value(frame, *def, ty::GenericArgs::empty(), site);
            }
            mir::Rvalue::RawPtr(_, place) => {
                // LIFETIME-ERASE: a raw pointer to a place that may hold a
                // `dyn` value (a `dyn` place itself, or one whose type carries
                // a reference to one).
                let span = body.source_info(location).span;
                if let Some(ty) = self.instance_ty(frame, place.ty(body, self.tcx).ty, span) {
                    self.erase_lifetimes(ty, frame.typing_env);
                }
                self.field_puns(frame, body, *place, location);
            }
            mir::Rvalue::Ref(_, _, place) => self.field_puns(frame, body, *place, location),
            mir::Rvalue::Discriminant(_)
            | mir::Rvalue::CopyForDeref(_)
            | mir::Rvalue::Reborrow(..) => {}
        }
    }

    fn cast(
        &mut self,
        frame: &Frame<'tcx>,
        body: &mir::Body<'tcx>,
        kind: mir::CastKind,
        operand: &mir::Operand<'tcx>,
        target: Ty<'tcx>,
        location: Location,
    ) {
        match kind {
            // Unsizes, reifications and closure casts are `MentionedItems`'s;
            // the others change no callable's key.
            // `&[T; N]` to `*const T`: a reference becomes a raw pointer.
            mir::CastKind::PointerCoercion(PointerCoercion::ArrayToPointer, _) => {
                let span = body.source_info(location).span;
                if let Some(source) = self.instance_ty(frame, operand.ty(body, self.tcx), span) {
                    self.erase_lifetimes(source, frame.typing_env);
                }
            }
            mir::CastKind::PointerCoercion(
                PointerCoercion::Unsize
                | PointerCoercion::ReifyFnPointer(_)
                | PointerCoercion::ClosureFnPointer(_)
                | PointerCoercion::UnsafeFnPointer
                | PointerCoercion::MutToConstPointer,
                _,
            )
            | mir::CastKind::IntToInt
            | mir::CastKind::FloatToInt
            | mir::CastKind::FloatToFloat
            | mir::CastKind::IntToFloat
            | mir::CastKind::Subtype => {}
            mir::CastKind::Transmute
            | mir::CastKind::BoxDerefTransmute
            | mir::CastKind::PtrToPtr
            | mir::CastKind::FnPtrToPtr
            | mir::CastKind::PointerExposeProvenance
            | mir::CastKind::PointerWithExposedProvenance => {
                let span = body.source_info(location).span;
                let source = operand.ty(body, self.tcx);
                let (Some(source), Some(target)) =
                    (self.instance_ty(frame, source, span), self.instance_ty(frame, target, span))
                else {
                    return;
                };
                let site = self.site(frame.owner, span);
                self.launder(frame, source, target, site);
                self.pun(frame, kind, source, target, site);
            }
        }
    }

    /// LAUNDER (route V, a value reinterpretation): a cast that turns a
    /// function pointer the value holds IN ITS OWN BYTES (not behind a
    /// reference or pointer: those are route P, [`Self::pun`]) into something
    /// that does not keep it as a fn pointer of a matching shape: `f as
    /// usize`, `f as *const ()`, a transmute to another call shape, or one
    /// that moves its bytes onto data (`(fn(), usize)` read as `(usize,
    /// fn())`: the census reads no layout, so a target with any data position
    /// may receive them; [`reinterpret`]). Keys are coarse on purpose, so
    /// core's own fn-to-fn transmute in `fmt::rt` keeps its key and is no
    /// LAUNDER (design §5.4); reading a pointer's address
    /// (`fmt::Arguments::as_str`'s tag test) is none either. Data turned into
    /// a fn pointer launders nothing by itself: in the census's world only a
    /// recorded LAUNDER could have put a callable there. A value LAUNDER is
    /// still a LAUNDER of `Any` (Phase A of the typed LAUNDER, design §10):
    /// it makes data a carrier of any callable and demotes every confined
    /// member; the fn pools stay keyed by shape (a laundered callable called
    /// back at a shape its own does not match is UB, R4). LIFETIME-ERASE:
    /// every principal either side may carry ([`Self::erase_lifetimes`]).
    fn launder(
        &mut self,
        frame: &Frame<'tcx>,
        source: Ty<'tcx>,
        target: Ty<'tcx>,
        site: ReachSite,
    ) {
        let typing_env = frame.typing_env;
        let laundered = self.peel(source, typing_env) != self.peel(target, typing_env) && {
            let (from, to) =
                (self.own_bytes(source, typing_env), self.own_bytes(target, typing_env));
            !reinterpret(&from, &to).is_empty()
        };
        if laundered {
            self.note_launder(frame, || format!("{source} -> {target}"));
            if self.debug && !self.laundered_at.contains_key(&CarriedKey::Any) {
                let at = self.describe_node(frame.node);
                let what = rustc_middle::ty::print::with_no_trimmed_paths!(format!(
                    "{at} (value {source} -> {target})"
                ));
                self.laundered_at.insert(CarriedKey::Any, what);
            }
            self.graph.add_launder(site);
        }
        // LIFETIME-ERASE: a reinterpretation of either side's bytes may
        // extend a reference's lifetime (`transmute::<&'a mut dyn P, &'static
        // mut dyn P>`, a struct holding one transmuted to its `'static` twin,
        // a raw pointer cast to or from a pointer to one).
        self.erase_lifetimes(source, frame.typing_env);
        self.erase_lifetimes(target, frame.typing_env);
    }

    /// Route V through `FnPtr::addr`'s shim: the code address of a fn pointer
    /// of type `fn_ptr` read as data, a LAUNDER of its shape (of `Any` when
    /// the type is no fn pointer the census can state).
    fn fn_ptr_addr(&mut self, frame: &Frame<'tcx>, fn_ptr: Ty<'tcx>, site: ReachSite) {
        let key = match fn_ptr.kind() {
            ty::FnPtr(..) => CarriedKey::Key(PoolKey::Fn(self.fn_shape(fn_ptr.fn_sig(self.tcx)))),
            _ => CarriedKey::Any,
        };
        let keys = Rc::new(vec![LaunderKey::Key(key)]);
        self.record_launder(frame, keys, site, || format!("address of `{fn_ptr}`"));
    }

    /// The first LAUNDER's place, for the census's own measurement
    /// (`TRUST_SPAWN_CENSUS_DEBUG`'s summary).
    fn note_launder(&mut self, frame: &Frame<'tcx>, what: impl FnOnce() -> String) {
        if self.launder_at.is_some() {
            return;
        }
        let at = self.node_keys.get(&frame.node).map(|index| self.keys[*index]);
        self.launder_at = Some(rustc_middle::ty::print::with_no_trimmed_paths!(match at {
            Some(Key::Body { def, .. } | Key::Value { def, .. } | Key::Promoted { def, .. }) => {
                format!("{} ({})", self.tcx.def_path_str(def), what())
            }
            _ => format!("({})", what()),
        }));
    }

    /// LIFETIME-ERASE every principal a value of `ty` may carry: unsafe code
    /// that reinterprets it may make a reference to a frame's local outlive
    /// the frame, so no member of those principals stays confined (the
    /// engine also demotes every principal an upcast makes of one).
    fn erase_lifetimes(&mut self, ty: Ty<'tcx>, typing_env: ty::TypingEnv<'tcx>) {
        for key in self.carried(ty, typing_env).iter() {
            let principal = match key {
                CarriedKey::Principal(principal) => *principal,
                CarriedKey::Key(key) => match key.principal() {
                    Some(principal) => principal,
                    None => continue,
                },
                // An opaque value (a coroutine's saved state, a type past the
                // recursion limit) may hold any confined erasure.
                CarriedKey::Any | CarriedKey::AnyDyn => {
                    self.demote_all_confined = true;
                    continue;
                }
                CarriedKey::AnyFn | CarriedKey::Untyped | CarriedKey::Laundered => continue,
            };
            self.graph.add_lifetime_erase(principal);
        }
    }

    /// LIFETIME-ERASE what every union a local of `ty` reaches (in its own
    /// bytes or behind a pointer) may carry: reading a union through another
    /// field reinterprets its bytes as a transmute does.
    fn erase_union_lifetimes(&mut self, ty: Ty<'tcx>, typing_env: ty::TypingEnv<'tcx>) {
        let memo = (ty, memo_env(&[ty], typing_env));
        if let Some(principals) = self.union_principals.get(&memo) {
            for &principal in principals {
                self.graph.add_lifetime_erase(principal);
            }
            return;
        }
        let tcx = self.tcx;
        let mut unions: Vec<Ty<'tcx>> = Vec::new();
        let mut entered = Entered::new();
        let mut stack = vec![(ty, Entered::ROOT)];
        let mut seen: FxHashSet<Ty<'tcx>> = FxHashSet::default();
        while let Some((ty, path)) = stack.pop() {
            if !seen.insert(ty) {
                continue;
            }
            if self.depth(ty) > self.limit {
                // Unions past the recursion limit cannot be named.
                self.demote_all_confined = true;
                continue;
            }
            let ty = normalize(tcx, typing_env, ty).unwrap_or(ty);
            match *ty.kind() {
                // Behind the pointers that do not name it (`Vec<T>`'s buffer).
                ty::Adt(adt, args) if adt.is_phantom_data() => stack.push((args.type_at(0), path)),
                ty::Adt(adt, args) => {
                    if adt.is_union() {
                        unions.push(ty);
                    }
                    let depth = self.depth(ty);
                    match entered.enter(&mut self.unbounded, path, adt.did(), depth) {
                        Some(below) => stack.extend(
                            adt.all_fields()
                                .map(|field| (field.ty(tcx, args).skip_norm_wip(), below)),
                        ),
                        // Polymorphic recursion ([`REENTRIES`]): the unions
                        // below cannot all be named.
                        None => self.demote_all_confined = true,
                    }
                }
                ty::Ref(_, inner, _)
                | ty::RawPtr(inner, _)
                | ty::Array(inner, _)
                | ty::Slice(inner)
                | ty::Pat(inner, _) => stack.push((inner, path)),
                ty::Tuple(elements) => stack.extend(elements.iter().map(|element| (element, path))),
                ty::Closure(_, args) => {
                    stack.extend(args.as_closure().upvar_tys().iter().map(|upvar| (upvar, path)))
                }
                ty::CoroutineClosure(_, args) => stack.extend(
                    args.as_coroutine_closure().upvar_tys().iter().map(|upvar| (upvar, path)),
                ),
                ty::Coroutine(_, args) => {
                    stack.extend(args.as_coroutine().upvar_tys().iter().map(|upvar| (upvar, path)))
                }
                _ => {}
            }
        }
        let mut principals: BTreeSet<PrincipalKey> = BTreeSet::new();
        for union in unions {
            for key in self.carried(union, typing_env).iter() {
                match key {
                    CarriedKey::Principal(principal) => {
                        principals.insert(*principal);
                    }
                    CarriedKey::Key(key) => principals.extend(key.principal()),
                    CarriedKey::Any | CarriedKey::AnyDyn => self.demote_all_confined = true,
                    CarriedKey::AnyFn | CarriedKey::Untyped | CarriedKey::Laundered => {}
                }
            }
        }
        let principals: Vec<PrincipalKey> = principals.into_iter().collect();
        for principal in &principals {
            self.graph.add_lifetime_erase(*principal);
        }
        self.union_principals.insert(memo, principals);
    }

    fn terminator(
        &mut self,
        frame: &Frame<'tcx>,
        body: &mir::Body<'tcx>,
        terminator: &mir::Terminator<'tcx>,
        location: Location,
    ) {
        let span = terminator.source_info.span;
        match &terminator.kind {
            TerminatorKind::Goto { .. }
            | TerminatorKind::UnwindResume
            | TerminatorKind::Return
            | TerminatorKind::Unreachable
            | TerminatorKind::CoroutineDrop
            | TerminatorKind::FalseEdge { .. }
            | TerminatorKind::FalseUnwind { .. } => {}
            // The drop itself is `MentionedItems`'s; the glue is handed a
            // pointer to the dropped place, which for a field views its base
            // (route F). Whether the instance's type needs a drop: one that
            // does not instantiate may.
            TerminatorKind::Drop { place, .. } => {
                // Metadata types may carry rigid aliases. instance_ty uses
                // mono's EarlyBinder invalidation and caller instantiation
                // before needs_drop, and conservatively launders a failure.
                if frame.mode != Mode::Const
                    && self
                        .instance_ty(frame, place.ty(body, self.tcx).ty, span)
                        .is_none_or(|ty| census_needs_drop(self.tcx, frame.typing_env, ty))
                {
                    self.field_puns(frame, body, *place, location);
                }
            }
            TerminatorKind::SwitchInt { discr, .. } => self.operand(frame, body, discr, location),
            TerminatorKind::UnwindTerminate(reason) => {
                self.lang_item_call(frame, reason.lang_item(), span);
            }
            // A call of a fn item is `MentionedItems`'s; the callee operand's
            // constant (a `const` or promoted fn pointer called directly,
            // `PG()`) and the arguments' constants are here.
            TerminatorKind::Call { func, args, .. }
            | TerminatorKind::TailCall { func, args, .. } => {
                if !matches!(func.ty(body, self.tcx).kind(), ty::FnDef(..)) {
                    self.operand(frame, body, func, location);
                }
                for arg in args.iter() {
                    self.operand(frame, body, &arg.node, location);
                }
            }
            TerminatorKind::Assert { cond, msg, .. } => {
                self.operand(frame, body, cond, location);
                self.lang_item_call(frame, assert_panic_lang_item(msg), span);
            }
            TerminatorKind::Yield { value, .. } => self.operand(frame, body, value, location),
            TerminatorKind::InlineAsm { asm_macro, template, operands, .. } => {
                let site = self.site(frame.owner, span);
                let runs_nothing = asm_executes_nothing(*asm_macro, template, operands);
                if !runs_nothing {
                    self.unknown(frame.node, DependencyRefusalKind::InlineAsm, site);
                    // Assembly that runs may turn any callable it can name or
                    // reach (a `sym`, a fn pointer it is handed, one in memory
                    // it is pointed at) into data: a LAUNDER of an unknown
                    // callable, beside the sink (a1/a2 of the P2m follow-up's
                    // soundness review, with an instruction in the template).
                    self.note_launder(frame, || "inline assembly".to_owned());
                    if self.debug && !self.laundered_at.contains_key(&CarriedKey::Any) {
                        let at = self.describe_node(frame.node);
                        self.laundered_at
                            .insert(CarriedKey::Any, format!("{at} (inline assembly)"));
                    }
                    self.graph.add_launder(site);
                }
                for operand in operands.iter() {
                    match operand {
                        mir::InlineAsmOperand::In { value, .. } => {
                            self.operand(frame, body, value, location)
                        }
                        mir::InlineAsmOperand::InOut { in_value, out_place, .. } => {
                            self.operand(frame, body, in_value, location);
                            // An `inout` register hands the input's bits to
                            // the output place. With no instruction run, that
                            // is exactly a transmute of the input to the
                            // output's type, which rustc admits only between
                            // integers and pointers of one size: `inout(reg) f
                            // => n` reads a fn pointer as an integer, a
                            // LAUNDER (the soundness review's a1/a2).
                            if let (true, Some(out_place)) = (runs_nothing, out_place) {
                                let target = out_place.ty(body, self.tcx).ty;
                                self.cast(
                                    frame,
                                    body,
                                    mir::CastKind::Transmute,
                                    in_value,
                                    target,
                                    location,
                                );
                            }
                        }
                        mir::InlineAsmOperand::Const { value } => {
                            self.constant(frame, value.const_, site)
                        }
                        mir::InlineAsmOperand::SymStatic { def_id } => {
                            self.read_value(frame, *def_id, ty::GenericArgs::empty(), site)
                        }
                        // `sym fn` is `MentionedItems`'s.
                        mir::InlineAsmOperand::SymFn { .. }
                        | mir::InlineAsmOperand::Out { .. }
                        | mir::InlineAsmOperand::Label { .. } => {}
                    }
                }
            }
        }
        if let Some(mir::UnwindAction::Terminate(reason)) = terminator.unwind() {
            self.lang_item_call(frame, reason.lang_item(), span);
        }
    }

    fn operand(
        &mut self,
        frame: &Frame<'tcx>,
        body: &mir::Body<'tcx>,
        operand: &mir::Operand<'tcx>,
        location: Location,
    ) {
        match operand {
            mir::Operand::Constant(constant) => {
                let site = self.site(frame.owner, body.source_info(location).span);
                self.constant(frame, constant.const_, site);
            }
            mir::Operand::Copy(_) | mir::Operand::Move(_) | mir::Operand::RuntimeChecks(_) => {}
        }
    }

    /// A panic or unwind-termination lang item a terminator runs. It is also
    /// recorded as covered in the body (self-audit check 2 compares the codegen
    /// body's panics with these).
    fn lang_item_call(&mut self, frame: &Frame<'tcx>, item: LangItem, span: Span) {
        if frame.mode == Mode::Const {
            // A compile-time panic is a compile error.
            return;
        }
        let site = self.site(frame.owner, span);
        if self.fault != Some(TestFault::ForgetCoverage) {
            if let Some(mention) = lang_item_mention(self.tcx, item) {
                self.cover(frame.owner, mention);
            }
        }
        match self.tcx.lang_items().get(item) {
            Some(def) => {
                let args = GenericArgs::identity_for_item(self.tcx, def);
                match self.body_node(def, args, None) {
                    Ok(callee) => {
                        self.graph.add_edge(frame.node, callee, EdgeClass::Run, site, false)
                    }
                    Err(reason) => self.unknown(frame.node, reason, site),
                }
            }
            None => self.unknown(frame.node, DependencyRefusalKind::ResolutionError, site),
        }
    }

    /// Record `item` as covered in the local body `owner` (self-audit check 2).
    fn cover(&mut self, owner: Option<LocalDefId>, item: MentionedItem<'tcx>) {
        if let Some(owner) = owner {
            let covered = self.covered.entry(owner).or_default();
            if !covered.contains(&item) {
                covered.push(item);
            }
        }
    }

    // ----- calls -------------------------------------------------------------------

    fn call(
        &mut self,
        frame: &Frame<'tcx>,
        callee: Ty<'tcx>,
        arg_tys: &[Ty<'tcx>],
        site: ReachSite,
    ) {
        let node = frame.node;
        let Some(callee) = self.mono(frame, callee) else {
            return self.unknown(node, DependencyRefusalKind::ResolutionError, site);
        };
        let Some(args) = arg_tys.iter().map(|ty| self.mono(frame, *ty)).collect::<Option<Vec<_>>>()
        else {
            return self.unknown(node, DependencyRefusalKind::ResolutionError, site);
        };
        match *callee.kind() {
            ty::FnDef(def, fn_args) => {
                self.call_fn_def(frame, def, fn_args.skip_binder(), &args, site, false)
            }
            ty::FnPtr(..) => {
                if frame.mode == Mode::Const {
                    return self.unknown(node, DependencyRefusalKind::ResolutionError, site);
                }
                let shape = self.fn_shape(callee.fn_sig(self.tcx));
                let carried = self.carried_all(&args, frame.typing_env);
                self.invoke(node, PoolKey::Fn(shape), carried, site, false);
            }
            _ => self.unknown(node, DependencyRefusalKind::ResolutionError, site),
        }
    }

    fn call_fn_def(
        &mut self,
        frame: &Frame<'tcx>,
        def: DefId,
        fn_args: GenericArgs<'tcx>,
        args: &[Ty<'tcx>],
        site: ReachSite,
        via_drop: bool,
    ) {
        let tcx = self.tcx;
        let node = frame.node;
        if tcx.is_constructor(def) {
            return;
        }
        if let Some(dropped) = drop_glue_call(tcx, def, fn_args) {
            // `core::ptr::drop_glue::<T>` (what `ptr::drop_in_place` calls) runs
            // T's drop glue, which the census decomposes itself (design §5.3,
            // Drops). It never asks rustc's resolver: for a coroutine that
            // demands the coroutine's `optimized_mir` (`rustc_ty_utils`'s
            // `resolve_instance`, for its async drop), and `inner_optimized_mir`
            // forces this census (E0391, design §8). A compile-time drop runs
            // nothing at run time.
            if frame.mode == Mode::Run {
                self.drop_edge(node, dropped, frame.env, frame.typing_env, site);
                self.drop_handoff(frame, dropped, site);
            }
            return;
        }
        // rustc's resolver reports an overflow as a FATAL error, not an
        // answer: selecting a blanket impl for a type nested as deep as the
        // recursion limit needs that many obligations. An instantiation near
        // the limit is refused before the resolver is asked, or a valid
        // program (a blanket impl's method calling itself at a larger type)
        // would be rejected.
        if self.near_limit(fn_args) {
            self.cut = true;
            return self.unknown(node, DependencyRefusalKind::Widened, site);
        }
        if frame.mode == Mode::Const {
            // What a compile-time call returns flows into the value: a READ.
            return match ty::Instance::try_resolve(tcx, frame.typing_env, def, fn_args) {
                Ok(Some(instance)) => match self.member(instance, frame.env) {
                    Ok(member) => self.graph.add_edge(node, member, EdgeClass::Read, site, false),
                    Err(reason) => self.unknown(node, reason, site),
                },
                Ok(None) if fn_args.has_param() => self.param(node, site),
                Ok(None) | Err(_) => {
                    self.unknown(node, DependencyRefusalKind::ResolutionError, site)
                }
            };
        }
        if is_std_thread_spawn(tcx, def) {
            return self.spawn(frame, def, fn_args, site, via_drop);
        }
        if tcx.is_foreign_item(def) {
            return self.foreign_call(frame, def, args, site, via_drop);
        }
        if let Some(intrinsic) = tcx.intrinsic(def) {
            return self.intrinsic_call(frame, def, fn_args, intrinsic, args, site);
        }
        match ty::Instance::try_resolve(tcx, frame.typing_env, def, fn_args) {
            Ok(Some(instance)) => self.run_instance(frame, instance, args, site, via_drop),
            // Through the caller's own type parameters: exact per instance (R1).
            Ok(None) if fn_args.has_param() || fn_args.has_aliases() => self.param(node, site),
            // A concrete call the resolver declines (the type-length limit).
            Ok(None) => self.unknown(node, DependencyRefusalKind::Widened, site),
            Err(_) => self.unknown(node, DependencyRefusalKind::ResolutionError, site),
        }
    }

    /// What a call of `instance` runs (design §5.3, Resolution).
    fn run_instance(
        &mut self,
        frame: &Frame<'tcx>,
        instance: Instance<'tcx>,
        args: &[Ty<'tcx>],
        site: ReachSite,
        via_drop: bool,
    ) {
        let tcx = self.tcx;
        let node = frame.node;
        match instance.def {
            InstanceKind::Item(def) => {
                if is_std_thread_spawn(tcx, def) {
                    return self.spawn(frame, def, instance.args, site, via_drop);
                }
                if tcx.is_foreign_item(def) {
                    return self.foreign_call(frame, def, args, site, via_drop);
                }
                if tcx.is_constructor(def) {
                    return;
                }
                match self.body_node(def, instance.args, frame.env) {
                    Ok(callee) => {
                        self.graph.add_edge(node, callee, EdgeClass::Run, site, via_drop);
                        if !def.is_local() {
                            self.handoff(frame, callee, args, site, via_drop);
                        }
                        if frame.locality == Locality::Local && self.opaque.contains(&callee) {
                            // What MIR-less code returns was minted out of sight.
                            let sig =
                                tcx.fn_sig(def).instantiate(tcx, instance.args).skip_norm_wip();
                            let output = tcx.instantiate_bound_regions_with_erased(sig).output();
                            if let Ok(output) = normalize(tcx, frame.typing_env, output) {
                                self.name_local_type(output, frame.typing_env);
                            }
                        }
                    }
                    Err(reason) => self.unknown(node, reason, site),
                }
            }
            InstanceKind::LlvmIntrinsic(_) => {
                self.unknown(node, DependencyRefusalKind::ResolutionError, site)
            }
            InstanceKind::Intrinsic(def) => match tcx.intrinsic(def) {
                Some(intrinsic) => {
                    self.intrinsic_call(frame, def, instance.args, intrinsic, args, site)
                }
                None => self.unknown(node, DependencyRefusalKind::ResolutionError, site),
            },
            InstanceKind::Virtual(def, _) => {
                self.virtual_call(frame, def, instance.args, args, site, via_drop)
            }
            InstanceKind::Shim(shim) => match shim {
                // The shim calls the TRAIT method `def` on `*self`: what that
                // resolves to for the concrete self type.
                ShimKind::VTable(def) => {
                    self.call_fn_def(frame, def, instance.args, args, site, via_drop)
                }
                // Over a trait method (a `#[track_caller]` closure's, or a
                // virtual call's) the shim calls that method; over an item, the
                // item.
                ShimKind::Reify(def, _) => {
                    if tcx.trait_of_assoc(def).is_none() {
                        self.run_instance(
                            frame,
                            Instance::new_raw(def, instance.args),
                            args,
                            site,
                            via_drop,
                        )
                    } else if instance.args.types().next().is_some_and(|ty| ty.is_trait()) {
                        self.virtual_call(frame, def, instance.args, args, site, via_drop)
                    } else {
                        self.call_fn_def(frame, def, instance.args, args, site, via_drop)
                    }
                }
                ShimKind::FnPtr(_, self_ty) => match *self_ty.kind() {
                    ty::FnPtr(..) => {
                        let shape = self.fn_shape(self_ty.fn_sig(tcx));
                        let carried = self.carried_all(args, frame.typing_env);
                        self.invoke(node, PoolKey::Fn(shape), carried, site, via_drop);
                    }
                    ty::FnDef(def, fn_args) => {
                        self.call_fn_def(frame, def, fn_args.skip_binder(), args, site, via_drop)
                    }
                    _ => self.unknown(node, DependencyRefusalKind::ResolutionError, site),
                },
                // Both shims' arguments are the trait's, `[self, inputs]`; the
                // closure's own arguments are its self type's.
                ShimKind::ClosureOnce { closure: def, .. }
                | ShimKind::ConstructCoroutineInClosure { coroutine_closure_def_id: def, .. } => {
                    match instance.args.types().next().map(|ty| *ty.kind()) {
                        Some(
                            ty::Closure(closure, closure_args)
                            | ty::CoroutineClosure(closure, closure_args),
                        ) if closure == def => self.run_instance(
                            frame,
                            Instance::new_raw(def, closure_args),
                            args,
                            site,
                            via_drop,
                        ),
                        _ => self.unknown(node, DependencyRefusalKind::ResolutionError, site),
                    }
                }
                ShimKind::ThreadLocal(def) => {
                    self.read_value(frame, def, ty::GenericArgs::empty(), site)
                }
                ShimKind::FutureDropPoll(..)
                | ShimKind::AsyncDropGlue(..)
                | ShimKind::AsyncDropGlueCtor(..) => {
                    self.unknown(node, DependencyRefusalKind::AsyncDropShim, site)
                }
                ShimKind::DropGlue(_, Some(ty)) => match self.drop_node(ty, frame.env) {
                    Ok(glue) => self.graph.add_edge(node, glue, EdgeClass::Run, site, true),
                    Err(reason) => self.unknown(node, reason, site),
                },
                ShimKind::DropGlue(_, None) => {}
                // `<F as FnPtr>::addr`: the fn pointer's code address as a
                // `*const ()`, whose bytes are then data (`addr()`, `Hash`,
                // `PartialEq`, `Ord`, `fn_addr_eq`, `Pointer`). A code address
                // needs no provenance to be called, so this is the value
                // reinterpretation `f as *const ()` is (route V), keyed by the
                // fn pointer's shape: only a fn pointer of that type is ever
                // reinterpreted here.
                ShimKind::FnPtrAsPtr(_, self_ty) | ShimKind::FnPtrFromPtr(_, self_ty) => {
                    self.fn_ptr_addr(frame, self_ty, site)
                }
                ShimKind::Clone(_, ty) => match self.clone_node(ty, frame.env) {
                    Ok(clone) => self.graph.add_edge(node, clone, EdgeClass::Run, site, via_drop),
                    Err(reason) => self.unknown(node, reason, site),
                },
            },
        }
    }

    /// A `dyn` method call charges its DynPool.
    fn virtual_call(
        &mut self,
        frame: &Frame<'tcx>,
        method: DefId,
        instance_args: GenericArgs<'tcx>,
        args: &[Ty<'tcx>],
        site: ReachSite,
        via_drop: bool,
    ) {
        let Some(receiver) = instance_args.types().next() else {
            return self.unknown(frame.node, DependencyRefusalKind::ResolutionError, site);
        };
        let ty::Dynamic(predicates, ..) = *receiver.kind() else {
            return self.unknown(frame.node, DependencyRefusalKind::ResolutionError, site);
        };
        let key = PoolKey::DynMethod {
            principal: self.principal_key(predicates),
            method: MethodKey(self.def_hash(method)),
        };
        let carried = self.carried_all(args, frame.typing_env);
        self.invoke(frame.node, key, carried, site, via_drop);
    }

    /// Rule H: a local frame handing callable-carrying operands to external
    /// code is charged with every pool key that code's closure invokes. Code
    /// with no body here (foreign code, R3; MIR-less Rust, R2) may also DROP
    /// what it is handed by value, `&mut` or raw pointer (an `extern "Rust"`
    /// declaration's definition is Rust): the frame then reaches that drop
    /// glue through an edge that claims no spawn (CREATE caps at ESCAPES).
    ///
    /// Such code may also KEEP what it is handed and call it from any later
    /// call into it (a registered callback): what it is handed is held by the
    /// foreign world's node (see [`Self::emit_pool_facts`]), which every call
    /// into such code reaches. The sysroot's own calls into foreign code (the
    /// platform's C library, the panic runtime) are exempt: std registers
    /// nothing there that runs as part of a caller but its thread-exit
    /// destructors (R6). A MIR-less dependency body is never exempt, whoever
    /// calls it (std's generic code runs a dependency's methods).
    fn handoff(
        &mut self,
        frame: &Frame<'tcx>,
        callee: ReachNode,
        args: &[Ty<'tcx>],
        site: ReachSite,
        via_drop: bool,
    ) {
        if frame.mode == Mode::Const {
            return;
        }
        let local = frame.locality == Locality::Local;
        let mirless_body = matches!(
            self.node_keys.get(&callee).map(|index| self.keys[*index]),
            Some(Key::Body { .. })
        );
        let keeps = self.world_of.contains_key(&callee)
            && (mirless_body
                || !frame
                    .instance
                    .is_some_and(|instance| in_sysroot(self.tcx, instance.def_id().krate)));
        if !local && !keeps {
            return;
        }
        let carried = self.carried_all(args, frame.typing_env);
        if keeps && !carried.is_empty() {
            self.note_carried(frame.node, &carried);
            self.handed_out.extend(carried.iter().cloned());
        }
        if !local {
            return;
        }
        if !carried.is_empty() {
            self.handoff_fact(frame.node, callee, carried, site, via_drop);
        }
        if !self.opaque.contains(&callee) {
            return;
        }
        let tcx = self.tcx;
        for &arg in args {
            let owned = match *arg.kind() {
                ty::Ref(_, pointee, ty::Mutability::Mut) | ty::RawPtr(pointee, _) => pointee,
                _ => arg,
            };
            if !census_needs_drop(tcx, frame.typing_env, owned) {
                continue;
            }
            match self.drop_node(owned, frame.env) {
                Ok(glue) => self.graph.add_edge(frame.node, glue, EdgeClass::Create, site, true),
                Err(reason) => self.unknown(frame.node, reason, site),
            }
        }
    }

    /// A call of a seed. The thread's entry is what `FnOnce::call_once` runs on
    /// the seed's `F` (every seed is `F: FnOnce() -> T`), when `F` names a
    /// closure or fn item; otherwise the spawn names no entry.
    fn spawn(
        &mut self,
        frame: &Frame<'tcx>,
        seed: DefId,
        seed_args: GenericArgs<'tcx>,
        site: ReachSite,
        via_drop: bool,
    ) {
        let tcx = self.tcx;
        let seed_node = self.node(Key::Seed(seed));
        let generics = tcx.generics_of(seed);
        let entry = (0..generics.count())
            .map(|index| generics.param_at(index, tcx))
            .find(|param| param.name.as_str() == "F")
            .and_then(|param| seed_args.get(param.index as usize))
            .and_then(|arg| arg.as_type())
            .filter(|callable| {
                // A closure or a fn item, itself or behind what forwards a
                // call to it (`Box<F>`, `&F`, `AssertUnwindSafe<F>`): the
                // wrapper's own `call_once` is walked, and runs it.
                let mut callable = *callable;
                loop {
                    callable = match *callable.kind() {
                        ty::Ref(_, inner, _) => inner,
                        ty::Adt(adt, args)
                            if adt.is_box()
                                || (in_sysroot(tcx, adt.did().krate)
                                    && tcx.item_name(adt.did()).as_str() == "AssertUnwindSafe") =>
                        {
                            args.type_at(0)
                        }
                        _ => break,
                    };
                }
                matches!(callable.kind(), ty::Closure(..) | ty::FnDef(..))
            })
            .and_then(|callable| self.call_once_member(callable, frame));
        self.graph.add_spawn(frame.node, seed_node, entry, site, via_drop);
    }

    /// The node `FnOnce::call_once(callable, ())` runs, if it resolves.
    fn call_once_member(&mut self, callable: Ty<'tcx>, frame: &Frame<'tcx>) -> Option<ReachNode> {
        let tcx = self.tcx;
        let fn_once = tcx.lang_items().get(LangItem::FnOnce)?;
        let call_once = tcx
            .associated_item_def_ids(fn_once)
            .iter()
            .copied()
            .find(|item| tcx.item_name(*item) == sym::call_once)?;
        let args = tcx.mk_args(&[callable.into(), tcx.types.unit.into()]);
        let instance = ty::Instance::try_resolve(tcx, frame.typing_env, call_once, args).ok()??;
        self.member(instance, frame.env).ok()
    }

    fn intrinsic_call(
        &mut self,
        frame: &Frame<'tcx>,
        def: DefId,
        fn_args: GenericArgs<'tcx>,
        intrinsic: ty::IntrinsicDef,
        args: &[Ty<'tcx>],
        site: ReachSite,
    ) {
        let tcx = self.tcx;
        let node = frame.node;
        if ValidityRequirement::from_intrinsic(intrinsic.name).is_some() {
            match tcx.lang_items().get(LangItem::PanicNounwind) {
                Some(panic) => match self.body_node(panic, ty::GenericArgs::empty(), None) {
                    Ok(callee) => self.graph.add_edge(node, callee, EdgeClass::Run, site, false),
                    Err(reason) => self.unknown(node, reason, site),
                },
                None => self.unknown(node, DependencyRefusalKind::ResolutionError, site),
            }
        }
        if intrinsic.name == sym::catch_unwind {
            // `catch_unwind(try_fn, data, catch_fn)` calls its fn pointers.
            let carried = self.carried_all(args, frame.typing_env);
            for arg in args {
                if let ty::FnPtr(..) = arg.kind() {
                    let shape = self.fn_shape(arg.fn_sig(tcx));
                    self.invoke(node, PoolKey::Fn(shape), carried.clone(), site, false);
                }
            }
        } else if intrinsic.name == sym::const_eval_select {
            // At run time, the third generic argument runs.
            match fn_args.types().nth(2).map(|runtime| *runtime.kind()) {
                Some(ty::FnDef(runtime, runtime_args)) => {
                    self.call_fn_def(frame, runtime, runtime_args.skip_binder(), &[], site, false)
                }
                Some(ty::Closure(..)) => match fn_args
                    .types()
                    .nth(2)
                    .and_then(|callable| self.call_once_member(callable, frame))
                {
                    Some(callee) => self.graph.add_edge(node, callee, EdgeClass::Run, site, false),
                    None => self.unknown(node, DependencyRefusalKind::ResolutionError, site),
                },
                Some(_) if fn_args.has_param() => self.param(node, site),
                _ => self.unknown(node, DependencyRefusalKind::ResolutionError, site),
            }
        } else if !intrinsic.must_be_overridden {
            // RUN to the fallback body.
            match self.body_node(def, fn_args, frame.env) {
                Ok(callee) => self.graph.add_edge(node, callee, EdgeClass::Run, site, false),
                Err(reason) => self.unknown(node, reason, site),
            }
        }
        // Every other intrinsic is implemented by the backend and calls nothing.
    }

    // ----- foreign symbols -----------------------------------------------------------------

    fn foreign_call(
        &mut self,
        frame: &Frame<'tcx>,
        def: DefId,
        args: &[Ty<'tcx>],
        site: ReachSite,
        via_drop: bool,
    ) {
        if frame.locality == Locality::Local {
            // What foreign code returns was minted out of sight (R3).
            let sig = self.tcx.fn_sig(def).instantiate_identity().skip_norm_wip();
            let output = self.tcx.instantiate_bound_regions_with_erased(sig).output();
            self.name_local_type(output, frame.typing_env);
        }
        let callee = self.foreign_target(def);
        self.graph.add_edge(frame.node, callee, EdgeClass::Run, site, via_drop);
        self.handoff(frame, callee, args, site, via_drop);
        // What foreign code returns may point to memory it reads later (a
        // registration slot): a store through it hands foreign code what that
        // memory can be made to hold, as a store into an `extern` static does.
        // The sysroot's own calls are exempt (R3, R6), as in `handoff`.
        if self.world_of.contains_key(&callee)
            && !frame.instance.is_some_and(|instance| in_sysroot(self.tcx, instance.def_id().krate))
        {
            let sig = self.tcx.fn_sig(def).instantiate_identity().skip_norm_wip();
            let output = self.tcx.instantiate_bound_regions_with_erased(sig).output();
            self.foreign_memory(frame.node, output, false, frame.typing_env);
        }
    }

    /// A foreign function resolved by link name (design §5.4, Foreign
    /// symbols), else opaque (R3).
    fn foreign_target(&mut self, def: DefId) -> ReachNode {
        match self.link_target(def) {
            Some(target) => {
                let args = GenericArgs::identity_for_item(self.tcx, target);
                match self.body_node(target, args, None) {
                    Ok(node) => node,
                    Err(_) => self.node(Key::Opaque(def)),
                }
            }
            None => self.node(Key::Opaque(def)),
        }
    }

    fn link_target(&mut self, def: DefId) -> Option<DefId> {
        let tcx = self.tcx;
        self.symbols().link_target(tcx, def)
    }

    fn runtime_symbol(&mut self, name: Symbol) -> Option<DefId> {
        self.symbols().runtime_symbol(name)
    }

    /// The crate graph's link-time names, built once.
    fn symbols(&mut self) -> &SymbolTables {
        let tcx = self.tcx;
        self.symbols.get_or_insert_with(|| SymbolTables::new(tcx))
    }

    // ----- callable values -----------------------------------------------------------------

    /// A fn item reified to a fn pointer: CREATE in the FnPool of its shape.
    fn reify(
        &mut self,
        frame: &Frame<'tcx>,
        callee: Ty<'tcx>,
        target: Option<Ty<'tcx>>,
        site: ReachSite,
    ) {
        let tcx = self.tcx;
        let node = frame.node;
        let Some(callee) = self.mono(frame, callee) else {
            return self.unknown(node, DependencyRefusalKind::ResolutionError, site);
        };
        let ty::FnDef(def, args) = *callee.kind() else {
            return self.unknown(node, DependencyRefusalKind::ResolutionError, site);
        };
        let args = args.skip_binder();
        let shape = match target.and_then(|target| self.mono(frame, target)) {
            Some(target) if target.is_fn_ptr() => self.fn_shape(target.fn_sig(tcx)),
            _ => self.instance_shape(Instance::new_raw(def, args)),
        };
        let member = if is_std_thread_spawn(tcx, def) {
            Ok(self.node(Key::Seed(def)))
        } else if let Some(dropped) = drop_glue_call(tcx, def, args) {
            // A fn pointer to drop glue runs the glue (never resolved: see
            // `call_fn_def`); trivial glue runs nothing.
            if !census_needs_drop(tcx, frame.typing_env, dropped) {
                return;
            }
            self.drop_node(dropped, frame.env)
        } else {
            match ty::Instance::resolve_for_fn_ptr(tcx, frame.typing_env, def, args) {
                Some(instance) => self.member(instance, frame.env),
                None if args.has_param() => return self.param(node, site),
                None => Err(DependencyRefusalKind::ResolutionError),
            }
        };
        match member {
            Ok(member) => self.create(node, member, PoolKey::Fn(shape), false, site),
            Err(reason) => self.unknown(node, reason, site),
        }
    }

    /// A closure cast to a fn pointer: CREATE of its `FnOnce` body.
    fn closure_pointer(
        &mut self,
        frame: &Frame<'tcx>,
        closure: Ty<'tcx>,
        target: Option<Ty<'tcx>>,
        site: ReachSite,
    ) {
        let node = frame.node;
        let Some(closure) = self.mono(frame, closure) else {
            return self.unknown(node, DependencyRefusalKind::ResolutionError, site);
        };
        let ty::Closure(def, args) = *closure.kind() else {
            return self.unknown(node, DependencyRefusalKind::ResolutionError, site);
        };
        let instance = Instance::resolve_closure(self.tcx, def, args, ty::ClosureKind::FnOnce);
        let shape = match target.and_then(|target| self.mono(frame, target)) {
            Some(target) if target.is_fn_ptr() => self.fn_shape(target.fn_sig(self.tcx)),
            _ => self.instance_shape(instance),
        };
        match self.member(instance, frame.env) {
            Ok(member) => self.create(node, member, PoolKey::Fn(shape), false, site),
            Err(reason) => self.unknown(node, reason, site),
        }
    }

    /// An unsizing coercion: each `dyn` it mints CREATEs its vtable's methods
    /// and drop slot; a `dyn` -> `dyn` coercion that changes the principal is
    /// an upcast. `confined`: the coercion erases a reference to a local of
    /// the frame's own body ([`erases_local_reference`]), so its vtable's
    /// members are confined (design §5.4).
    fn unsize(
        &mut self,
        frame: &Frame<'tcx>,
        source: Ty<'tcx>,
        target: Ty<'tcx>,
        site: ReachSite,
        confined: bool,
    ) {
        let node = frame.node;
        let (Some(source), Some(target)) = (self.mono(frame, source), self.mono(frame, target))
        else {
            return self.unknown(node, DependencyRefusalKind::ResolutionError, site);
        };
        for (concrete, predicates, shared) in self.unsize_pairs(frame.typing_env, source, target) {
            if let ty::Dynamic(from, ..) = *concrete.kind() {
                let (from, to) = (self.principal_key(from), self.principal_key(predicates));
                if from != to {
                    self.add_upcast(from, to);
                }
                continue;
            }
            // (A `dyn` whose own bounds name a parameter
            // (`Box<Echo> as Box<dyn Handler<Req>>` in `fn handlers<Req>`) has a
            // vtable per concrete instance too, though the value's type names
            // none: its methods are `<Echo as Handler<Req>>::handle`, which the
            // compiler resolves for concrete trait refs only (review 4 of the
            // review-14 build: a compiler panic in `vtable_slots`, at every
            // declared binding of such a crate.)
            if concrete.has_param()
                || concrete.has_aliases()
                || predicates.has_param()
                || predicates.has_aliases()
            {
                // The vtable is per concrete instance (R1).
                self.param(node, site);
                continue;
            }
            self.vtable(node, concrete, predicates, site, !shared, confined);
        }
    }

    /// The `(concrete, dyn predicates, through a shared &)` pairs an unsizing
    /// coercion from `source` to `target` mints: through references, raw
    /// pointers and `CoerceUnsized` smart pointers (their coerced field) down
    /// to the unsized tail (a struct's last field, a tuple's last element).
    fn unsize_pairs(
        &mut self,
        typing_env: ty::TypingEnv<'tcx>,
        source: Ty<'tcx>,
        target: Ty<'tcx>,
    ) -> Vec<(Ty<'tcx>, &'tcx ty::List<ty::PolyExistentialPredicate<'tcx>>, bool)> {
        let tcx = self.tcx;
        let mut out = Vec::new();
        // (source, target, behind a pointer already, that pointer is a shared &)
        let mut stack = vec![(source, target, false, false)];
        let mut seen: FxHashSet<(Ty<'tcx>, Ty<'tcx>, bool)> = FxHashSet::default();
        while let Some((source, target, pointee, shared)) = stack.pop() {
            let source = normalize(tcx, typing_env, source).unwrap_or(source);
            let target = normalize(tcx, typing_env, target).unwrap_or(target);
            if source == target || !seen.insert((source, target, pointee)) {
                continue;
            }
            if let (true, ty::Dynamic(predicates, ..)) = (pointee, *target.kind()) {
                out.push((source, predicates, shared));
                continue;
            }
            match (*source.kind(), *target.kind()) {
                (ty::Ref(_, s, mutability), ty::Ref(_, t, _) | ty::RawPtr(t, _)) if !pointee => {
                    stack.push((s, t, true, mutability == ty::Mutability::Not))
                }
                (ty::RawPtr(s, _), ty::RawPtr(t, _)) if !pointee => stack.push((s, t, true, false)),
                (ty::Pat(s, _), ty::Pat(t, _)) => stack.push((s, t, pointee, shared)),
                (ty::Tuple(s), ty::Tuple(t)) if pointee && s.len() == t.len() => {
                    if let (Some(&s), Some(&t)) = (s.last(), t.last()) {
                        stack.push((s, t, true, shared));
                    }
                }
                (ty::Adt(source_adt, source_args), ty::Adt(target_adt, target_args))
                    if source_adt == target_adt =>
                {
                    if pointee {
                        // In place behind the pointer: the unsized tail.
                        let last = if source_adt.is_struct() {
                            source_adt.non_enum_variant().fields.iter().last()
                        } else {
                            None
                        };
                        if let Some(last) = last {
                            stack.push((
                                last.ty(tcx, source_args).skip_norm_wip(),
                                last.ty(tcx, target_args).skip_norm_wip(),
                                true,
                                shared,
                            ));
                        }
                    } else {
                        // A smart pointer (`Box`, `Rc`, `Arc`, `Pin<P>`, ...):
                        // its fields that differ, each a pointer again.
                        for field in source_adt.all_fields() {
                            stack.push((
                                field.ty(tcx, source_args).skip_norm_wip(),
                                field.ty(tcx, target_args).skip_norm_wip(),
                                false,
                                false,
                            ));
                        }
                    }
                }
                _ => {}
            }
        }
        out
    }

    /// CREATE every method of the vtable for `concrete as dyn <predicates>`
    /// (its principal and supertraits) in that principal's DynPool, and the
    /// drop slot in its DynDropPool: a CREATE edge unless the vtable was
    /// minted through a shared `&` (the `&`-erasure rule).
    ///
    /// CONFINEMENT (design §5.4). A `confined` vtable erases a reference to a
    /// local of the creating frame: borrowck bounds every copy of that
    /// reference by the local's storage, so the value can be called only
    /// while the frame is live, by code it runs, unless unsafe code extends
    /// the reference's lifetime, which demotes it ([`Self::erase_lifetimes`]:
    /// every cast, transmute, raw pointer and union whose type carries the
    /// principal). Its members are visible to every invoke in a local body;
    /// an invoke in external code sees none of them. What still reaches them:
    /// the creating frame, through its CREATE edge (every caller of it), and
    /// rule H for every local frame that hands a value carrying the principal
    /// to external code, by a call (`handoff`), an indirect call (the
    /// engine's implicit hand-offs) or a drop ([`Self::drop_handoff`]). So a
    /// local function whose execution may run a confined member is charged:
    /// it is the creator or calls it, holds the invoke, or hands the value to
    /// the external code that invokes it.
    fn vtable(
        &mut self,
        creator: ReachNode,
        concrete: Ty<'tcx>,
        predicates: &'tcx ty::List<ty::PolyExistentialPredicate<'tcx>>,
        site: ReachSite,
        drop_create: bool,
        confined: bool,
    ) {
        match self.vtable_slots(concrete, predicates) {
            Ok(slots) => {
                let principal = self.principal_key(predicates);
                self.minted.insert(principal);
                self.note_concrete(principal, concrete);
                if confined {
                    self.confined_principals.insert(principal);
                }
                for (member, key) in slots {
                    if drop_create || !matches!(key, PoolKey::DynDrop(_)) {
                        self.create(creator, member, key, confined, site);
                    } else {
                        self.pool_member(member, key, confined);
                    }
                }
            }
            Err(reason) => self.unknown(creator, reason, site),
        }
    }

    /// A vtable the sysroot mints where no walked body runs: its slots join the
    /// pools with no CREATE edge (design §5.4, membership). A vtable whose slots
    /// do not resolve adds nothing, so its principal stays open.
    fn vtable_members(
        &mut self,
        concrete: Ty<'tcx>,
        predicates: &'tcx ty::List<ty::PolyExistentialPredicate<'tcx>>,
    ) {
        if let Ok(slots) = self.vtable_slots(concrete, predicates) {
            let principal = self.principal_key(predicates);
            self.minted.insert(principal);
            self.note_concrete(principal, concrete);
            for (member, key) in slots {
                self.pool_member(member, key, false);
            }
        }
    }

    /// The members of the vtable for `concrete as dyn <predicates>`, keyed:
    /// each method of the principal and its supertraits, and the drop slot.
    fn vtable_slots(
        &mut self,
        concrete: Ty<'tcx>,
        predicates: &'tcx ty::List<ty::PolyExistentialPredicate<'tcx>>,
    ) -> Result<Vec<(ReachNode, PoolKey)>, DependencyRefusalKind> {
        let tcx = self.tcx;
        let typing_env = ty::TypingEnv::fully_monomorphized();
        let principal = self.principal_key(predicates);
        let mut slots = Vec::new();
        if let Some(principal_trait) = predicates.principal() {
            let trait_ref = tcx.instantiate_bound_regions_with_erased(
                principal_trait
                    .map_bound(|principal_trait| principal_trait.with_self_ty(tcx, concrete)),
            );
            let supertraits: Vec<ty::TraitRef<'tcx>> =
                rustc_type_ir::elaborate::supertraits(tcx, ty::Binder::dummy(trait_ref))
                    .map(|supertrait| tcx.instantiate_bound_regions_with_erased(supertrait))
                    .collect();
            for supertrait in supertraits {
                for &method in tcx.own_existential_vtable_entries(supertrait.def_id) {
                    let args = GenericArgs::for_item(tcx, method, |param, _| match param.kind {
                        ty::GenericParamDefKind::Lifetime => tcx.lifetimes.re_erased.into(),
                        ty::GenericParamDefKind::Type { .. }
                        | ty::GenericParamDefKind::Const { .. } => {
                            supertrait.args[param.index as usize]
                        }
                    });
                    let args = tcx
                        .try_normalize_erasing_regions(typing_env, ty::Unnormalized::new_wip(args))
                        .map_err(|_| DependencyRefusalKind::ResolutionError)?;
                    if tcx.instantiate_and_check_impossible_clauses((method, args)) {
                        continue;
                    }
                    // (Asked of concrete trait refs only: one that names a
                    // parameter is read per instance, `unsize`. Fail-closed,
                    // never a compiler panic.)
                    if args.has_param() {
                        return Err(DependencyRefusalKind::ResolutionError);
                    }
                    let instance = Instance::expect_resolve_for_vtable(
                        tcx, typing_env, method, args, DUMMY_SP,
                    );
                    let member = self.member(instance, None)?;
                    let key =
                        PoolKey::DynMethod { principal, method: MethodKey(self.def_hash(method)) };
                    slots.push((member, key));
                }
            }
        }
        if census_needs_drop(tcx, typing_env, concrete) {
            slots.push((self.drop_node(concrete, None)?, PoolKey::DynDrop(principal)));
        }
        Ok(slots)
    }

    // ----- constants -------------------------------------------------------------------------

    fn constant(&mut self, frame: &Frame<'tcx>, constant: mir::Const<'tcx>, site: ReachSite) {
        let node = frame.node;
        let Some(constant) = self.mono(frame, constant) else {
            return self.unknown(node, DependencyRefusalKind::ResolutionError, site);
        };
        match constant {
            // A type-level constant is a valtree: no provenance, no callable.
            mir::Const::Ty(..) => {}
            mir::Const::Unevaluated(unevaluated, _) => match unevaluated.promoted {
                Some(promoted) => {
                    let args = self.tcx.erase_and_anonymize_regions(unevaluated.args);
                    let key = Key::Promoted {
                        def: unevaluated.def,
                        args,
                        promoted,
                        env: Self::env_of(frame.env, args),
                    };
                    let target = self.node(key);
                    self.graph.add_edge(node, target, EdgeClass::Read, site, false);
                }
                None => self.read_value(frame, unevaluated.def, unevaluated.args, site),
            },
            mir::Const::Val(value, ty) => self.const_value(node, value, ty, site),
        }
    }

    /// A read of a `const` / `static` / thread-local: READ its value node. A
    /// trait associated const is the impl const it resolves to.
    fn read_value(
        &mut self,
        frame: &Frame<'tcx>,
        def: DefId,
        args: GenericArgs<'tcx>,
        site: ReachSite,
    ) {
        let tcx = self.tcx;
        let node = frame.node;
        let (def, args) = if tcx.trait_of_assoc(def).is_some() {
            match ty::Instance::try_resolve(tcx, frame.typing_env, def, args) {
                Ok(Some(instance)) => (instance.def_id(), instance.args),
                Ok(None) if args.has_param() || args.has_aliases() => {
                    return self.param(node, site);
                }
                Ok(None) | Err(_) => {
                    return self.unknown(node, DependencyRefusalKind::ResolutionError, site);
                }
            }
        } else {
            (def, args)
        };
        let args = tcx.erase_and_anonymize_regions(args);
        if self.too_deep(args) {
            return self.unknown(node, DependencyRefusalKind::Widened, site);
        }
        let target = self.node(Key::Value { def, args, env: Self::env_of(frame.env, args) });
        self.graph.add_edge(node, target, EdgeClass::Read, site, false);
        // A thread-local reference, a TLS shim or a `sym` operand names a
        // static as a constant's provenance does (`allocations`).
        if matches!(tcx.def_kind(def), DefKind::Static { .. }) {
            self.touch_static(node, def);
        }
    }

    /// A constant `value` of type `ty`: what its provenance holds
    /// ([`Self::allocations`]), each allocation typed by how the value
    /// reaches it (route C).
    fn const_value(
        &mut self,
        node: ReachNode,
        value: mir::ConstValue,
        ty: Ty<'tcx>,
        site: ReachSite,
    ) {
        let roots = match value {
            mir::ConstValue::Scalar(Scalar::Ptr(pointer, _)) => {
                let (provenance, offset) = pointer.into_raw_parts();
                vec![(provenance.alloc_id(), self.value_typing(ty, offset.bytes()))]
            }
            mir::ConstValue::Slice { alloc_id, .. } => {
                let typing = match ty.builtin_deref(true).map(|pointee| *pointee.kind()) {
                    Some(ty::Slice(element)) => Typing::Elements(element, 0),
                    Some(ty::Str) => Typing::Elements(self.tcx.types.u8, 0),
                    _ => Typing::Untyped,
                };
                vec![(alloc_id, typing)]
            }
            mir::ConstValue::Indirect { alloc_id, offset } => {
                vec![(alloc_id, Typing::At(ty, offset.bytes()))]
            }
            mir::ConstValue::Scalar(Scalar::Int(_)) | mir::ConstValue::ZeroSized => Vec::new(),
        };
        self.allocations(node, roots, site);
    }

    /// What an allocation's provenance holds, recursively: a fn pointer is a
    /// CREATE, a vtable CREATEs its slots, a pointer to a static READs it.
    ///
    /// Route C (design §10, "typed LAUNDER"): a fn pointer at a position its
    /// allocation's type does not spell as a fn pointer of a matching shape
    /// (`static S: [MaybeUninit<u8>; 8] = transmute(launch as fn())`, a
    /// union's bytes, a raw pointer's target, anything reached untyped) is a
    /// callable in data: a LAUNDER keyed by its shape. A fn pointer at a
    /// position of a matching shape but another fn-pointer type is called at
    /// that type (route S, [`Self::signature_positions`]). Const evaluation
    /// validates a value at its type, so provenance sits only at pointer
    /// positions or in bytes no type names (a union's, behind a raw pointer).
    /// Memory a pointer reaches is read again at that pointer's typing, a
    /// static's included: a static is typed by its own type where its own
    /// walk reads it, and by every pointer that reaches it.
    fn allocations(
        &mut self,
        node: ReachNode,
        roots: Vec<(AllocId, Typing<'tcx>)>,
        site: ReachSite,
    ) {
        let tcx = self.tcx;
        // `true`: the allocation's provenance is this node's (CREATE, READ);
        // `false`: only its typing is checked (a static's bytes, which the
        // static's own node holds).
        let mut stack: Vec<(AllocId, Typing<'tcx>, bool)> =
            roots.into_iter().map(|(alloc_id, typing)| (alloc_id, typing, true)).collect();
        let mut seen: FxHashSet<AllocId> = FxHashSet::default();
        let mut checked: FxHashSet<(AllocId, Typing<'tcx>, bool)> = FxHashSet::default();
        while let Some((alloc_id, typing, edges)) = stack.pop() {
            if !checked.insert((alloc_id, typing.clone(), edges)) {
                continue;
            }
            let first = edges && seen.insert(alloc_id);
            let mut children = Vec::new();
            match tcx.try_get_global_alloc(alloc_id) {
                Some(GlobalAlloc::Function { instance }) => {
                    let shape = self.instance_shape(instance);
                    let kept = match &typing {
                        Typing::Fn(held) => self.fn_shape(held.fn_sig(tcx)).matches(&shape),
                        Typing::Unchecked => true,
                        Typing::Untyped | Typing::At(..) | Typing::Elements(..) => false,
                    };
                    if !kept {
                        let launder_shape = self.launder_shape(instance, &shape);
                        self.constant_launder(node, &launder_shape, instance, site);
                    } else if let Typing::Fn(held) = &typing {
                        self.constant_signature(node, instance, *held, &shape, site);
                    }
                    if first {
                        match self.member(instance, None) {
                            Ok(member) => {
                                self.create(node, member, PoolKey::Fn(shape), false, site)
                            }
                            Err(reason) => self.unknown(node, reason, site),
                        }
                    }
                }
                Some(GlobalAlloc::VTable(concrete, predicates)) => {
                    if first {
                        self.vtable(node, concrete, predicates, site, true, false)
                    }
                }
                Some(GlobalAlloc::Static(def)) => {
                    if first {
                        let target = self.node(Key::Value {
                            def,
                            args: ty::GenericArgs::empty(),
                            env: None,
                        });
                        self.graph.add_edge(node, target, EdgeClass::Read, site, false);
                        self.touch_static(node, def);
                    }
                    // A static's bytes are typed by every pointer that reaches
                    // them. A nested static (memory const evaluation interned
                    // out of a static's initializer) has no type of its own and
                    // no node that holds it: what it holds is this node's. Any
                    // other static's node holds what it holds, and its own walk
                    // reads it at its own type; here it is only read again. A
                    // foreign static has no initializer here (R3).
                    if typing != Typing::Unchecked && !tcx.is_foreign_item(def) {
                        let nested =
                            matches!(tcx.def_kind(def), DefKind::Static { nested: true, .. });
                        if let Ok(allocation) = tcx.eval_static_initializer(def) {
                            let mut held = Vec::new();
                            self.allocation_provenance(allocation.inner(), &typing, &mut held);
                            let edges = edges && nested;
                            children
                                .extend(held.into_iter().map(|(id, typing)| (id, typing, edges)));
                        }
                    }
                }
                Some(GlobalAlloc::Memory(allocation)) => {
                    let mut held = Vec::new();
                    self.allocation_provenance(allocation.inner(), &typing, &mut held);
                    children.extend(held.into_iter().map(|(id, typing)| (id, typing, edges)));
                }
                Some(GlobalAlloc::TypeId { .. }) => {}
                None => {
                    if first {
                        self.unknown(node, DependencyRefusalKind::ResolutionError, site)
                    }
                }
            }
            stack.extend(children);
        }
    }

    /// Route S in constant memory: `instance`'s fn pointer sits at a position
    /// of the fn-pointer type `held`, whose shape matches its own, and is
    /// called at `held` (`static G: fn(&mut usize) =
    /// transmute::<fn(&mut Option<fn()>), _>(put)`): its arguments and return
    /// value are read at the other's types. An instance whose fn-pointer type
    /// the census cannot state is laundered by its shape.
    fn constant_signature(
        &mut self,
        node: ReachNode,
        instance: Instance<'tcx>,
        held: Ty<'tcx>,
        shape: &FnShape,
        site: ReachSite,
    ) {
        let Some(own) = self.instance_fn_ptr(instance) else {
            let launder_shape = self.launder_shape(instance, shape);
            return self.constant_launder(node, &launder_shape, instance, site);
        };
        let typing_env = ty::TypingEnv::fully_monomorphized();
        let held = self.tcx.erase_and_anonymize_regions(held);
        if own == held {
            return;
        }
        let mut keys = FxIndexSet::default();
        self.views(vec![(own, held)], true, typing_env, &mut keys);
        if keys.is_empty() {
            return;
        }
        let what = self.debug.then(|| {
            let at = self.describe_node(node);
            rustc_middle::ty::print::with_no_trimmed_paths!(format!(
                "{at} (constant bytes hold `{instance}` as `{held}`)"
            ))
        });
        let keys = Rc::new(keys.into_iter().collect());
        self.deferred_launders.entry((keys, typing_env)).or_insert((site, node, what));
    }

    /// The fn-pointer type `instance` is reified to, regions erased: an
    /// item's signature, a closure's (its `call_once` shim), or `None`.
    fn instance_fn_ptr(&self, instance: Instance<'tcx>) -> Option<Ty<'tcx>> {
        let tcx = self.tcx;
        let def = instance.def_id();
        let sig = if let InstanceKind::Shim(ShimKind::ClosureOnce { .. }) = instance.def {
            let ty::Closure(_, args) = *instance.args.types().next()?.kind() else { return None };
            tcx.signature_unclosure(args.as_closure().sig(), rustc_hir::Safety::Safe)
        } else if tcx.is_closure_like(def) {
            let ty::Closure(..) = tcx.type_of(def).skip_binder().kind() else { return None };
            tcx.signature_unclosure(instance.args.as_closure().sig(), rustc_hir::Safety::Safe)
        } else {
            match instance.def {
                InstanceKind::Item(def) | InstanceKind::Shim(ShimKind::Reify(def, _))
                    if matches!(tcx.def_kind(def), DefKind::Fn | DefKind::AssocFn) =>
                {
                    tcx.fn_sig(def).instantiate(tcx, instance.args).skip_norm_wip()
                }
                _ => return None,
            }
        };
        Some(tcx.erase_and_anonymize_regions(Ty::new_fn_ptr(tcx, sig)))
    }

    /// The key a LAUNDER of `instance`'s fn pointer records: its pool key's
    /// shape, or, for a closure's `call_once` shim (reified closures, filed
    /// unclassified), the closure's signature, which admits that member (an
    /// unclassified class matches every class) without admitting every
    /// callable.
    fn launder_shape(&self, instance: Instance<'tcx>, shape: &FnShape) -> FnShape {
        if let InstanceKind::Shim(ShimKind::ClosureOnce { .. }) = instance.def {
            if let Some(ty::Closure(_, args)) = instance.args.types().next().map(|ty| *ty.kind()) {
                let sig = args.as_closure().sig();
                return self.fn_shape(self.tcx.signature_unclosure(sig, rustc_hir::Safety::Safe));
            }
        }
        shape.clone()
    }

    /// Route C: `instance`'s fn pointer sits in constant memory at a position
    /// that does not keep it as a fn pointer of its shape.
    fn constant_launder(
        &mut self,
        node: ReachNode,
        shape: &FnShape,
        instance: Instance<'tcx>,
        site: ReachSite,
    ) {
        let keys = Rc::new(vec![LaunderKey::Key(CarriedKey::Key(PoolKey::Fn(shape.clone())))]);
        let what = self.debug.then(|| {
            let at = self.describe_node(node);
            rustc_middle::ty::print::with_no_trimmed_paths!(format!(
                "{at} (constant bytes hold `{instance}` as data)"
            ))
        });
        self.deferred_launders
            .entry((keys, ty::TypingEnv::fully_monomorphized()))
            .or_insert((site, node, what));
    }

    /// Push each pointer `allocation` holds with how `typing` types its
    /// position ([`Self::allocations`]).
    fn allocation_provenance(
        &mut self,
        allocation: &Allocation,
        typing: &Typing<'tcx>,
        stack: &mut Vec<(AllocId, Typing<'tcx>)>,
    ) {
        let size = allocation.size().bytes();
        let slots = match typing {
            Typing::At(ty, base) => self.slots(*ty, *base, None),
            Typing::Elements(ty, base) => self.slots(*ty, *base, Some(size)),
            Typing::Untyped | Typing::Fn(_) | Typing::Unchecked => None,
        };
        let pointer = self.tcx.data_layout.pointer_size().bytes();
        let endian = self.tcx.data_layout.endian;
        for &(offset, provenance) in allocation.provenance().ptrs().iter() {
            let offset = offset.bytes();
            let child = match (typing, slots.as_ref().and_then(|slots| slots.get(offset))) {
                (Typing::Unchecked, _) => Typing::Unchecked,
                (_, Some(Slot::Fn(held))) => Typing::Fn(*held),
                (_, Some(Slot::Ptr(pointee))) => {
                    // The pointer's offset into its target, as its bytes store it.
                    let end = (offset + pointer).min(size);
                    let bytes = allocation.inspect_with_uninit_and_ptr_outside_interpreter(
                        offset as usize..end as usize,
                    );
                    match read_target_uint(endian, bytes) {
                        // A `dyn` pointer's target is the concrete type its
                        // vtable names (const evaluation validates a `dyn`
                        // pointee at its vtable's type).
                        Ok(into) if pointee.is_trait() => {
                            let vtable = allocation
                                .provenance()
                                .ptrs()
                                .get(&rustc_abi::Size::from_bytes(offset + pointer))
                                .map(|metadata| self.tcx.try_get_global_alloc(metadata.alloc_id()));
                            match vtable {
                                Some(Some(GlobalAlloc::VTable(concrete, _)))
                                    if concrete.is_sized(
                                        self.tcx,
                                        ty::TypingEnv::fully_monomorphized(),
                                    ) =>
                                {
                                    Typing::At(concrete, into as u64)
                                }
                                _ => Typing::Untyped,
                            }
                        }
                        Ok(into) => self.pointee_typing(*pointee, into as u64),
                        Err(_) => Typing::Untyped,
                    }
                }
                _ => Typing::Untyped,
            };
            stack.push((provenance.alloc_id(), child));
        }
    }

    /// How a reference to `pointee` at `offset` into its target types it.
    fn pointee_typing(&self, pointee: Ty<'tcx>, offset: u64) -> Typing<'tcx> {
        match *pointee.kind() {
            ty::Slice(element) => Typing::Elements(element, offset),
            ty::Str => Typing::Elements(self.tcx.types.u8, offset),
            ty::Dynamic(..) => Typing::Untyped,
            _ if pointee.is_sized(self.tcx, ty::TypingEnv::fully_monomorphized()) => {
                Typing::At(pointee, offset)
            }
            _ => Typing::Untyped,
        }
    }

    /// How a constant scalar of type `ty`, a pointer `offset` into its
    /// target, types that target.
    fn value_typing(&mut self, ty: Ty<'tcx>, offset: u64) -> Typing<'tcx> {
        match self.slots(ty, 0, None).as_ref().and_then(|slots| slots.get(0)) {
            Some(Slot::Fn(held)) => Typing::Fn(*held),
            Some(Slot::Ptr(pointee)) => self.pointee_typing(*pointee, offset),
            _ => Typing::Untyped,
        }
    }

    /// The pointer positions of a value of `ty` laid out at `base` (route C),
    /// or of values of `ty` repeated from `base` to `until`; `None` when the
    /// layout is unknown or too large to enumerate.
    fn slots(&mut self, ty: Ty<'tcx>, base: u64, until: Option<u64>) -> Option<Slots<'tcx>> {
        let typing_env = ty::TypingEnv::fully_monomorphized();
        let tcx = self.tcx;
        let ty = tcx.erase_and_anonymize_regions(ty);
        if ty.has_param() || ty.has_aliases() {
            return None;
        }
        let layout = tcx.layout_of(typing_env.as_query_input(ty)).ok()?;
        let cx = LayoutCx::new(tcx, typing_env);
        let mut slots = Slots::default();
        let mut budget = LAUNDER_BUDGET * 16;
        match until {
            None => self.layout_slots(&cx, layout, base, &mut slots, &mut budget)?,
            Some(end) => {
                let stride = layout.size.bytes();
                if stride > 0 && !self.pointer_free(ty) {
                    let mut at = base;
                    while at + stride <= end {
                        self.layout_slots(&cx, layout, at, &mut slots, &mut budget)?;
                        at += stride;
                    }
                }
            }
        }
        Some(slots)
    }

    /// Whether a value of `ty` holds no pointer, fn pointer or union bytes.
    fn pointer_free(&mut self, ty: Ty<'tcx>) -> bool {
        let own = self.own_bytes(ty, ty::TypingEnv::fully_monomorphized());
        own.callables.is_empty()
            && own.pointees.is_empty()
            && own.objects.is_empty()
            && !own.untyped
            && !own.param
    }

    fn layout_slots(
        &mut self,
        cx: &LayoutCx<'tcx>,
        layout: TyAndLayout<'tcx>,
        base: u64,
        slots: &mut Slots<'tcx>,
        budget: &mut usize,
    ) -> Option<()> {
        *budget = budget.checked_sub(1)?;
        match *layout.ty.kind() {
            ty::FnPtr(..) => {
                slots.insert(base, Slot::Fn(layout.ty));
                return Some(());
            }
            ty::Ref(_, pointee, _) | ty::RawPtr(pointee, _) => {
                slots.insert(base, Slot::Ptr(pointee));
                return Some(());
            }
            // SC-7d: a state-guarded sysroot union is read only as the field
            // last written, so each field's positions type its bytes; any
            // other union's bytes are typed by none of them.
            ty::Adt(adt, _) if adt.is_union() => {
                if self.state_guarded_union(adt.did()) {
                    for index in 0..layout.fields.count() {
                        let field = layout.field(cx, index);
                        let offset = base + layout.fields.offset(index).bytes();
                        self.layout_slots(cx, field, offset, slots, budget)?;
                    }
                } else {
                    slots.opaque.push((base, base + layout.size.bytes()));
                }
                return Some(());
            }
            _ => {}
        }
        if layout.size.bytes() == 0 || self.pointer_free(layout.ty) {
            return Some(());
        }
        match &layout.variants {
            Variants::Single { .. } | Variants::Empty => {
                self.fields_slots(cx, layout, base, slots, budget)?
            }
            Variants::Multiple { tag_field, variants, .. } => {
                // Every variant's fields at their offsets, and a coroutine's
                // prefix fields; never the tag, which is an integer or a niche
                // inside a variant's field (`Option<fn()>`'s is the fn
                // pointer itself).
                for index in 0..layout.fields.count() {
                    if index == tag_field.as_usize() {
                        continue;
                    }
                    let field = layout.field(cx, index);
                    let offset = base + layout.fields.offset(index).bytes();
                    self.layout_slots(cx, field, offset, slots, budget)?;
                }
                for index in variants.indices() {
                    let variant = layout.for_variant(cx, index);
                    self.fields_slots(cx, variant, base, slots, budget)?;
                }
            }
        }
        Some(())
    }

    fn fields_slots(
        &mut self,
        cx: &LayoutCx<'tcx>,
        layout: TyAndLayout<'tcx>,
        base: u64,
        slots: &mut Slots<'tcx>,
        budget: &mut usize,
    ) -> Option<()> {
        match &layout.fields {
            FieldsShape::Primitive => {}
            FieldsShape::Union(_) => slots.opaque.push((base, base + layout.size.bytes())),
            FieldsShape::Array { stride, count } => {
                if *count == 0 {
                    return Some(());
                }
                let element = layout.field(cx, 0);
                if self.pointer_free(element.ty) {
                    return Some(());
                }
                for index in 0..*count {
                    self.layout_slots(cx, element, base + index * stride.bytes(), slots, budget)?;
                }
            }
            FieldsShape::Arbitrary { .. } => {
                for index in 0..layout.fields.count() {
                    let field = layout.field(cx, index);
                    let offset = base + layout.fields.offset(index).bytes();
                    self.layout_slots(cx, field, offset, slots, budget)?;
                }
            }
        }
        Some(())
    }

    // ----- drops and clones -------------------------------------------------------------------

    fn drop_node(
        &mut self,
        ty: Ty<'tcx>,
        env: Option<DefId>,
    ) -> Result<ReachNode, DependencyRefusalKind> {
        let ty = self.tcx.erase_and_anonymize_regions(ty);
        self.cut = false;
        if self.depth(ty) > self.limit {
            self.cut = true;
            return Err(DependencyRefusalKind::Widened);
        }
        let env = Self::env_of(env, ty);
        if ty.has_param() && env.is_none() {
            return Err(DependencyRefusalKind::ResolutionError);
        }
        Ok(self.node(Key::Drop { ty, env }))
    }

    fn clone_node(
        &mut self,
        ty: Ty<'tcx>,
        env: Option<DefId>,
    ) -> Result<ReachNode, DependencyRefusalKind> {
        let ty = self.tcx.erase_and_anonymize_regions(ty);
        self.cut = false;
        if self.depth(ty) > self.limit {
            self.cut = true;
            return Err(DependencyRefusalKind::Widened);
        }
        let env = Self::env_of(env, ty);
        if ty.has_param() && env.is_none() {
            return Err(DependencyRefusalKind::ResolutionError);
        }
        Ok(self.node(Key::Clone { ty, env }))
    }

    /// A MIR `Drop` of a value of type `ty` (S3 when its glue reaches a spawn).
    fn drop(&mut self, frame: &Frame<'tcx>, ty: Ty<'tcx>, async_drop: bool, site: ReachSite) {
        if frame.mode == Mode::Const {
            // Compile-time drops run no code at run time.
            return;
        }
        let node = frame.node;
        if async_drop {
            return self.unknown(node, DependencyRefusalKind::AsyncDropShim, site);
        }
        let Some(ty) = self.mono(frame, ty) else {
            return self.unknown(node, DependencyRefusalKind::ResolutionError, site);
        };
        self.drop_edge(node, ty, frame.env, frame.typing_env, site);
        self.drop_handoff(frame, ty, site);
    }

    /// Rule H for a drop (design §5.4, confinement): a local frame dropping a
    /// value hands it to the drop glue, which may invoke a callable the value
    /// carries (an external guard whose `Drop` calls its `&mut dyn FnMut`).
    /// The RUN edge to the glue reaches every member the glue's invokes see,
    /// and those never include a confined one, so the frame is charged as at
    /// a call: with every key the glue's closure invokes that the value may
    /// carry. Only values that may carry a `dyn` value count: confinement is
    /// of vtables only.
    fn drop_handoff(&mut self, frame: &Frame<'tcx>, ty: Ty<'tcx>, site: ReachSite) {
        if frame.locality != Locality::Local
            || frame.mode != Mode::Run
            || self.depth(ty) > self.limit
            || !census_needs_drop(self.tcx, frame.typing_env, ty)
        {
            return;
        }
        let carried: Vec<CarriedKey> = self
            .carried(ty, frame.typing_env)
            .iter()
            .filter(|key| match key {
                CarriedKey::Principal(_) | CarriedKey::AnyDyn | CarriedKey::Any => true,
                CarriedKey::Key(key) => key.principal().is_some(),
                CarriedKey::AnyFn | CarriedKey::Untyped | CarriedKey::Laundered => false,
            })
            .cloned()
            .collect();
        if carried.is_empty() {
            return;
        }
        let Ok(glue) = self.drop_node(ty, frame.env) else { return };
        self.deferred_drop_handoffs.push((frame.node, glue, carried, site));
    }

    /// A RUN of the drop glue of `ty` from `node`, when `ty` needs one.
    fn drop_edge(
        &mut self,
        node: ReachNode,
        ty: Ty<'tcx>,
        env: Option<DefId>,
        typing_env: ty::TypingEnv<'tcx>,
        site: ReachSite,
    ) {
        // (A type past the limits is refused before rustc is asked about it.)
        if self.depth(ty) > self.limit {
            self.cut = true;
            return self.unknown(node, DependencyRefusalKind::Widened, site);
        }
        if !census_needs_drop(self.tcx, typing_env, ty) {
            return;
        }
        match self.drop_node(ty, env) {
            Ok(glue) => self.graph.add_edge(node, glue, EdgeClass::Run, site, true),
            Err(reason) => self.unknown(node, reason, site),
        }
    }

    /// Drop glue, decomposed structurally (design §5.3, Drops).
    fn walk_drop(&mut self, node: ReachNode, ty: Ty<'tcx>, env: Option<DefId>) {
        let tcx = self.tcx;
        let frame = self.bare_frame(node, env, Locality::External);
        let site = self.internal;
        // The glue drops each component through a pointer to it, which for a
        // field (not an element, nor what a box owns) views `ty` (route F).
        let component = |walker: &mut Self, component: Ty<'tcx>, field: bool| {
            let component = normalize(tcx, frame.typing_env, component).unwrap_or(component);
            if census_needs_drop(tcx, frame.typing_env, component) {
                if field {
                    walker.field_view(&frame, ty, component, site);
                }
                match walker.drop_node(component, env) {
                    Ok(glue) => walker.graph.add_edge(node, glue, EdgeClass::Run, site, true),
                    Err(reason) => walker.unknown(node, reason, site),
                }
            }
        };
        match *ty.kind() {
            ty::Adt(adt, args) => {
                if adt.is_manually_drop() {
                    return;
                }
                if adt.has_dtor(tcx) {
                    // `<T as Drop>::drop`, then the fields.
                    let drop_fn = tcx.lang_items().get(LangItem::Drop).and_then(|drop_trait| {
                        tcx.associated_item_def_ids(drop_trait).first().copied()
                    });
                    match drop_fn.map(|drop_fn| {
                        ty::Instance::try_resolve(
                            tcx,
                            frame.typing_env,
                            drop_fn,
                            tcx.mk_args(&[ty.into()]),
                        )
                    }) {
                        Some(Ok(Some(instance))) => {
                            self.run_instance(&frame, instance, &[], site, true)
                        }
                        Some(Ok(None)) if ty.has_param() || ty.has_aliases() => {
                            self.param(node, site)
                        }
                        _ => self.unknown(node, DependencyRefusalKind::ResolutionError, site),
                    }
                }
                if let Some(content) = ty.boxed_ty() {
                    // The box drops what it owns before its own `Drop` frees it.
                    component(self, content, false);
                }
                if !adt.is_union() {
                    for field in adt.all_fields() {
                        component(self, field.ty(tcx, args).skip_norm_wip(), true);
                    }
                }
            }
            ty::Tuple(elements) => {
                for element in elements {
                    component(self, element, true);
                }
            }
            ty::Array(element, _) | ty::Slice(element) | ty::Pat(element, _) => {
                component(self, element, false)
            }
            ty::Closure(_, args) => {
                for upvar in args.as_closure().upvar_tys() {
                    component(self, upvar, true);
                }
            }
            ty::CoroutineClosure(_, args) => {
                for upvar in args.as_coroutine_closure().upvar_tys() {
                    component(self, upvar, true);
                }
            }
            ty::Coroutine(def, args) => self.walk_coroutine_drop(&frame, def, args),
            ty::Dynamic(predicates, ..) => {
                let key = PoolKey::DynDrop(self.principal_key(predicates));
                self.invoke(node, key, Vec::new(), site, true);
            }
            ty::Param(_) | ty::Alias(..) => self.param(node, site),
            ty::UnsafeBinder(_)
            | ty::CoroutineWitness(..)
            | ty::Error(_)
            | ty::Infer(_)
            | ty::Placeholder(_)
            | ty::Bound(..) => self.unknown(node, DependencyRefusalKind::ResolutionError, site),
            ty::Bool
            | ty::Char
            | ty::Int(_)
            | ty::Uint(_)
            | ty::Float(_)
            | ty::Str
            | ty::Foreign(_)
            | ty::RawPtr(..)
            | ty::Ref(..)
            | ty::FnDef(..)
            | ty::FnPtr(..)
            | ty::Never => {}
        }
    }

    /// A coroutine's drop runs its `coroutine_drop` body.
    fn walk_coroutine_drop(&mut self, frame: &Frame<'tcx>, def: DefId, args: GenericArgs<'tcx>) {
        let tcx = self.tcx;
        let site = self.internal;
        let frame =
            Frame { instance: Some(Instance { def: InstanceKind::Item(def), args }), ..*frame };
        let mut found = false;
        if let Some(local) = def.as_local() {
            let hooks = self.hooks;
            hooks.with_local_body(local, &mut |body| {
                if let Some(drop_body) = body.coroutine_drop() {
                    found = true;
                    self.visit(&frame, drop_body);
                }
            });
        } else if tcx.is_mir_available(def) {
            if let Some(drop_body) = tcx.optimized_mir(def).coroutine_drop() {
                found = true;
                self.visit(&frame, drop_body);
            }
        }
        if !found {
            self.unknown(frame.node, DependencyRefusalKind::ResolutionError, site);
        }
    }

    /// The compiler's `Clone` shim: per-component `Clone::clone`.
    fn walk_clone(&mut self, node: ReachNode, ty: Ty<'tcx>, env: Option<DefId>) {
        let tcx = self.tcx;
        let frame = self.bare_frame(node, env, Locality::External);
        let site = self.internal;
        let components: Vec<Ty<'tcx>> = match *ty.kind() {
            ty::Tuple(elements) => elements.to_vec(),
            ty::Array(element, _) => vec![element],
            ty::Closure(_, args) => args.as_closure().upvar_tys().to_vec(),
            ty::CoroutineClosure(_, args) => args.as_coroutine_closure().upvar_tys().to_vec(),
            ty::Coroutine(..) => {
                return self.unknown(node, DependencyRefusalKind::CoroutineClone, site);
            }
            ty::Param(_) | ty::Alias(..) => return self.param(node, site),
            _ => Vec::new(),
        };
        let Some(clone_fn) = tcx.lang_items().get(LangItem::CloneFn) else {
            return self.unknown(node, DependencyRefusalKind::ResolutionError, site);
        };
        for component in components {
            match ty::Instance::try_resolve(
                tcx,
                frame.typing_env,
                clone_fn,
                tcx.mk_args(&[component.into()]),
            ) {
                Ok(Some(instance)) => self.run_instance(&frame, instance, &[], site, false),
                Ok(None) if component.has_param() || component.has_aliases() => {
                    self.param(node, site)
                }
                Ok(None) | Err(_) => {
                    self.unknown(node, DependencyRefusalKind::ResolutionError, site)
                }
            }
        }
    }

    // ----- pool keys ----------------------------------------------------------------------------

    fn def_hash(&self, def: DefId) -> u64 {
        self.tcx.def_path_hash(def).0.to_smaller_hash().as_u64()
    }

    /// A `dyn` principal: the principal trait with its generic arguments
    /// (every region erased, so subtyping between binders never splits a
    /// pool). Neither the projection bounds nor the AUTO TRAITS are part of
    /// the key: a vtable is the same whatever auto traits its `dyn` type
    /// lists, and valid Rust changes them with no unsizing coercion the census
    /// could record as an upcast (a transmute or a union pun of
    /// `Box<dyn FnOnce() + 'a>` to `Box<dyn FnOnce() + Send + 'static>`, which
    /// Miri accepts: it does not validate a vtable's auto traits), so keys that
    /// split them would leave the call through the re-typed value a pool that
    /// cannot hold its vtable. Coarser only merges pools; upcasts join
    /// principals.
    fn principal_key(
        &self,
        predicates: &'tcx ty::List<ty::PolyExistentialPredicate<'tcx>>,
    ) -> PrincipalKey {
        if let Some(&key) = self.principal_keys.borrow().get(&predicates) {
            return key;
        }
        let tcx = self.tcx;
        let mut hasher = FxHasher::default();
        if let Some(principal) = predicates.principal() {
            let principal = tcx.instantiate_bound_regions_with_erased(principal);
            self.def_hash(principal.def_id).hash(&mut hasher);
            for arg in principal.args.iter() {
                match arg.kind() {
                    GenericArgKind::Type(ty) => tcx.type_id_hash(ty).as_u128().hash(&mut hasher),
                    GenericArgKind::Const(constant) => {
                        rustc_middle::ty::print::with_no_trimmed_paths!(format!("{constant:?}"))
                            .hash(&mut hasher)
                    }
                    GenericArgKind::Lifetime(_) => {}
                }
            }
        }
        let raw_key = hasher.finish();
        let key = PrincipalKey(raw_key);
        self.principal_keys.borrow_mut().insert(predicates, key);
        self.principals.borrow_mut().entry(raw_key).or_insert(predicates);
        key
    }

    fn fn_shape(&self, sig: ty::PolyFnSig<'tcx>) -> FnShape {
        let sig = self.tcx.instantiate_bound_regions_with_erased(sig);
        // `$X-unwind` and `$X` are one class: core's fn-pointer documentation
        // ("ABI compatibility") makes a `$X-unwind` caller of a `$X` callee
        // ABI-compatible, so a call through an `extern "C-unwind" fn()` may run
        // an `extern "C" fn()`.
        let mut abi = FxHasher::default();
        let convention = sig.abi().as_str();
        convention.strip_suffix("-unwind").unwrap_or(convention).hash(&mut abi);
        FnShape {
            abi: Some(abi.finish() as u32),
            variadic: Some(sig.c_variadic()),
            params: Some(sig.inputs().iter().map(|ty| self.arg_class(*ty)).collect()),
        }
    }

    /// The shape of the fn pointer `instance` is reified to.
    fn instance_shape(&self, instance: Instance<'tcx>) -> FnShape {
        let tcx = self.tcx;
        let def = instance.def_id();
        if tcx.is_closure_like(def) {
            if let ty::Closure(..) = tcx.type_of(def).skip_binder().kind() {
                let sig = instance.args.as_closure().sig();
                return self.fn_shape(tcx.signature_unclosure(sig, rustc_hir::Safety::Safe));
            }
            return FnShape::unclassified();
        }
        match instance.def {
            InstanceKind::Item(def) | InstanceKind::Shim(ShimKind::Reify(def, _))
                if matches!(tcx.def_kind(def), DefKind::Fn | DefKind::AssocFn) =>
            {
                self.fn_shape(tcx.fn_sig(def).instantiate(tcx, instance.args).skip_norm_wip())
            }
            _ => FnShape::unclassified(),
        }
    }

    /// The coarse ABI class of one argument (`analysis::ArgClass`). Only
    /// classes the census can establish without `layout_of` are used; every
    /// other type is `Unclassified`, which matches every class.
    fn arg_class(&self, ty: Ty<'tcx>) -> ArgClass {
        let tcx = self.tcx;
        let pointer_bits = tcx.data_layout.pointer_size().bits() as u32;
        let pointee = |pointee: Ty<'tcx>| match pointee.kind() {
            ty::Slice(_) | ty::Str => ArgClass::LengthFatPointer,
            ty::Dynamic(..) => ArgClass::VtableFatPointer,
            ty::Param(_) | ty::Alias(..) | ty::Error(_) => ArgClass::Unclassified,
            _ if pointee.has_trivial_sizedness(tcx, ty::SizedTraitKind::Sized) => {
                ArgClass::ThinPointer
            }
            // A class is no function of an environment, so `Sized` is asked
            // in the empty one, of a type with nothing left to instantiate:
            // there, a type that names a parameter may need a bound it does
            // not hold (a const parameter's type: a compiler panic). Such a
            // pointee is a class that matches every class.
            _ if pointee.has_non_region_param() => ArgClass::Unclassified,
            _ if pointee.is_sized(tcx, ty::TypingEnv::fully_monomorphized()) => {
                ArgClass::ThinPointer
            }
            _ => ArgClass::Unclassified,
        };
        match *ty.kind() {
            ty::Bool => ArgClass::Int(8),
            ty::Char => ArgClass::Int(32),
            ty::Int(int) => ArgClass::Int(int.bit_width().map_or(pointer_bits, |bits| bits as u32)),
            ty::Uint(uint) => {
                ArgClass::Int(uint.bit_width().map_or(pointer_bits, |bits| bits as u32))
            }
            ty::Float(float) => ArgClass::Float(float.bit_width() as u32),
            ty::Ref(_, inner, _) | ty::RawPtr(inner, _) => pointee(inner),
            ty::FnPtr(..) => ArgClass::ThinPointer,
            ty::Adt(..) if ty.boxed_ty().is_some() => {
                ty.boxed_ty().map_or(ArgClass::Unclassified, pointee)
            }
            _ => ArgClass::Unclassified,
        }
    }

    /// The method pool keys of a `dyn` type: each method of its principal and
    /// the principal's supertraits, filed under its principal key as
    /// [`Self::vtable_slots`] files a vtable's methods.
    fn method_keys(
        &mut self,
        predicates: &'tcx ty::List<ty::PolyExistentialPredicate<'tcx>>,
    ) -> Vec<PoolKey> {
        let tcx = self.tcx;
        let Some(principal_trait) = predicates.principal() else { return Vec::new() };
        let principal = self.principal_key(predicates);
        let trait_ref = tcx.instantiate_bound_regions_with_erased(principal_trait.map_bound(
            |principal_trait| principal_trait.with_self_ty(tcx, tcx.types.trait_object_dummy_self),
        ));
        let mut keys = Vec::new();
        for supertrait in rustc_type_ir::elaborate::supertraits(tcx, ty::Binder::dummy(trait_ref)) {
            let supertrait = tcx.instantiate_bound_regions_with_erased(supertrait);
            for &method in tcx.own_existential_vtable_entries(supertrait.def_id) {
                keys.push(PoolKey::DynMethod {
                    principal,
                    method: MethodKey(self.def_hash(method)),
                });
            }
        }
        keys
    }

    /// Rule H: what operands of these types may carry (`CarriedKey`).
    fn carried_all(
        &mut self,
        tys: &[Ty<'tcx>],
        typing_env: ty::TypingEnv<'tcx>,
    ) -> Vec<CarriedKey> {
        let mut keys: BTreeSet<CarriedKey> = BTreeSet::new();
        for &ty in tys {
            keys.extend(self.carried(ty, typing_env).iter().cloned());
        }
        keys.into_iter().collect()
    }

    /// What a value of `ty` may carry: a fn pointer its FnPool key, a `dyn`
    /// its principal, an untyped pointer or opaque value anything, plain data
    /// a callable only after a LAUNDER. A type parameter carries nothing here
    /// (R1: its concrete instances carry what it stands for).
    fn carried(&mut self, ty: Ty<'tcx>, typing_env: ty::TypingEnv<'tcx>) -> Rc<[CarriedKey]> {
        let memo = (ty, memo_env(&[ty], typing_env));
        if let Some(keys) = self.carried.get(&memo) {
            return Rc::clone(keys);
        }
        let tcx = self.tcx;
        let mut out: BTreeSet<CarriedKey> = BTreeSet::new();
        let mut entered = Entered::new();
        let mut stack = vec![(ty, Entered::ROOT)];
        let mut seen: FxHashSet<Ty<'tcx>> = FxHashSet::default();
        while let Some((ty, path)) = stack.pop() {
            if !seen.insert(ty) {
                continue;
            }
            if self.depth(ty) > self.limit {
                // Polymorphic recursion behind a reference
                // (`Option<&'static Nested<(T, T)>>`): an unbounded type
                // sequence, so the value may lead to anything.
                out.insert(CarriedKey::Any);
                continue;
            }
            let ty = match normalize(tcx, typing_env, ty) {
                Ok(ty) => ty,
                Err(()) => {
                    out.insert(CarriedKey::Any);
                    continue;
                }
            };
            match *ty.kind() {
                ty::Bool | ty::Char | ty::Int(_) | ty::Uint(_) | ty::Float(_) | ty::Str => {
                    out.insert(CarriedKey::Laundered);
                }
                ty::Never | ty::FnDef(..) => {}
                ty::FnPtr(..) => {
                    out.insert(CarriedKey::Key(PoolKey::Fn(self.fn_shape(ty.fn_sig(tcx)))));
                }
                ty::Dynamic(predicates, ..) => {
                    out.insert(CarriedKey::Principal(self.principal_key(predicates)));
                }
                // A shared reference to a trait object lets its holder call
                // the object's methods, never run its drop glue (that needs
                // `*mut`, and dropping through `&` is UB, R4): the methods'
                // keys, not the principal, which also admits the drop pool.
                ty::Ref(_, inner, ty::Mutability::Not)
                    if matches!(inner.kind(), ty::Dynamic(..)) =>
                {
                    if let ty::Dynamic(predicates, ..) = *inner.kind() {
                        out.extend(self.method_keys(predicates).into_iter().map(CarriedKey::Key));
                    }
                }
                ty::Ref(_, inner, _) | ty::RawPtr(inner, _) => {
                    let untyped = inner.is_unit()
                        || matches!(inner.kind(), ty::Foreign(_))
                        || inner
                            .ty_adt_def()
                            .is_some_and(|adt| tcx.is_lang_item(adt.did(), LangItem::CVoid));
                    if untyped {
                        // Any callable but a confined one: memory holding a
                        // confined erasure is reached through a raw pointer
                        // only after a demoting cast (`erase_lifetimes`).
                        out.insert(CarriedKey::Untyped);
                    } else {
                        stack.push((inner, path));
                    }
                }
                ty::Array(inner, _) | ty::Slice(inner) | ty::Pat(inner, _) => {
                    stack.push((inner, path))
                }
                ty::Tuple(elements) => stack.extend(elements.iter().map(|element| (element, path))),
                // A `PhantomData<T>` is the value's claim to own a `T` through
                // pointers that do not name it: `Vec<T>`, `VecDeque<T>` and
                // the hash tables keep their elements behind a `u8` pointer,
                // so the element type is only here. What a `T` carries, the
                // value leads to.
                ty::Adt(adt, args) if adt.is_phantom_data() => stack.push((args.type_at(0), path)),
                ty::Adt(adt, args) => {
                    let depth = self.depth(ty);
                    match entered.enter(&mut self.unbounded, path, adt.did(), depth) {
                        Some(below) => stack.extend(
                            adt.all_fields()
                                .map(|field| (field.ty(tcx, args).skip_norm_wip(), below)),
                        ),
                        // Polymorphic recursion ([`REENTRIES`]): the value may
                        // lead to anything.
                        None => {
                            out.insert(CarriedKey::Any);
                        }
                    }
                }
                ty::Closure(_, args) => {
                    stack.extend(args.as_closure().upvar_tys().iter().map(|upvar| (upvar, path)))
                }
                ty::CoroutineClosure(_, args) => stack.extend(
                    args.as_coroutine_closure().upvar_tys().iter().map(|upvar| (upvar, path)),
                ),
                ty::Coroutine(_, args) => {
                    // Its saved state is not enumerated here.
                    stack.extend(args.as_coroutine().upvar_tys().iter().map(|upvar| (upvar, path)));
                    out.insert(CarriedKey::Any);
                }
                ty::Foreign(_)
                | ty::UnsafeBinder(_)
                | ty::CoroutineWitness(..)
                | ty::Error(_)
                | ty::Infer(_)
                | ty::Placeholder(_)
                | ty::Bound(..) => {
                    out.insert(CarriedKey::Any);
                }
                ty::Param(_) | ty::Alias(..) => {}
            }
        }
        let keys: Rc<[CarriedKey]> = out.into_iter().collect();
        self.carried.insert(memo, Rc::clone(&keys));
        keys
    }

    // ----- typed LAUNDER (design §10) ------------------------------------------------------------

    /// What a value of `ty` holds in its OWN bytes ([`OwnBytes`]), memoized.
    fn own_bytes(&mut self, ty: Ty<'tcx>, typing_env: ty::TypingEnv<'tcx>) -> Rc<OwnBytes<'tcx>> {
        let memo = (ty, memo_env(&[ty], typing_env));
        if let Some(own) = self.own_bytes.get(&memo) {
            return own.clone();
        }
        let tcx = self.tcx;
        let mut out = OwnBytes::default();
        // `out`'s lists, each without repeats in first-seen order ([`FxIndexSet`]).
        let mut fn_ptrs: FxIndexSet<Ty<'tcx>> = FxIndexSet::default();
        let mut pointees: FxIndexSet<Ty<'tcx>> = FxIndexSet::default();
        let mut objects: FxIndexSet<PrincipalKey> = FxIndexSet::default();
        let mut phantoms: FxIndexSet<Ty<'tcx>> = FxIndexSet::default();
        let mut stack = vec![ty];
        let mut seen: FxHashSet<Ty<'tcx>> = FxHashSet::default();
        while let Some(ty) = stack.pop() {
            if !seen.insert(ty) {
                continue;
            }
            if seen.len() > LAUNDER_BUDGET {
                out.callables.insert(CarriedKey::Any);
                out.other = true;
                break;
            }
            if self.depth(ty) > self.limit {
                out.callables.insert(CarriedKey::Any);
                out.other = true;
                continue;
            }
            let Ok(ty) = normalize(tcx, typing_env, ty) else {
                out.callables.insert(CarriedKey::Any);
                out.other = true;
                continue;
            };
            match *ty.kind() {
                ty::Bool | ty::Char | ty::Int(_) | ty::Uint(_) | ty::Float(_) | ty::Str => {
                    out.other = true
                }
                ty::Never | ty::FnDef(..) => {}
                ty::FnPtr(..) => {
                    out.callables
                        .insert(CarriedKey::Key(PoolKey::Fn(self.fn_shape(ty.fn_sig(tcx)))));
                    fn_ptrs.insert(tcx.erase_and_anonymize_regions(ty));
                }
                // An address and its metadata are data: a vtable word is no
                // callable in data (SC-7c).
                ty::Ref(_, inner, _) | ty::RawPtr(inner, _) => {
                    out.other = true;
                    pointees.insert(inner);
                }
                ty::Dynamic(predicates, ..) => {
                    let principal = self.principal_key(predicates);
                    objects.insert(principal);
                }
                ty::Array(inner, _) | ty::Slice(inner) | ty::Pat(inner, _) => stack.push(inner),
                ty::Tuple(elements) => stack.extend(elements),
                ty::Adt(adt, args) if adt.is_phantom_data() => {
                    phantoms.insert(args.type_at(0));
                }
                ty::Adt(adt, _) if tcx.is_lang_item(adt.did(), LangItem::CVoid) => {
                    out.untyped = true
                }
                ty::Adt(adt, args) => {
                    if adt.is_union() {
                        out.untyped = true;
                    }
                    stack.extend(adt.all_fields().map(|field| field.ty(tcx, args).skip_norm_wip()));
                }
                ty::Closure(_, args) => stack.extend(args.as_closure().upvar_tys()),
                ty::CoroutineClosure(_, args) => {
                    stack.extend(args.as_coroutine_closure().upvar_tys())
                }
                ty::Coroutine(def, args) => {
                    stack.extend(args.as_coroutine().upvar_tys());
                    match self.coroutine_saved_tys(def, args) {
                        Some(saved) => stack.extend(saved),
                        // Its saved state cannot be read here: anything.
                        None => {
                            out.callables.insert(CarriedKey::Any);
                            out.other = true;
                        }
                    }
                }
                ty::Foreign(_) => {
                    out.other = true;
                    out.untyped = true;
                }
                ty::UnsafeBinder(_)
                | ty::CoroutineWitness(..)
                | ty::Error(_)
                | ty::Infer(_)
                | ty::Placeholder(_)
                | ty::Bound(..) => {
                    out.callables.insert(CarriedKey::Any);
                    out.other = true;
                }
                ty::Param(_) | ty::Alias(..) => out.param = true,
            }
        }
        out.fn_ptrs = fn_ptrs.into_iter().collect();
        out.pointees = pointees.into_iter().collect();
        out.objects = objects.into_iter().collect();
        out.phantoms = phantoms.into_iter().collect();
        let own = Rc::new(out);
        self.own_bytes.insert(memo, own.clone());
        own
    }

    /// The types of a coroutine's saved locals (its own bytes beside its
    /// upvars), or `None` where its layout cannot be read here: an async
    /// drop glue's, the by-move body of a by-ref coroutine-closure, a body
    /// with no MIR, a local body already stolen. A local coroutine's is the
    /// pre-steal layout TrustVerify serves (`trust_local_coroutine_layout`);
    /// with verification off, the body the census itself reads.
    fn coroutine_saved_tys(&self, def: DefId, args: GenericArgs<'tcx>) -> Option<Vec<Ty<'tcx>>> {
        let tcx = self.tcx;
        if tcx.is_async_drop_in_place_coroutine(def) {
            return None;
        }
        let kind = args.as_coroutine().kind_ty();
        if !kind.is_unit() {
            let ty::Coroutine(_, identity) =
                *tcx.type_of(def).instantiate_identity().skip_norm_wip().kind()
            else {
                return None;
            };
            if identity.as_coroutine().kind_ty() != kind {
                return None;
            }
        }
        let read = |layout: &mir::CoroutineLayout<'tcx>| -> Vec<Ty<'tcx>> {
            layout
                .field_tys
                .iter()
                .map(|saved| {
                    let ty =
                        ty::EarlyBinder::bind(tcx, saved.ty).instantiate(tcx, args).skip_norm_wip();
                    tcx.erase_and_anonymize_regions(ty)
                })
                .collect()
        };
        match def.as_local() {
            Some(local) if tcx.sess.trust_verification_enabled() => {
                tcx.trust_local_coroutine_layout(local).map(read)
            }
            Some(local) => {
                let elaborated = tcx.mir_drops_elaborated_and_const_checked(local);
                if elaborated.is_stolen() {
                    return None;
                }
                elaborated.borrow().coroutine_layout_raw().map(read)
            }
            None if tcx.is_mir_available(def) => {
                tcx.optimized_mir(def).coroutine_layout_raw().map(read)
            }
            None => None,
        }
    }

    /// `ty` with what a reinterpretation cannot change stripped: each
    /// `repr(transparent)` wrapper (`ManuallyDrop`, `MaybeUninit`,
    /// `UnsafeCell`, `Cell`, `NonNull`) to its one field that is not a 1-ZST,
    /// an array or slice to its element, `str` to `u8`, and a `dyn` type to
    /// its principal (auto traits ignored). Two views whose types peel alike
    /// reinterpret nothing.
    fn peel(&mut self, ty: Ty<'tcx>, typing_env: ty::TypingEnv<'tcx>) -> Peeled<'tcx> {
        let tcx = self.tcx;
        let mut ty = ty;
        for _ in 0..=self.limit {
            ty = normalize(tcx, typing_env, ty).unwrap_or(ty);
            match *ty.kind() {
                ty::Array(inner, _) | ty::Slice(inner) | ty::Pat(inner, _) => ty = inner,
                ty::Str => return Peeled::Ty(tcx.types.u8),
                ty::Dynamic(predicates, ..) => {
                    return Peeled::Dyn(self.principal_key(predicates));
                }
                ty::Adt(adt, args) if adt.repr().transparent() => {
                    let mut wide = adt
                        .all_fields()
                        .map(|field| field.ty(tcx, args).skip_norm_wip())
                        .filter(|field| {
                            !tcx.layout_of(typing_env.as_query_input(*field))
                                .is_ok_and(|layout| layout.is_1zst())
                        });
                    match (wide.next(), wide.next()) {
                        (Some(field), None) => ty = field,
                        _ => return Peeled::Ty(ty),
                    }
                }
                _ => return Peeled::Ty(ty),
            }
        }
        Peeled::Ty(ty)
    }

    /// The keys of memory read through two views, for each pair `(a, b)`:
    /// the callables either holds in its own bytes that the other may read as
    /// something else ([`reinterpret`]); a `dyn` side's concrete objects
    /// viewed as the other (resolved at [`Self::emit_pool_facts`]); when one
    /// side keeps no pointee type ([`OwnBytes::untyped_view`]), everything
    /// behind the other's pointers; and the same for every pair of their
    /// pointees, since memory written through either view is read through
    /// the other (RawVec and the hash tables derive their `*mut T` from a
    /// `*mut u8`). `values`: the pairs are values sharing bytes (a union's
    /// fields, a reshaped fn pointer's arguments), so a side with no bytes
    /// reinterprets nothing. Bounded by the visited pairs and
    /// [`LAUNDER_BUDGET`], past which the pun is a LAUNDER of `Any`. `out`
    /// keeps each key once, where it was first found.
    fn views(
        &mut self,
        pairs: Vec<(Ty<'tcx>, Ty<'tcx>)>,
        values: bool,
        typing_env: ty::TypingEnv<'tcx>,
        out: &mut FxIndexSet<LaunderKey<'tcx>>,
    ) {
        let mut stack: Vec<(Ty<'tcx>, Ty<'tcx>, bool)> =
            pairs.into_iter().map(|(a, b)| (a, b, values)).collect();
        let mut visited: FxHashSet<(Ty<'tcx>, Ty<'tcx>, bool)> = FxHashSet::default();
        while let Some((a, b, values)) = stack.pop() {
            if visited.contains(&(b, a, values)) || !visited.insert((a, b, values)) {
                continue;
            }
            if visited.len() > LAUNDER_BUDGET {
                out.insert(LaunderKey::Key(CarriedKey::Any));
                return;
            }
            let (peeled_a, peeled_b) = (self.peel(a, typing_env), self.peel(b, typing_env));
            if peeled_a == peeled_b {
                continue;
            }
            // A `dyn` object read through another principal's vtable: UB (R4,
            // a forged vtable).
            if matches!((peeled_a, peeled_b), (Peeled::Dyn(_), Peeled::Dyn(_))) {
                continue;
            }
            let (own_a, own_b) = (self.own_bytes(a, typing_env), self.own_bytes(b, typing_env));
            if values && (own_a.positionless() || own_b.positionless()) {
                continue;
            }
            for key in reinterpret(&own_a, &own_b).into_iter().chain(reinterpret(&own_b, &own_a)) {
                out.insert(LaunderKey::Key(key));
            }
            for principal in &own_a.objects {
                out.insert(LaunderKey::Objects { principal: *principal, as_: b });
            }
            for principal in &own_b.objects {
                out.insert(LaunderKey::Objects { principal: *principal, as_: a });
            }
            for (own, other) in [(&own_a, &own_b), (&own_b, &own_a)] {
                if other.untyped_view() {
                    for behind in own.pointees.iter().chain(&own.phantoms) {
                        out.insert(LaunderKey::Reach(*behind));
                    }
                }
            }
            for pointee_a in &own_a.pointees {
                for pointee_b in &own_b.pointees {
                    stack.push((*pointee_a, *pointee_b, false));
                }
            }
            // S: a fn pointer one view holds, called through a fn pointer of a
            // matching shape the other holds, reads the caller's arguments at
            // its parameter types and its return value at the caller's: each
            // position is two values sharing bytes, their pointees included.
            for (callee, caller) in self.signature_positions(&own_a, &own_b) {
                stack.push((callee, caller, true));
            }
        }
    }

    /// Route S (design §10, "typed LAUNDER"): for each fn pointer `a` holds
    /// and each fn pointer of another type but a matching shape `b` holds,
    /// the pairs of their argument and return types. A call through a fn
    /// pointer of a shape its callee's does not match is UB (R4); a call
    /// through one of a matching shape is defined exactly when its argument
    /// and return types are ABI-compatible, and each reads the caller's
    /// value at the callee's type (references and raw pointers to different
    /// pointees are compatible: core's `primitive_docs`, "ABI
    /// compatibility"). Where the two fn-pointer types sit in a value does
    /// not matter: they share bytes through any transmute, union, pointer
    /// view or constant that puts one where the other is read.
    fn signature_positions(
        &mut self,
        a: &OwnBytes<'tcx>,
        b: &OwnBytes<'tcx>,
    ) -> Vec<(Ty<'tcx>, Ty<'tcx>)> {
        let tcx = self.tcx;
        let mut positions = FxIndexSet::default();
        for &callee in &a.fn_ptrs {
            for &caller in &b.fn_ptrs {
                if callee == caller {
                    continue;
                }
                let (callee_sig, caller_sig) = (callee.fn_sig(tcx), caller.fn_sig(tcx));
                if !self.fn_shape(callee_sig).matches(&self.fn_shape(caller_sig)) {
                    continue;
                }
                let callee_sig = tcx.instantiate_bound_regions_with_erased(callee_sig);
                let caller_sig = tcx.instantiate_bound_regions_with_erased(caller_sig);
                for pair in
                    callee_sig.inputs_and_output.iter().zip(caller_sig.inputs_and_output.iter())
                {
                    positions.insert(pair);
                }
            }
        }
        positions.into_iter().collect()
    }

    /// Routes P, S and A at one reinterpreting cast (design §10, "typed
    /// LAUNDER"), a LAUNDER keyed by what the reinterpreted memory may hold,
    /// deferred to [`Self::emit_pool_facts`].
    fn pun(
        &mut self,
        frame: &Frame<'tcx>,
        kind: mir::CastKind,
        source: Ty<'tcx>,
        target: Ty<'tcx>,
        site: ReachSite,
    ) {
        let exposes = kind == mir::CastKind::PointerExposeProvenance;
        let memo = (source, target, exposes, memo_env(&[source, target], frame.typing_env));
        let keys = match self.puns.get(&memo) {
            Some(keys) => keys.clone(),
            None => {
                let keys = Rc::new(self.pun_keys(source, target, exposes, frame.typing_env));
                self.puns.insert(memo, keys.clone());
                keys
            }
        };
        if !keys.is_empty() {
            self.record_launder(frame, keys, site, || format!("pun {source} -> {target}"));
        }
    }

    /// Route F (design §10, "typed LAUNDER"): a pointer to a field is a
    /// pointer to its base's memory at the field's type, with the base's
    /// provenance. A raw pointer (`&raw const (*p).n`) keeps the base pointer's
    /// provenance under every aliasing model, and a reference's covers the
    /// whole allocation under Tree Borrows, so pointer arithmetic (`add`,
    /// `slice::from_raw_parts`) reads and writes the base's other fields at
    /// the field's type, and a field of no bytes (`()`, `c_void`) is a view
    /// the next cast re-views at any type. Each `Field` projection after the
    /// place's last dereference is a pointer view of its base as the field
    /// (DECISION_QUEUE SC-7i). A coroutine's saved locals are exempt: they
    /// are distinct locals, which state transformation only lays out side by
    /// side, and so are SC-7d's unions in a sysroot body.
    fn field_puns(
        &mut self,
        frame: &Frame<'tcx>,
        body: &mir::Body<'tcx>,
        place: mir::Place<'tcx>,
        location: Location,
    ) {
        let tcx = self.tcx;
        let start = place
            .projection
            .iter()
            .rposition(|elem| matches!(elem, mir::ProjectionElem::Deref))
            .map_or(0, |deref| deref + 1);
        for (base, elem) in place.iter_projections().skip(start) {
            let mir::ProjectionElem::Field(_, field) = elem else { continue };
            let base = base.ty(body, tcx);
            match *base.ty.kind() {
                ty::Coroutine(..) if base.variant_index.is_some() => continue,
                ty::Adt(adt, _)
                    if adt.is_union()
                        && in_sysroot(tcx, body.source.def_id().krate)
                        && self.state_guarded_union(adt.did()) =>
                {
                    continue;
                }
                _ => {}
            }
            let span = body.source_info(location).span;
            let (Some(base), Some(field)) =
                (self.instance_ty(frame, base.ty, span), self.instance_ty(frame, field, span))
            else {
                continue;
            };
            let site = self.site(frame.owner, span);
            self.field_view(frame, base, field, site);
        }
    }

    /// Route F for one pointer to a `field` of `base` ([`Self::field_puns`];
    /// drop glue's pointers to the fields it drops, [`Self::walk_drop`]).
    fn field_view(
        &mut self,
        frame: &Frame<'tcx>,
        base: Ty<'tcx>,
        field: Ty<'tcx>,
        site: ReachSite,
    ) {
        let typing_env = frame.typing_env;
        let memo = (base, field, memo_env(&[base, field], typing_env));
        let keys = match self.field_views.get(&memo) {
            Some(keys) => keys.clone(),
            None => {
                let mut keys = FxIndexSet::default();
                self.views(vec![(base, field)], false, typing_env, &mut keys);
                let keys: Rc<Vec<LaunderKey<'tcx>>> = Rc::new(keys.into_iter().collect());
                self.field_views.insert(memo, keys.clone());
                keys
            }
        };
        if !keys.is_empty() {
            self.record_launder(frame, keys, site, || format!("field {base} -> {field}"));
        }
    }

    fn pun_keys(
        &mut self,
        source: Ty<'tcx>,
        target: Ty<'tcx>,
        exposes: bool,
        typing_env: ty::TypingEnv<'tcx>,
    ) -> Vec<LaunderKey<'tcx>> {
        let mut out = FxIndexSet::default();
        let (from, to) = (self.own_bytes(source, typing_env), self.own_bytes(target, typing_env));
        // P: memory reached through a pointer the source holds is read
        // through one the target holds.
        let mut pointers = Vec::new();
        for pointee in &from.pointees {
            for other in &to.pointees {
                pointers.push((*pointee, *other));
            }
        }
        self.views(pointers, false, typing_env, &mut out);
        // S: a fn pointer in the source's own bytes (by itself, or inside a
        // tuple, struct, array or `Option`) becomes one of a matching shape
        // but another type in the target's: a call through it reads the
        // caller's arguments at the callee's parameter types, and the
        // callee's return value at the caller's ([`Self::signature_positions`]).
        let positions = self.signature_positions(&from, &to);
        self.views(positions, true, typing_env, &mut out);
        // A (SC-7b): an exposed address re-enters its whole allocation, and
        // what its pointers lead to.
        if exposes {
            for pointee in &from.pointees {
                out.insert(LaunderKey::Reach(*pointee));
            }
        }
        out.into_iter().collect()
    }

    /// Route U (design §10, "typed LAUNDER"): a union's bytes are read
    /// through another field than the one that wrote them, so every pair of
    /// its fields is a reinterpretation. Recorded once per union type. SC-7d
    /// exempts the sysroot's state-guarded unions
    /// ([`SYSROOT_STATE_GUARDED_UNIONS`], `MaybeUninit`) where a sysroot body
    /// projects them; user code that puns their memory does so by a cast,
    /// which route P records with every field's bytes.
    fn union_pun(&mut self, frame: &Frame<'tcx>, body: DefId, union_ty: Ty<'tcx>, span: Span) {
        let tcx = self.tcx;
        let ty::Adt(adt, args) = *union_ty.kind() else { return };
        let memo = (union_ty, memo_env(&[union_ty], frame.typing_env));
        if !adt.is_union() || self.punned_unions.contains(&memo) {
            return;
        }
        if in_sysroot(tcx, body.krate) && self.state_guarded_union(adt.did()) {
            return;
        }
        self.punned_unions.insert(memo);
        let fields: Vec<Ty<'tcx>> =
            adt.all_fields().map(|field| field.ty(tcx, args).skip_norm_wip()).collect();
        let mut pairs = Vec::new();
        for (index, field) in fields.iter().enumerate() {
            for other in &fields[index + 1..] {
                pairs.push((*field, *other));
            }
        }
        let mut keys = FxIndexSet::default();
        self.views(pairs, true, frame.typing_env, &mut keys);
        if !keys.is_empty() {
            let site = self.site(frame.owner, span);
            let keys = Rc::new(keys.into_iter().collect());
            self.record_launder(frame, keys, site, || format!("union {union_ty}"));
        }
    }

    /// SC-7d's explicit list.
    fn state_guarded_union(&self, def: DefId) -> bool {
        let tcx = self.tcx;
        if !in_sysroot(tcx, def.krate) {
            return false;
        }
        if tcx.is_lang_item(def, LangItem::MaybeUninit) {
            return true;
        }
        if tcx.item_name(def).as_str() != "Data" {
            return false;
        }
        let path = rustc_middle::ty::print::with_no_trimmed_paths!(tcx.def_path_str(def));
        SYSROOT_STATE_GUARDED_UNIONS.contains(&path.as_str())
    }

    /// Hold a typed LAUNDER for [`Self::emit_pool_facts`]; the principals
    /// whose objects it views are named, so the sysroot scan looks them up.
    fn record_launder(
        &mut self,
        frame: &Frame<'tcx>,
        keys: Rc<Vec<LaunderKey<'tcx>>>,
        site: ReachSite,
        what: impl FnOnce() -> String,
    ) {
        for key in keys.iter() {
            if let LaunderKey::Objects { principal, .. } | LaunderKey::ReachObjects(principal) = key
            {
                self.named.insert(*principal);
                self.named_at.entry(*principal).or_insert(frame.node);
            }
        }
        let entry = (keys, frame.typing_env);
        if self.deferred_launders.contains_key(&entry) {
            return;
        }
        let what = self.debug.then(|| {
            let at = self.describe_node(frame.node);
            rustc_middle::ty::print::with_no_trimmed_paths!(format!("{at} ({})", what()))
        });
        self.deferred_launders.insert(entry, (site, frame.node, what));
    }

    /// Where a fact of `node` is, for `TRUST_SPAWN_CENSUS_DEBUG`.
    fn describe_node(&self, node: ReachNode) -> String {
        match self.node_keys.get(&node).map(|index| self.keys[*index]) {
            Some(Key::Body { def, .. } | Key::Value { def, .. } | Key::Promoted { def, .. }) => {
                rustc_middle::ty::print::with_no_trimmed_paths!(self.tcx.def_path_str(def))
            }
            Some(Key::Drop { ty, .. }) => format!("drop glue of `{ty}`"),
            Some(Key::Clone { ty, .. }) => format!("clone of `{ty}`"),
            Some(Key::Shim { instance, .. }) => format!("{instance}"),
            _ => String::from("?"),
        }
    }

    /// A concrete type a vtable of `principal` joined for.
    fn note_concrete(&mut self, principal: PrincipalKey, concrete: Ty<'tcx>) {
        self.concrete_of.entry(principal).or_default().insert(concrete);
    }

    /// The concrete types a `dyn` value of `principal` may have: those a
    /// vtable of it, or of a principal an upcast chain makes into it, joined
    /// for; `None` (anything) when it is live but none is recorded.
    fn concrete_types(
        &self,
        principal: PrincipalKey,
        live: &BTreeSet<PrincipalKey>,
    ) -> Option<Vec<Ty<'tcx>>> {
        let mut sources = BTreeSet::from([principal]);
        loop {
            let before = sources.len();
            for (from, to) in &self.upcasts {
                if sources.contains(to) {
                    sources.insert(*from);
                }
            }
            if sources.len() == before {
                break;
            }
        }
        let mut concretes: FxIndexSet<Ty<'tcx>> = FxIndexSet::default();
        for source in &sources {
            for concrete in self.concrete_of.get(source).into_iter().flatten() {
                concretes.insert(*concrete);
            }
        }
        if concretes.is_empty() && sources.iter().any(|source| live.contains(source)) {
            return None;
        }
        Some(concretes.into_iter().collect())
    }

    /// The [`CarriedKey`]s a typed LAUNDER's keys stand for, now that the
    /// concrete types are known (`name`: name each principal met, for the
    /// sysroot scan, as [`Self::run`] does between walks).
    fn resolve_launder(
        &mut self,
        keys: &[LaunderKey<'tcx>],
        typing_env: ty::TypingEnv<'tcx>,
        name: Option<ReachNode>,
        live: &BTreeSet<PrincipalKey>,
    ) -> BTreeSet<CarriedKey> {
        let mut out: BTreeSet<CarriedKey> = BTreeSet::new();
        let mut stack: Vec<LaunderKey<'tcx>> = keys.to_vec();
        let mut seen: FxHashSet<LaunderKey<'tcx>> = FxHashSet::default();
        while let Some(key) = stack.pop() {
            if !seen.insert(key.clone()) {
                continue;
            }
            if seen.len() > LAUNDER_BUDGET {
                out.insert(CarriedKey::Any);
                break;
            }
            match key {
                LaunderKey::Key(key) => {
                    out.insert(key);
                }
                LaunderKey::Objects { principal, as_ } => {
                    if let Some(node) = name {
                        self.named.insert(principal);
                        self.named_at.entry(principal).or_insert(node);
                    }
                    match self.concrete_types(principal, live) {
                        None => {
                            out.insert(CarriedKey::Any);
                        }
                        Some(concretes) => {
                            let pairs =
                                concretes.into_iter().map(|concrete| (concrete, as_)).collect();
                            let mut more = FxIndexSet::default();
                            self.views(pairs, false, typing_env, &mut more);
                            stack.extend(more);
                        }
                    }
                }
                LaunderKey::Reach(ty) => {
                    let reach = self.reach(ty, typing_env);
                    out.extend(reach.0.iter().cloned());
                    for principal in &reach.1 {
                        stack.push(LaunderKey::ReachObjects(*principal));
                    }
                }
                LaunderKey::ReachObjects(principal) => {
                    if let Some(node) = name {
                        self.named.insert(principal);
                        self.named_at.entry(principal).or_insert(node);
                    }
                    match self.concrete_types(principal, live) {
                        None => {
                            out.insert(CarriedKey::Any);
                        }
                        Some(concretes) => {
                            stack.extend(concretes.into_iter().map(LaunderKey::Reach));
                        }
                    }
                }
            }
        }
        out.remove(&CarriedKey::Laundered);
        out
    }

    /// The callables a value of `ty` holds in its own bytes or behind its
    /// pointers (and the `PhantomData`s that name what it owns behind
    /// pointers that do not), and the principals of the `dyn` objects it
    /// leads to, whose concrete objects the caller resolves. Memoized; past
    /// [`LAUNDER_BUDGET`] types, `Any`.
    fn reach(
        &mut self,
        ty: Ty<'tcx>,
        typing_env: ty::TypingEnv<'tcx>,
    ) -> Rc<(BTreeSet<CarriedKey>, BTreeSet<PrincipalKey>)> {
        let memo = (ty, memo_env(&[ty], typing_env));
        if let Some(reach) = self.reaches.get(&memo) {
            return reach.clone();
        }
        let mut keys: BTreeSet<CarriedKey> = BTreeSet::new();
        let mut principals: BTreeSet<PrincipalKey> = BTreeSet::new();
        let mut stack = vec![ty];
        let mut seen: FxHashSet<Ty<'tcx>> = FxHashSet::default();
        while let Some(ty) = stack.pop() {
            if !seen.insert(ty) {
                continue;
            }
            if seen.len() > LAUNDER_BUDGET {
                keys.insert(CarriedKey::Any);
                break;
            }
            let own = self.own_bytes(ty, typing_env);
            keys.extend(own.callables.iter().cloned());
            principals.extend(own.objects.iter().copied());
            stack.extend(own.pointees.iter().chain(&own.phantoms).copied());
        }
        let reach = Rc::new((keys, principals));
        self.reaches.insert(memo, reach.clone());
        reach
    }

    /// Name every principal a held typed LAUNDER resolves through, with the
    /// concrete types known so far ([`Self::run`]).
    fn name_launder_principals(&mut self) {
        let live = self.live_principals();
        let inputs = self.launder_inputs();
        let entries: Vec<(Rc<Vec<LaunderKey<'tcx>>>, ty::TypingEnv<'tcx>, ReachNode)> = self
            .deferred_launders
            .iter()
            .filter(|((keys, _), _)| keys.iter().any(|key| !matches!(key, LaunderKey::Key(_))))
            .map(|((keys, typing_env), (_, node, _))| (keys.clone(), *typing_env, *node))
            .collect();
        let mut settled = FxHashMap::default();
        for (keys, typing_env, node) in entries {
            let resolved = self.resolve_launder(&keys, typing_env, Some(node), &live);
            settled.insert((keys, typing_env), resolved);
        }
        // A resolution writes only `named` and `named_at`, which it never reads.
        debug_assert_eq!(inputs, self.launder_inputs());
        self.settled_launders = Some((inputs, settled));
    }

    /// What [`Self::resolve_launder`] reads besides its arguments: the
    /// concrete types each principal joined for and the upcasts
    /// ([`Self::concrete_types`]), and the minted and entering principals
    /// `live` is made of. Each only grows (inserts, never a removal), so equal
    /// counts are equal contents. Everything else a resolution reads is a
    /// compiler query or a value memoized when first computed (`own_bytes`,
    /// `reaches`, and the depth and size memos those first computations
    /// read), so under equal inputs a second resolution of the same keys
    /// retraces the first and returns its set.
    fn launder_inputs(&self) -> [usize; 4] {
        [
            self.concrete_of.values().map(FxIndexSet::len).sum(),
            self.upcasts.len(),
            self.minted.len(),
            self.entering.len(),
        ]
    }

    // ----- the answer -----------------------------------------------------------------------------

    fn finish(mut self) -> TrustSpawnCensus<'tcx> {
        let scanned = self.sysroot_creates.as_ref().map(|index| {
            (index.bodies, index.creates.values().map(Vec::len).sum::<usize>(), self.searched.len())
        });
        self.emit_pool_facts();
        let unjoined = (self.pending_creates.len(), self.pending_upcasts.len());
        let dead_invokes = self.dead_invokes;
        let upcasts_of: Vec<(PrincipalKey, PrincipalKey)> = self
            .sysroot_creates
            .as_ref()
            .map(|index| index.upcasts.iter().copied().collect())
            .unwrap_or_default();
        // A Clean-origin body (R5) is a root but is not read: it has no coverage
        // for self-audit check 2 to compare a codegen body with, its own or that
        // of a body it is inlined into.
        let unread: FxHashSet<LocalDefId> =
            self.roots.iter().copied().filter(|def| self.hooks.is_clean_origin(*def)).collect();
        if self.fault == Some(TestFault::Defect) {
            if let Some(&node) = self.nodes.values().next() {
                // TEST-ONLY: an adapter APPROX edge is a malformed fact.
                let site = self.internal;
                self.graph.add_edge(node, node, EdgeClass::Approx, site, false);
            }
        }
        let Walker {
            tcx,
            hooks,
            graph,
            keys,
            sites,
            roots,
            covered,
            sinks,
            sink_texts,
            principals,
            launder_at,
            named_at,
            entering,
            fact_owners,
            laundered_at,
            cuts,
            ..
        } = self;
        let census = graph.solve();
        let render = Render { tcx, keys: &keys, census: &census };
        // Trust (SC-8 (c), 2026-10-11; docs/DECISION_QUEUE.md "SC-8"): why the pools
        // are unclosed, named on every row the unclosed flag decides (disclosure only:
        // no verdict, row or formula changes).
        let unclosed_causes = unclosed_root_cause(
            &render,
            &principals.borrow(),
            &named_at,
            &entering,
            &sinks,
            &sink_texts,
        );
        let mut disclosed_rows = 0usize;
        let opts = &tcx.sess.opts.unstable_opts;
        let bindings = hooks.field_bindings();
        if opts.trust_send_census || opts.trust_writer_census.is_some() || !bindings.is_empty() {
            // The writer census and a binding need the threads and
            // consumers; their own notes are emitted only under
            // `-Ztrust-send-census`.
            let emit = opts.trust_send_census;
            let Sends { sent, messages, threads } = report_sends(&render, &sites, hooks, emit);
            let (consumers, unexamined) =
                report_consumers(&render, hooks, &sent, &messages, &threads, emit);
            if emit {
                report_shared(&render, &messages, &threads, &consumers);
            }
            if let Some(path) = &opts.trust_writer_census {
                report_writers(
                    &render,
                    hooks,
                    &sites,
                    &threads,
                    &consumers,
                    unexamined,
                    cuts.len(),
                    path,
                );
            }
            for binding in &bindings {
                check_binding(
                    &render, hooks, &sites, &cuts, &threads, &consumers, unexamined, binding,
                );
            }
        }
        let fallback = census.fallback().map(|fallback| format!("{fallback:?}"));
        // A fallback (a malformed fact, or a certificate the checker rejected)
        // refuses every body UNKNOWN; every row says why.
        let fallback_note = fallback.as_ref().map(|reason| {
            format!(
                " [the spawn census refused every body as UNKNOWN: its graph or certificate was \
                 rejected ({reason})]"
            )
        });
        // Every refusing row's whole witness, each edge with its class.
        let debug = spawn_census_debug_enabled();
        // A row's witness is rendered for the verifier, which reads the rows.
        // With verification off the census runs only for the send and writer
        // censuses, and rendering every refusing edge's path cost aterm-gui
        // minutes.
        let witnesses = tcx.sess.trust_verification_enabled();

        // Every row candidate is an edge out of a local body whose site that
        // body owns, with a refusing strength; per owner, only the first
        // candidate of each (span, kind) in edge order can become a row
        // ([`Candidates`]). So candidates are deduplicated by
        // (owner, span, kind) first, and only the survivors' witnesses are
        // rendered: the census holds one candidate per row, never a string
        // per refusing edge. The derived edges are read through the engine's
        // scan, node by node, from the nodes of facts at an owned site only
        // (`fact_owners`): a derived edge's site is one of its node's facts'.
        let expanded = census.expanded();
        let mut candidates = Candidates::default();
        let mut consider = |order: EdgeOrder, edge: &ReachEdge| {
            let ReachSite::Mir(site) = edge.site else { return };
            let Some(&(Some(owner), span)) = sites.get(site as usize) else { return };
            let target = census.verdict(edge.to);
            let strength = target.min(edge.class.cap());
            if strength == Verdict::Quiet {
                return;
            }
            let kind = render.kind(edge, strength);
            if debug {
                eprintln!(
                    "TRUST_SPAWN_CENSUS_DEBUG row {:?} at {span:?}: {} -{:?}-> {}",
                    kind,
                    render.name(edge.from),
                    edge.class,
                    render.full_witness(edge.to)
                );
            }
            candidates.offer(owner, span, kind, order, edge.to);
        };
        for (index, edge) in expanded.edges()[..expanded.adapter_edge_count()].iter().enumerate() {
            consider(EdgeOrder::Adapter(index), edge);
        }
        let mut owners: Vec<ReachNode> = fact_owners.into_iter().collect();
        owners.sort_unstable();
        let mut scan = expanded.derived_edge_scan();
        let mut derived_edges = 0usize;
        for node in owners {
            for (order, edge) in scan.edges_from(node) {
                derived_edges += 1;
                consider(EdgeOrder::Derived(*order), edge);
            }
        }
        let mut rows = candidates.rows(|kind, target| {
            let witness = if kind == SpawnRowKind::DirectSpawn || !witnesses {
                String::new()
            } else {
                render.witness(target)
            };
            let mut text = kind.text(&witness);
            if let Some(causes) = &unclosed_causes {
                if kind == SpawnRowKind::NotEnumerated && render.decided_by_unclosed_pools(target) {
                    text.push_str(&unclosed_row_suffix(causes));
                    disclosed_rows += 1;
                }
            }
            if let Some(note) = &fallback_note {
                text.push_str(note);
            }
            text
        });
        if let Some(causes) = &unclosed_causes {
            if disclosed_rows > 0 && witnesses {
                tcx.dcx().struct_note(unclosed_crate_note(causes, disclosed_rows)).emit();
            }
        }

        let mut definitions = Vec::with_capacity(roots.len());
        for def in roots {
            let key = DefinitionKey(u128::from(def.local_def_index.as_u32()));
            let verdict =
                census.definition_verdict(key).map_or(TrustSpawnVerdict::Quiet, to_verdict);
            let mut rows = rows.remove(&def).unwrap_or_default();
            if let (Some(note), true) =
                (&fallback_note, rows.is_empty() && verdict != TrustSpawnVerdict::Quiet)
            {
                rows.push(TrustSpawnRow {
                    span: tcx.def_span(def),
                    verdict,
                    text: format!(
                        "not enumerated (no spawn was found); effect is unmodeled (fail-closed; \
                         not a spawn claim){note}"
                    ),
                });
            }
            let covered = covered.get(&def).cloned().unwrap_or_default();
            let walked = !unread.contains(&def);
            definitions.push((def, TrustSpawnSites { verdict, rows, walked, covered }));
        }

        if debug {
            let expanded = census.expanded();
            let pools = expanded.pools();
            let principals = principals.into_inner();
            let name_of = |key: &PrincipalKey| {
                principals.get(&key.0).map_or_else(
                    || format!("{:x}", key.0),
                    |predicates| {
                        rustc_middle::ty::print::with_no_trimmed_paths!(format!(
                            "{}",
                            Ty::new_dynamic(tcx, predicates, tcx.lifetimes.re_erased)
                        ))
                    },
                )
            };
            let open: Vec<String> = pools.open_principals().iter().map(name_of).collect();
            let (hubs, facts) = expanded.derivation_size();
            eprintln!(
                "TRUST_SPAWN_CENSUS_DEBUG summary: nodes={} edges={} (adapter {}; derived through \
                 {hubs} hubs and {facts} facts; {derived_edges} derived edges out of owned sites) \
                 sinks={:?} open-principals={:?} unclosed={} launder={} sysroot-scan={:?} \
                 sysroot-unjoined(vtables, upcasts)={:?} dead-invokes={} fallback={}",
                expanded.nodes().len(),
                expanded.edges().len(),
                expanded.adapter_edge_count(),
                sinks,
                open,
                pools.unclosed(),
                launder_at.as_deref().unwrap_or("none"),
                scanned,
                unjoined,
                dead_invokes,
                fallback.as_deref().unwrap_or("none"),
            );
            // What data may hold (design §10, "typed LAUNDER"): each key with
            // the first reinterpretation that put it there.
            let laundered: Vec<String> =
                laundered_at.iter().map(|(key, at)| format!("{} at {at}", key_text(key))).collect();
            eprintln!(
                "TRUST_SPAWN_CENSUS_DEBUG laundered-keys ({} in the engine): {laundered:?}",
                pools.laundered_keys().len()
            );
            for key in pools.open_principals() {
                let upcasts: Vec<String> = upcasts_of
                    .iter()
                    .filter(|(from, to)| from == key || to == key)
                    .map(|(from, to)| format!("{} -> {}", name_of(from), name_of(to)))
                    .collect();
                eprintln!(
                    "TRUST_SPAWN_CENSUS_DEBUG open principal {}: first named by {}; sysroot \
                     upcasts {:?}",
                    name_of(key),
                    named_at.get(key).map_or_else(|| "?".to_string(), |node| render.name(*node)),
                    upcasts
                );
            }
        }
        TrustSpawnCensus { definitions, fallback }
    }
}

fn to_verdict(verdict: Verdict) -> TrustSpawnVerdict {
    match verdict {
        Verdict::Quiet => TrustSpawnVerdict::Quiet,
        Verdict::Unknown => TrustSpawnVerdict::Unknown,
        Verdict::Indirect => TrustSpawnVerdict::Indirect,
        Verdict::Escapes => TrustSpawnVerdict::Escapes,
        Verdict::Spawns => TrustSpawnVerdict::Spawns,
    }
}

/// Where a row candidate's edge stands in the expanded graph's logical edge
/// order: every adapter edge, in order, then every derived edge in derivation
/// order.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum EdgeOrder {
    Adapter(usize),
    Derived(DerivedOrder),
}

/// The row candidates that can become rows, offered in any order: per local
/// body, the strongest verdict at each source position (a span's start), and
/// the first candidate, in edge order, of each span and kind.
#[derive(Default)]
struct Candidates {
    best: FxHashMap<(LocalDefId, rustc_span::BytePos), TrustSpawnVerdict>,
    first: FxHashMap<(LocalDefId, Span, SpawnRowKind), (EdgeOrder, ReachNode)>,
}

impl Candidates {
    fn offer(
        &mut self,
        owner: LocalDefId,
        span: Span,
        kind: SpawnRowKind,
        order: EdgeOrder,
        target: ReachNode,
    ) {
        let best = self.best.entry((owner, span.lo())).or_insert(kind.verdict());
        *best = (*best).max(kind.verdict());
        self.first
            .entry((owner, span, kind))
            .and_modify(|first| {
                if order < first.0 {
                    *first = (order, target);
                }
            })
            .or_insert((order, target));
    }

    /// The strongest rows per source position: a weaker row never hides a
    /// stronger one, and two sites of the same strength at one start
    /// (`mk_fn()()`) keep their own spans. One row per span and kind: the
    /// first candidate's (instances of a generic body share its spans), its
    /// text rendered only here. Rows come in the order of their spans, and of
    /// their first candidates at one span.
    fn rows(
        self,
        mut text: impl FnMut(SpawnRowKind, ReachNode) -> String,
    ) -> FxHashMap<LocalDefId, Vec<TrustSpawnRow>> {
        let mut kept: Vec<(LocalDefId, Span, SpawnRowKind, EdgeOrder, ReachNode)> = self
            .first
            .into_iter()
            .filter(|((owner, span, kind), _)| {
                self.best.get(&(*owner, span.lo())) == Some(&kind.verdict())
            })
            .map(|((owner, span, kind), (order, target))| (owner, span, kind, order, target))
            .collect();
        kept.sort_unstable_by_key(|(owner, span, _, order, _)| {
            (owner.local_def_index.as_u32(), span.lo(), span.hi(), *order)
        });
        let mut rows: FxHashMap<LocalDefId, Vec<TrustSpawnRow>> = FxHashMap::default();
        for (owner, span, kind, _, target) in kept {
            rows.entry(owner).or_default().push(TrustSpawnRow {
                span,
                verdict: kind.verdict(),
                text: text(kind, target),
            });
        }
        rows
    }
}

/// What the send census found, for the censuses after it.
struct Sends<'tcx> {
    sent: Vec<Sent<'tcx>>,
    /// Every enum a send in the graph carries, regions erased: one a thread
    /// with no named entry sends, or one sent only behind an indirect call,
    /// has consumers too.
    messages: Vec<Ty<'tcx>>,
    threads: Vec<Thread>,
}

/// A note at `span`, or one with no place when there is none.
fn note_at(tcx: TyCtxt<'_>, span: Option<Span>, text: String) {
    match span {
        Some(span) => tcx.dcx().struct_span_note(span, text).emit(),
        None => tcx.dcx().struct_note(text).emit(),
    }
}

/// The closure a thread's entry runs, with its type: the entry's own body,
/// or, behind a `FnOnce::call_once` shim (a closure bound to a variable before
/// it is spawned has its kind inferred from its body), the closure the shim
/// is for.
fn entry_closure<'tcx>(render: &Render<'_, 'tcx>, entry: ReachNode) -> Option<(DefId, Ty<'tcx>)> {
    let tcx = render.tcx;
    match render.key(entry)? {
        Key::Body { def, args, .. } if tcx.def_kind(def) == DefKind::Closure => {
            // At the instance that runs (a closure in a generic fn captures
            // `Arc<Slot<T>>`; the thread's captures `Arc<Slot<u8>>`).
            let this = if args.len() == tcx.generics_of(def).count() {
                tcx.type_of(def).instantiate(tcx, args).skip_norm_wip()
            } else {
                tcx.type_of(def).instantiate_identity().skip_norm_wip()
            };
            Some((def, at_instance(tcx, None, this)))
        }
        Key::Shim { instance, .. } => {
            let this = instance.args.types().next()?;
            match *this.kind() {
                ty::Closure(def, _) => Some((def, this)),
                _ => None,
            }
        }
        _ => None,
    }
}

/// The send census (`-Ztrust-send-census`): for every thread the census
/// found (each spawn site's entry, and `main`; in a library, which has no
/// `main`, the code its callers run), a note naming each std channel send
/// ([`is_std_channel_send`]) it reaches over the calls and drops the census
/// resolved (RUN edges), with the message type, the variants traced
/// ([`sent_variants`]) and a shortest call path. These are the actors a
/// derived model would have and what each posts (design: the temporal-models
/// P3 send-site census). A thread whose entry the census could not name says
/// so. Sends reached behind an indirect call's pool or a hand-off to foreign
/// code are listed after, by message type, whether or not the thread also
/// reaches that send directly: on a real event loop the hand-off of the
/// run-loop handler alone makes every thread "reach" the whole consumer, which
/// the design covers with a disclosed assumption, not a send.
fn report_sends<'tcx>(
    render: &Render<'_, 'tcx>,
    sites: &[(Option<LocalDefId>, Span)],
    hooks: &dyn CensusHooks<'tcx>,
    emit: bool,
) -> Sends<'tcx> {
    let tcx = render.tcx;
    let census = render.census;
    let mut found = Sends { sent: Vec::new(), messages: Vec::new(), threads: Vec::new() };
    let Some(spawns) = census.spawn_sites() else {
        if emit {
            tcx.dcx()
                .struct_note("send census: the spawn census fell back, so no thread is enumerated")
                .emit();
        }
        return found;
    };
    // Each thread: where its note goes, how the note calls it, how another
    // note names it, where it starts, whether the census knows what it runs,
    // and whether it is the library's callers.
    struct Actor {
        span: Option<Span>,
        who: String,
        named: String,
        starts: Vec<ReachNode>,
        known: bool,
        is_main: bool,
        outside: bool,
    }
    let expanded = census.expanded();
    let mut threads: Vec<Actor> = Vec::new();
    let entry_fn = tcx.entry_fn(());
    if let Some((main, _)) = entry_fn {
        let entry = expanded.nodes().find_map(|(node, _)| {
            matches!(render.key(node), Some(Key::Body { def, .. }) if def == main).then_some(node)
        });
        threads.push(Actor {
            span: Some(tcx.def_span(main)),
            who: "`main`".to_owned(),
            named: "`main`".to_owned(),
            starts: entry.into_iter().collect(),
            known: true,
            is_main: true,
            outside: false,
        });
    }
    type Site = trust_ir::function_dependencies::SpawnSite;
    // A spawn in a generic fn is walked once uninstantiated and once per
    // instance. Where an instance exists, it is the thread that runs; the
    // uninstantiated walk stands only for a generic no caller instantiates.
    let generic_site = |site: &Site| matches!(render.key(site.edge.from), Some(Key::Body { args, .. }) if args.has_non_region_param());
    // Where the spawn call is in the crate's own source.
    let owned = |site: ReachSite| match site {
        ReachSite::Mir(id) => sites.get(id as usize).and_then(|&(owner, span)| owner.map(|_| span)),
        _ => None,
    };
    // A spawn made by another crate's code (a helper that names its threads)
    // has no place in this crate: the nearest local calls that lead to it
    // stand for it, one thread per call (two calls of one helper with the
    // same callable are one spawn site in the graph and two threads). Found
    // by walking the resolved calls back, all such spawns at once, as far
    // as they go.
    let mut spans: Vec<Vec<Span>> =
        spawns.iter().map(|site| owned(site.edge.site).into_iter().collect()).collect();
    let mut pending: FxHashMap<ReachNode, Vec<usize>> = FxHashMap::default();
    for (index, site) in spawns.iter().enumerate() {
        if spans[index].is_empty() {
            pending.entry(site.edge.from).or_default().push(index);
        }
    }
    let mut calls_into: FxHashMap<ReachNode, Vec<&ReachEdge>> = FxHashMap::default();
    if !pending.is_empty() {
        for edge in expanded.edges() {
            if edge.class == EdgeClass::Run {
                calls_into.entry(edge.to).or_default().push(edge);
            }
        }
    }
    // (Each spawn passes a body once, so the walk ends.)
    let mut walked: FxHashSet<(ReachNode, usize)> = FxHashSet::default();
    while !pending.is_empty() {
        let mut next: FxHashMap<ReachNode, Vec<usize>> = FxHashMap::default();
        // Every local call at this distance, before looking further.
        let mut found: Vec<(usize, Span)> = Vec::new();
        let mut at: Vec<(&ReachNode, &Vec<usize>)> = pending.iter().collect();
        at.sort_unstable_by_key(|(node, _)| node.index());
        for (to, waiting) in at {
            for edge in calls_into.get(to).map_or(&[][..], Vec::as_slice) {
                let local = owned(edge.site);
                for &index in waiting {
                    match local {
                        Some(span) => found.push((index, span)),
                        None => {
                            if walked.insert((edge.from, index)) {
                                next.entry(edge.from).or_default().push(index);
                            }
                        }
                    }
                }
            }
        }
        for (index, span) in found {
            if !spans[index].contains(&span) {
                spans[index].push(span);
            }
        }
        // (A way ends at its first local call; another way to the same
        // spawn, through more of the dependency, goes on.)
        pending = next;
    }
    for at in &mut spans {
        at.sort_unstable_by_key(|span| (span.lo(), span.hi()));
    }
    // A spawn in generic code is walked as written and once per instance.
    // Two walks are one spawn when they are of the same spawn site and one's
    // arguments are an instance of the other's (`inner<F>` and
    // `inner<outer<T>::{closure#0}>`, `spawner<T>` and `spawner<u8>`): the
    // more instantiated one is the thread that runs, or stands for it best.
    // Walks whose arguments differ any other way (two closures through one
    // helper, the two spawn sites of a `spawn_pair`) are two threads,
    // wherever their notes land.
    let from_of = |site: &Site| match render.key(site.edge.from) {
        Some(Key::Body { def, args, .. }) => Some((def, args)),
        _ => None,
    };
    // (Each walk of a body numbers its call sites anew: one place in source
    // is the same owner and span.)
    let same_place = |one: ReachSite, other: ReachSite| match (one, other) {
        (ReachSite::Mir(one), ReachSite::Mir(other)) => {
            sites.get(one as usize) == sites.get(other as usize)
        }
        _ => one == other,
    };
    for (index, site) in spawns.iter().enumerate() {
        let generic = generic_site(site);
        let at: &[Span] = spans[index].as_slice();
        if generic {
            let subsumed = from_of(site).is_some_and(|(def, args)| {
                spawns.iter().enumerate().any(|(other, seen)| {
                    other != index
                        && same_place(seen.edge.site, site.edge.site)
                        && from_of(seen).is_some_and(|(seen_def, seen_args)| {
                            seen_def == def
                                && seen_args != args
                                && seen_args.len() == args.len()
                                && args
                                    .types()
                                    .zip(seen_args.types())
                                    .all(|(general, instance)| could_be(general, instance))
                        })
                })
            });
            if subsumed {
                continue;
            }
        }
        let own = owned(site.edge.site);
        let closure = site.entry.and_then(|entry| entry_closure(render, entry));
        let places: Vec<Option<Span>> = if at.is_empty() {
            vec![closure.map(|(def, _)| tcx.def_span(def))]
        } else {
            at.iter().copied().map(Some).collect()
        };
        for span in places {
            let named = match (site.entry, span) {
                // A closure entered through a shim is named as the closure.
                (Some(entry), _) => match (render.key(entry), closure) {
                    (Some(Key::Shim { .. }), Some((def, _))) => {
                        format!("`{}`", tcx.def_path_str(def))
                    }
                    _ => format!("`{}`", render.name(entry)),
                },
                (None, Some(span)) => format!(
                    "the thread spawned at {}",
                    tcx.sess.source_map().span_to_diagnostic_string(span)
                ),
                (None, None) => "a thread another crate's code spawns".to_owned(),
            };
            let mut who = if own.is_some() {
                "the thread spawned here".to_owned()
            } else if !at.is_empty() {
                "the thread spawned through this call".to_owned()
            } else if span.is_some() {
                "the thread that runs this closure".to_owned()
            } else {
                format!("the thread that runs {named}")
            };
            if generic {
                who.push_str(" (in a generic fn this crate never instantiates)");
            }
            threads.push(Actor {
                span,
                who,
                named,
                starts: site.entry.into_iter().collect(),
                known: site.entry.is_some(),
                is_main: false,
                outside: false,
            });
        }
    }
    // The exact reach: RUN edges only (calls and drops the census resolved),
    // never entering a seed. What the thread closure adds over it is reached
    // only through an APPROX edge (an indirect call's pool, or code handed to
    // foreign code that may call it back): a real send can hide there, but most
    // are artefacts of the pool (every implementer of one `dyn` signature).
    let mut run_out: FxHashMap<ReachNode, Vec<ReachEdge>> = FxHashMap::default();
    // What each body reads: constants and statics.
    let mut read_out: FxHashMap<ReachNode, Vec<ReachNode>> = FxHashMap::default();
    for edge in expanded.edges() {
        match edge.class {
            EdgeClass::Run => run_out.entry(edge.from).or_default().push(*edge),
            EdgeClass::Read => read_out.entry(edge.from).or_default().push(edge.to),
            _ => {}
        }
    }
    let is_seed = |node: ReachNode| {
        matches!(
            expanded.node(node),
            Some(ReachNodeKind::Program(ReachNodeSpec { body: NodeBody::Seed, .. }))
        )
    };
    // The bodies outside code calls with values of its own: for a library's
    // callers, their starts and every instance of an exported body.
    let mut callable: FxHashSet<ReachNode> = FxHashSet::default();
    if entry_fn.is_none() {
        // A library has no `main`: what runs its code is whoever calls it.
        // That actor starts at every body outside code can name (an exported
        // fn or method, the body of an exported `async fn`, whatever also
        // calls it inside the crate), and at every other local body that no
        // running body calls over a resolved call and no spawn starts: the
        // handlers and callbacks the crate hands out. "Running" is decided
        // callers first, by strongly connected component of the resolved call
        // graph: two private fns that only call each other start there too; a
        // closure only a foreign generic instance calls is entered from
        // whoever called that instance; and a shim or a vtable's instance
        // that nothing calls (a `dyn Fn`, a fn pointer: only a CREATE put it
        // in the graph) enters nothing, so the handler behind it is a start.
        // A generic body stands for the instances outside code makes of it; a
        // private one the crate instantiates itself runs only as those
        // instances.
        let mut entries: FxHashSet<ReachNode> =
            spawns.iter().filter_map(|site| site.entry).collect();
        // A callable made into a value in a body that starts a thread the
        // census cannot name (a boxed job, a fn pointer) is taken to be what
        // that thread runs, not something the crate hands its callers.
        let unnamed: FxHashSet<ReachNode> =
            spawns.iter().filter(|site| site.entry.is_none()).map(|site| site.edge.from).collect();
        if !unnamed.is_empty() {
            for edge in expanded.edges() {
                if edge.class == EdgeClass::Create && unnamed.contains(&edge.from) {
                    entries.insert(edge.to);
                }
            }
        }
        let calls: Vec<(usize, usize)> = expanded
            .edges()
            .iter()
            .filter(|edge| edge.class == EdgeClass::Run)
            .map(|edge| (edge.from.index(), edge.to.index()))
            .collect();
        let call_graph = VecGraph::<usize>::new(expanded.nodes().len(), calls);
        let cycles: Sccs<usize, usize> = Sccs::new(&call_graph);
        let mut instances: FxHashMap<DefId, usize> = FxHashMap::default();
        for (node, _) in expanded.nodes() {
            if let Some(Key::Body { def, .. }) = render.key(node) {
                *instances.entry(def).or_default() += 1;
            }
        }
        let visibilities = tcx.effective_visibilities(());
        let level = rustc_middle::middle::privacy::Level::ReachableThroughImplTrait;
        let exported = |def: DefId| {
            let Some(local) = def.as_local() else { return false };
            // An `async fn`'s body is its fn's.
            let named = match tcx.coroutine_kind(def) {
                Some(rustc_hir::CoroutineKind::Desugared(_, rustc_hir::CoroutineSource::Fn)) => {
                    tcx.local_parent(local)
                }
                _ => local,
            };
            visibilities.is_public_at_level(named, level)
        };
        let local_body = |node: ReachNode| match render.key(node) {
            Some(Key::Body { def, args, .. }) if def.is_local() => Some((def, args)),
            _ => None,
        };
        // An exported body, as outside code calls it.
        let named_start = |node: ReachNode| {
            local_body(node).is_some_and(|(def, args)| {
                // A coroutine's own parameters are the compiler's (its
                // resume and yield types, its upvars): whether an `async
                // fn`'s body is generic is the fn's to say.
                let root = tcx.typeck_root_def_id(def);
                !entries.contains(&node)
                    && exported(def)
                    && (args.has_non_region_param()
                        || !tcx.generics_of(root).requires_monomorphization(tcx))
            })
        };
        // A body that starts there when nothing running calls it.
        let root_start = |node: ReachNode| {
            local_body(node).is_some_and(|(def, args)| {
                !entries.contains(&node)
                    && !(args.has_non_region_param()
                        && !exported(def)
                        && instances.get(&def).is_some_and(|count| *count > 1))
            })
        };
        let mut members: Vec<Vec<ReachNode>> = vec![Vec::new(); cycles.num_sccs()];
        for (node, _) in expanded.nodes() {
            members[cycles.scc(node.index())].push(node);
        }
        let mut entered = vec![false; cycles.num_sccs()];
        let mut starts: Vec<ReachNode> = Vec::new();
        // Components come in dependency order, callees first.
        for component in (0..cycles.num_sccs()).rev() {
            let nodes = &members[component];
            let mut runs = entered[component] || nodes.iter().any(|node| entries.contains(node));
            for &node in nodes {
                if named_start(node) || (!entered[component] && root_start(node)) {
                    starts.push(node);
                    runs = true;
                }
            }
            if runs {
                for &callee in cycles.successors(component) {
                    entered[callee] = true;
                }
            }
        }
        starts.sort_unstable();
        callable.extend(starts.iter().copied());
        callable.extend(
            expanded
                .nodes()
                .map(|(node, _)| node)
                .filter(|node| local_body(*node).is_some_and(|(def, _)| exported(def))),
        );
        threads.insert(
            0,
            Actor {
                span: Some(tcx.def_span(rustc_span::def_id::CRATE_DEF_ID)),
                who: "code called from outside this crate (it has no `main`)".to_owned(),
                named: "code called from outside the crate".to_owned(),
                starts,
                known: true,
                is_main: false,
                outside: true,
            },
        );
    }
    let send_of = |node: ReachNode| match render.key(node) {
        Some(Key::Body { def, args, .. })
            if is_std_channel_send(tcx, def) || is_std_channel_send_inside(tcx, def) =>
        {
            Some(args.types().next().map_or_else(|| "a message".to_owned(), |ty| format!("`{ty}`")))
        }
        _ => None,
    };
    // The channel's own code: a send inside it that only that code calls is
    // part of a send already counted.
    let channel_code = |node: ReachNode| match render.key(node) {
        Some(Key::Body { def, .. }) => {
            in_std_module(tcx, def, "mpsc") || in_std_module(tcx, def, "mpmc")
        }
        _ => false,
    };
    let inside = |node: ReachNode| matches!(render.key(node), Some(Key::Body { def, .. }) if is_std_channel_send_inside(tcx, def));
    let message_ty = |node: ReachNode| match render.key(node) {
        Some(Key::Body { args, .. }) => {
            args.types().next().map(|ty| tcx.erase_and_anonymize_regions(ty))
        }
        _ => None,
    };
    // Every send in the graph, found once.
    let send_nodes: Vec<(ReachNode, String)> =
        expanded.nodes().filter_map(|(node, _)| Some((node, send_of(node)?))).collect();
    for (node, _) in &send_nodes {
        let Some(ty) = message_ty(*node) else { continue };
        if matches!(ty.kind(), ty::Adt(adt, _) if adt.is_enum()) && !found.messages.contains(&ty) {
            found.messages.push(ty);
        }
    }
    // And every enum the crate takes off a channel: a library whose callers
    // hold the sender sends it nowhere itself, and has consumers all the
    // same.
    for (node, _) in expanded.nodes() {
        let Some(Key::Body { def, args, .. }) = render.key(node) else { continue };
        if !is_std_channel_recv(tcx, def) {
            continue;
        }
        let Some(ty) = args.types().next().map(|ty| tcx.erase_and_anonymize_regions(ty)) else {
            continue;
        };
        if matches!(ty.kind(), ty::Adt(adt, _) if adt.is_enum())
            && !ty.has_non_region_param()
            && !found.messages.contains(&ty)
        {
            found.messages.push(ty);
        }
    }
    // Which sends each node reaches over RUN and APPROX edges, never leaving a
    // seed (`ReachCensus::thread_closure`'s walk), for every thread at once:
    // the graph's strongly connected components, each with a bitset of the
    // sends it reaches, filled in dependency order. A walk per thread was
    // seconds each on aterm-gui, whose threads all reach most of the graph
    // through winit's run-loop hand-off.
    let words = send_nodes.len().div_ceil(64).max(1);
    let wide = VecGraph::<usize>::new(
        expanded.nodes().len(),
        expanded
            .edges()
            .iter()
            .filter(|edge| {
                matches!(edge.class, EdgeClass::Run | EdgeClass::Approx | EdgeClass::Create)
                    && !is_seed(edge.from)
            })
            .map(|edge| (edge.from.index(), edge.to.index()))
            .collect(),
    );
    let components: Sccs<usize, usize> = Sccs::new(&wide);
    let mut reaches = vec![0u64; components.num_sccs() * words];
    for (bit, (node, _)) in send_nodes.iter().enumerate() {
        reaches[components.scc(node.index()) * words + bit / 64] |= 1 << (bit % 64);
    }
    for component in components.all_sccs() {
        for &next in components.successors(component) {
            for word in 0..words {
                let carried = reaches[next * words + word];
                reaches[component * words + word] |= carried;
            }
        }
    }
    // Of those, the sends a node reaches behind at least one APPROX edge:
    // what an APPROX edge's target reaches, carried back to everything that
    // reaches the edge.
    let mut behind = vec![0u64; components.num_sccs() * words];
    for edge in expanded.edges() {
        // A callable the code makes into a value (CREATE) may be run behind
        // one too: `Once::call_once(|| tx.send(..))` erases its closure
        // inside std, and std's own code calls it.
        if matches!(edge.class, EdgeClass::Approx | EdgeClass::Create) && !is_seed(edge.from) {
            let from = components.scc(edge.from.index());
            let to = components.scc(edge.to.index());
            for word in 0..words {
                behind[from * words + word] |= reaches[to * words + word];
            }
        }
    }
    for component in components.all_sccs() {
        for &next in components.successors(component) {
            for word in 0..words {
                let carried = behind[next * words + word];
                behind[component * words + word] |= carried;
            }
        }
    }
    let reaches_behind = |entry: ReachNode, bit: usize| {
        behind[components.scc(entry.index()) * words + bit / 64] & (1 << (bit % 64)) != 0
    };
    for (index, actor) in threads.into_iter().enumerate() {
        let Actor { span, who, named, starts, known, is_main, outside } = actor;
        let mut exact: BTreeMap<ReachNode, Option<ReachEdge>> = BTreeMap::new();
        {
            let mut queue = VecDeque::new();
            for &start in &starts {
                if exact.insert(start, None).is_none() {
                    queue.push_back(start);
                }
            }
            while let Some(node) = queue.pop_front() {
                if is_seed(node) {
                    continue;
                }
                for edge in run_out.get(&node).map_or(&[][..], Vec::as_slice) {
                    if let std::collections::btree_map::Entry::Vacant(slot) = exact.entry(edge.to) {
                        slot.insert(Some(*edge));
                        queue.push_back(edge.to);
                    }
                }
            }
        }
        // The thread's RUN edges by callee, for tracing what it sends.
        let mut callers: FxHashMap<ReachNode, Vec<ReachEdge>> = FxHashMap::default();
        for &node in exact.keys() {
            if is_seed(node) {
                continue;
            }
            for edge in run_out.get(&node).map_or(&[][..], Vec::as_slice) {
                callers.entry(edge.to).or_default().push(*edge);
            }
        }
        // The bodies outside code calls with values of its own.
        let open: FxHashSet<ReachNode> =
            if outside { callable.clone() } else { FxHashSet::default() };
        let path_to = |node: ReachNode| {
            let mut names = Vec::new();
            let mut current = node;
            while let Some(Some(edge)) = exact.get(&current) {
                names.push(render.name(edge.to));
                current = edge.from;
            }
            names.push(render.name(current));
            names.reverse();
            names.join(" -> ")
        };
        let row = |sent: &mut Vec<Sent<'tcx>>, message: Ty<'tcx>| -> usize {
            match sent.iter().position(|row| row.thread == index && row.message == message) {
                Some(at) => at,
                None => {
                    sent.push(Sent {
                        thread: index,
                        who: named.clone(),
                        message,
                        variants: BTreeSet::new(),
                        untraced: false,
                        indirect: false,
                    });
                    sent.len() - 1
                }
            }
        };
        // Each send with its path, and whether it is one inside the channel
        // code.
        let mut sends: Vec<(String, String, bool)> = Vec::new();
        for (node, message) in &send_nodes {
            let (node, message) = (*node, message.clone());
            if !exact.contains_key(&node) {
                continue;
            }
            // A send inside the channel code counts only where code outside
            // it calls it: where the inliner removed `mpsc`'s own `send`.
            let inner = inside(node);
            if inner
                && !callers
                    .get(&node)
                    .is_some_and(|edges| edges.iter().any(|edge| !channel_code(edge.from)))
            {
                continue;
            }
            let ty = message_ty(node);
            let (variants, complete) = ty
                .map(|ty| {
                    sent_variants(
                        render, sites, hooks, &callers, &run_out, &read_out, &open, node, ty,
                    )
                })
                .unwrap_or((Vec::new(), true));
            if let Some(ty) = ty {
                let at = row(&mut found.sent, ty);
                found.sent[at].untraced |= !complete;
                found.sent[at].variants.extend(variants.iter().cloned());
                // A sender still to be instantiated (a library's exported
                // `Bus<T>::post(m: T)`, a send of `Msg<T>`, a thread spawned
                // in a generic fn the crate makes no instance of) sends
                // whatever it is instantiated with: each of the program's
                // message enums the type can be, with a variant not traced.
                if ty.has_non_region_param() {
                    for message in found.messages.clone() {
                        if could_be(ty, message) {
                            let at = row(&mut found.sent, message);
                            found.sent[at].untraced = true;
                        }
                    }
                }
            }
            // `…` marks a value the census could not trace to a variant.
            let generic = ty.is_some_and(|ty| ty.has_non_region_param());
            let message = match (variants.is_empty(), complete) {
                // Whoever instantiates the code chooses the type: any message
                // enum of the program's it can be, whose own entry cannot
                // say so.
                _ if generic && outside => format!("{message} (any type its callers pass)"),
                _ if generic => format!("{message} (at whatever type the fn is instantiated)"),
                (true, true) => message,
                (true, false) => format!("{message} (…)"),
                (false, true) => format!("{message} ({})", variants.join(", ")),
                (false, false) => format!("{message} ({}, …)", variants.join(", ")),
            };
            sends.push((message, path_to(node), inner));
        }
        sends.sort();
        sends.dedup();
        // The three channel flavors are one send of the message.
        let mut flavors: FxHashSet<String> = FxHashSet::default();
        sends.retain(|(message, _, inner)| !*inner || flavors.insert(message.clone()));
        let mut indirect: Vec<String> = Vec::new();
        for (bit, (node, message)) in send_nodes.iter().enumerate() {
            if !starts.iter().any(|start| reaches_behind(*start, bit)) {
                continue;
            }
            indirect.push(message.clone());
            if let Some(ty) = message_ty(*node) {
                let at = row(&mut found.sent, ty);
                found.sent[at].indirect = true;
            }
        }
        indirect.sort();
        indirect.dedup();
        let mut text = if !known {
            // What the thread runs is a value: the census cannot say what it
            // sends, so it must not say it sends nothing.
            format!(
                "send census: {who} runs a callable the census could not name (a fn pointer, a \
                 `dyn FnOnce` or a type parameter): its sends are not enumerated"
            )
        } else if sends.is_empty() {
            format!("send census: {who} sends on no std channel over the calls it makes")
        } else {
            let listed: Vec<String> =
                sends.iter().map(|(message, path, _)| format!("{message} via {path}")).collect();
            format!("send census: {who} sends {}", listed.join("; "))
        };
        if !indirect.is_empty() {
            text.push_str(&format!(
                ". Behind indirect calls or code it hands off it may also reach sends of {} \
                 message type(s): {}",
                indirect.len(),
                indirect.join(", ")
            ));
        }
        if emit {
            note_at(tcx, span, text);
        }
        found.threads.push(Thread {
            span,
            named: named.clone(),
            is_main,
            known,
            entry: starts.first().copied().filter(|_| starts.len() == 1 && !outside),
            exact: exact.keys().copied().collect(),
            starts,
        });
    }
    found
}

/// One consumer the consumer census found, for the shared-state and writer
/// censuses.
struct Consumer<'tcx> {
    def: LocalDefId,
    message: Ty<'tcx>,
    /// The message's variants, by index.
    names: Vec<String>,
    /// Per block of the consumer's body, the variants the held message can be
    /// when it runs ([`Dispatch::live`]).
    live: Vec<VariantSet>,
    /// The same per message the body holds ([`Dispatch::by_root`]): a body
    /// with two in hand is in an arm of each.
    by_root: Vec<Vec<VariantSet>>,
}

/// One thread the send census enumerated, for the shared-state census.
struct Thread {
    /// Its spawn site (`main`'s definition), when it has a place.
    span: Option<Span>,
    /// How another census's note names it.
    named: String,
    is_main: bool,
    /// Whether the census knows what the thread runs. Not for a thread
    /// started with a fn pointer, a `dyn FnOnce` or a type parameter.
    known: bool,
    /// Its entry, for a thread with one.
    entry: Option<ReachNode>,
    /// Where it starts: its entry, or, for a library's callers, every body
    /// they can call.
    starts: Vec<ReachNode>,
    /// What it reaches over RUN edges.
    exact: FxHashSet<ReachNode>,
}

/// What one thread sends of one message type, for the consumer census.
struct Sent<'tcx> {
    /// The thread, by its place in the send census's order.
    thread: usize,
    /// The thread, as an arm's note names it.
    who: String,
    /// The message type, regions erased.
    message: Ty<'tcx>,
    /// The variants traced, over the calls the census resolved.
    variants: BTreeSet<String>,
    /// Whether some send of it over those calls had a value the census could
    /// not trace to a variant.
    untraced: bool,
    /// Whether the thread may also reach a send of it behind an indirect call
    /// or a hand-off.
    indirect: bool,
}

/// `a`, `a and b`, `a, b and c`.
fn and_list(items: &[String]) -> String {
    match items {
        [] => String::new(),
        [one] => one.clone(),
        [init @ .., last] => format!("{} and {last}", init.join(", ")),
    }
}

/// How a body comes to hold a message, for the consumer census.
#[derive(Clone, Copy)]
enum Holds {
    /// It takes it off a std `Receiver`: a drain loop.
    Drains,
    /// Foreign code calls it with one: an implementation of another crate's
    /// trait method that takes it by value (winit calls
    /// `ApplicationHandler::user_event` from its run loop).
    Foreign(DefId),
    /// Such a body passes it on by value to this local fn, which does not
    /// hand it back.
    From(LocalDefId),
}

/// A set of a message enum's variants, by index.
#[derive(Clone, PartialEq, Eq)]
struct VariantSet {
    words: Vec<u64>,
    len: usize,
}

impl VariantSet {
    fn none(len: usize) -> Self {
        VariantSet { words: vec![0; len.div_ceil(64).max(1)], len }
    }

    fn all(len: usize) -> Self {
        let mut set = Self::none(len);
        for index in 0..len {
            set.insert(index);
        }
        set
    }

    fn insert(&mut self, index: usize) {
        self.words[index / 64] |= 1 << (index % 64);
    }

    fn remove(&mut self, index: usize) {
        self.words[index / 64] &= !(1 << (index % 64));
    }

    fn contains(&self, index: usize) -> bool {
        self.words[index / 64] & (1 << (index % 64)) != 0
    }

    fn count(&self) -> usize {
        self.words.iter().map(|word| word.count_ones() as usize).sum()
    }

    /// Adds `other`; whether anything was added.
    fn union(&mut self, other: &VariantSet) -> bool {
        let mut grew = false;
        for (word, more) in self.words.iter_mut().zip(&other.words) {
            grew |= *more & !*word != 0;
            *word |= *more;
        }
        grew
    }

    fn iter(&self) -> impl Iterator<Item = usize> + '_ {
        (0..self.len).filter(|index| self.contains(*index))
    }
}

/// Whether `adt` is one of `std::sync::mpsc`'s iterators over a channel.
fn is_mpsc_iterator(tcx: TyCtxt<'_>, adt: ty::AdtDef<'_>) -> bool {
    matches!(tcx.item_name(adt.did()).as_str(), "Iter" | "TryIter" | "IntoIter")
        && crate::def_is_in_sysroot_resident_crate(tcx, adt.did())
        && tcx.opt_item_name(tcx.parent(adt.did())).is_some_and(|name| name.as_str() == "mpsc")
}

/// The message a call takes off a std channel, one per call: `recv`,
/// `try_recv`, `recv_timeout`, `recv_deadline` on `mpsc::Receiver<M>`, and
/// `Iterator::next` on its `Iter`, `TryIter` and `IntoIter` (a `for` loop's
/// step) or on an adapter over one (`rx.try_iter().take(n)`).
fn receives_message<'tcx>(
    tcx: TyCtxt<'tcx>,
    callee: DefId,
    callee_args: GenericArgs<'tcx>,
) -> Option<Ty<'tcx>> {
    if is_std_channel_recv(tcx, callee) {
        let stepwise = tcx
            .opt_item_name(callee)
            .is_some_and(|name| !matches!(name.as_str(), "iter" | "try_iter" | "into_iter"));
        return stepwise.then(|| callee_args.types().next()).flatten();
    }
    if tcx.lang_items().next_fn() != Some(callee) {
        return None;
    }
    let iterator = callee_args.types().next()?;
    let message = mpsc_iterator_item(tcx, iterator)?;
    // An adapter whose callable makes the item (`map`, `flat_map`,
    // `filter_map`, `scan`) yields what the callable returns, which is not
    // the message received. One whose callable only looks (`filter`,
    // `inspect`, `take_while`) yields the message.
    if remakes_message(tcx, iterator, tcx.erase_and_anonymize_regions(message)) {
        return None;
    }
    Some(message)
}

/// Whether a value of type `ty` is or holds a callable that takes the
/// message and returns one (`map`'s closure, the `Map` adapter built with it,
/// a fn pointer of that shape; a coroutine or a `dyn Fn` is taken to):
/// the message given to it goes into the callable, and what comes back is
/// what the callable made. A callable that takes no message
/// (`unwrap_or_else(|| Msg::Idle)`) is another source beside the message,
/// like `unwrap_or`'s second argument, and one that returns none (`filter`,
/// `inspect`) only looks.
fn remakes_message<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>, message: Ty<'tcx>) -> bool {
    let names =
        |ty: Ty<'tcx>| tcx.erase_and_anonymize_regions(ty).walk().any(|arg| arg == message.into());
    let remakes = |inputs: &[Ty<'tcx>], output: Ty<'tcx>| {
        names(output) && inputs.iter().any(|input| names(*input))
    };
    ty.walk().any(|arg| match arg.kind() {
        GenericArgKind::Type(part) => match *part.kind() {
            ty::Closure(_, args) => {
                let sig = args.as_closure().sig().skip_binder();
                remakes(sig.inputs(), sig.output())
            }
            ty::FnDef(def, args) => {
                let sig = erased_sig(tcx, def, Some(args.skip_binder()));
                remakes(sig.inputs(), sig.output())
            }
            ty::FnPtr(sig, _) => {
                let sig = sig.skip_binder();
                remakes(sig.inputs(), sig.output())
            }
            // What a `dyn Fn` or a coroutine returns is not known here. Any
            // other `dyn` (an error type's `dyn Error`) is no callable.
            ty::Dynamic(predicates, ..) => predicates
                .principal_def_id()
                .is_some_and(|def| tcx.fn_trait_kind_from_def_id(def).is_some()),
            ty::Coroutine(..) => true,
            _ => false,
        },
        _ => false,
    })
}

/// The message of the `std::sync::mpsc` iterator that `iterator` is or
/// adapts (`TryIter<M>`, `Take<IntoIter<M>>`).
fn mpsc_iterator_item<'tcx>(tcx: TyCtxt<'tcx>, iterator: Ty<'tcx>) -> Option<Ty<'tcx>> {
    iterator.walk().find_map(|arg| match arg.kind() {
        GenericArgKind::Type(part) => match *part.kind() {
            ty::Adt(adt, args) if is_mpsc_iterator(tcx, adt) => args.types().next(),
            _ => None,
        },
        _ => None,
    })
}

/// The message a call starts draining from a std channel: any
/// [`receives_message`] call, `iter` and `try_iter` on a `Receiver<M>`, and
/// `IntoIterator::into_iter` on one or on a reference to one (`for m in rx`,
/// `for m in &rx`: MIR names the trait method, not an inherent one).
fn drains_message<'tcx>(
    tcx: TyCtxt<'tcx>,
    callee: DefId,
    callee_args: GenericArgs<'tcx>,
) -> Option<Ty<'tcx>> {
    if is_std_channel_recv(tcx, callee) {
        return callee_args.types().next();
    }
    if tcx.lang_items().into_iter_fn() == Some(callee) {
        let ty::Adt(adt, args) = *callee_args.types().next()?.peel_refs().kind() else {
            return None;
        };
        let receiver =
            tcx.get_diagnostic_name(adt.did()).is_some_and(|name| name.as_str() == "MpscReceiver");
        return receiver.then(|| args.types().next()).flatten();
    }
    receives_message(tcx, callee, callee_args)
}

/// What a local is to the message a body holds.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Hold {
    No,
    /// The message itself.
    Is,
    /// A value that wraps the message and no other of its type: a receive's
    /// `Result`, a filter's `Option`, an iterator over the channel.
    Wraps,
    /// A reference to the message.
    Refers,
}

/// A type as a body names it, at the instance the body is examined at
/// (`subst`: a generic body's own parameters given what one of its callers
/// instantiates them with), regions erased, and normalized once nothing is
/// left to instantiate (`<F as FnOnce<(Msg,)>>::Output`).
fn at_instance<'tcx, T>(tcx: TyCtxt<'tcx>, subst: Option<GenericArgs<'tcx>>, value: T) -> T
where
    T: rustc_middle::ty::TypeFoldable<TyCtxt<'tcx>> + Copy,
{
    let value = match subst {
        Some(args) if !args.is_empty() => {
            ty::EarlyBinder::bind(tcx, value).instantiate(tcx, args).skip_norm_wip()
        }
        _ => value,
    };
    let value = tcx.erase_and_anonymize_regions(value);
    if value.has_non_region_param() {
        return value;
    }
    tcx.try_normalize_erasing_regions(
        ty::TypingEnv::fully_monomorphized(),
        ty::Unnormalized::new_wip(value),
    )
    .unwrap_or(value)
}

/// The message a body holds, local by local ([`held_message`]).
struct Held<'tcx> {
    /// The instance the body was read at ([`at_instance`]).
    subst: Option<GenericArgs<'tcx>>,
    locals: Vec<Hold>,
    /// The fields of a tuple or other aggregate that were built from the
    /// message or from a reference to it: (aggregate, field) to every local
    /// moved in (a tuple assigned on two ways has one for each).
    fields: FxHashMap<(mir::Local, usize), Vec<mir::Local>>,
    /// The local each held local got the message from, first.
    source: Vec<Option<mir::Local>>,
    /// Every local it got one from: a local assigned on two paths has two.
    sources: Vec<Vec<mir::Local>>,
    /// The locals a message first comes into: a parameter that is given it,
    /// what a receive returns.
    rooted: FxHashSet<mir::Local>,
    /// The local fns the message went through and came back from: result,
    /// callee, and whether the result can lack it (it is not the bare type).
    filters: Vec<(mir::Local, DefId, Filter)>,
    /// The blocks whose call hands the message to a callee that may rewrite
    /// it: what comes back can be any variant.
    rewritten: FxHashSet<mir::BasicBlock>,
    /// The locals a `&mut` of which went to code outside the crate
    /// (`mem::swap(&mut self.pending, &mut m)`, `mem::take(&mut m)`): what
    /// they hold after is whatever that code put there.
    clobbered: FxHashSet<mir::Local>,
}

impl<'tcx> Held<'tcx> {
    /// Whether `place` is the held message: the local itself, the target of
    /// a reference to it, a field an aggregate was built with (or the target
    /// of a reference put in one: `match (&state, &msg)`), or what a wrapper
    /// unwraps to.
    fn is_message(
        &self,
        tcx: TyCtxt<'tcx>,
        body: &mir::Body<'tcx>,
        place: mir::Place<'tcx>,
        message: Ty<'tcx>,
    ) -> bool {
        if self.clobbered.contains(&place.local)
            || at_instance(tcx, self.subst, place.ty(body, tcx).ty) != message
        {
            return false;
        }
        let built_with = |field: rustc_abi::FieldIdx, hold: Hold| {
            self.built(place.local, field).iter().any(|local| self.locals[local.as_usize()] == hold)
        };
        match (self.locals[place.local.as_usize()], place.projection.as_slice()) {
            (Hold::Is, []) => true,
            (Hold::Refers, [mir::ProjectionElem::Deref]) => true,
            // What a wrapper put in an aggregate unwraps to, read through
            // its field (`((_t.0) as Ok).0` for `(rx.recv(), &last)`).
            (Hold::No, [mir::ProjectionElem::Field(field, _), _, ..])
                if built_with(*field, Hold::Wraps) =>
            {
                !self.into_payload(tcx, body, place, message)
            }
            (Hold::Wraps, [_, ..]) => !self.into_payload(tcx, body, place, message),
            (_, [mir::ProjectionElem::Field(field, _)]) => built_with(*field, Hold::Is),
            (_, [mir::ProjectionElem::Field(field, _), mir::ProjectionElem::Deref]) => {
                built_with(*field, Hold::Refers)
            }
            _ => false,
        }
    }

    /// The locals field `field` of the aggregate in `local` was built from.
    fn built(&self, local: mir::Local, field: rustc_abi::FieldIdx) -> &[mir::Local] {
        self.fields.get(&(local, field.as_usize())).map_or(&[], Vec::as_slice)
    }

    /// Records that field `index` of the aggregate in `local` was built from
    /// `from`; whether that is news.
    fn build(&mut self, local: mir::Local, index: usize, from: mir::Local) -> bool {
        let built = self.fields.entry((local, index)).or_default();
        let news = !built.contains(&from);
        if news {
            built.push(from);
        }
        news
    }

    /// The locals `place` reads the message out of: for a read of or through
    /// a field an aggregate was built with (`t.0`, `(t.0 as Ok).0`), what was
    /// moved into the field; else the place's own local. A read through a
    /// variant of an enum the body built (`(batch as Two).1` of a
    /// `Batch::Two(first, second)`) is both: the fields of two variants are
    /// not told apart, and the local may hold a value built elsewhere.
    fn read_from(&self, place: mir::Place<'tcx>) -> Vec<mir::Local> {
        match place.projection.as_slice() {
            [mir::ProjectionElem::Field(field, _), ..] => {
                let built = self.built(place.local, *field);
                if built.is_empty() { vec![place.local] } else { built.to_vec() }
            }
            [mir::ProjectionElem::Downcast(..), mir::ProjectionElem::Field(field, _), ..] => {
                let mut from = self.built(place.local, *field).to_vec();
                from.push(place.local);
                from
            }
            _ => vec![place.local],
        }
    }

    /// Whether `place` goes through the message into its payload: a shorter
    /// prefix of it already has the message's type (`((r as Ok).0 as
    /// Batch).0`, the `Vec<Msg>` a `Batch` carries, and the `Msg` a `Boxed`
    /// one points to). What is there is another value.
    fn into_payload(
        &self,
        tcx: TyCtxt<'tcx>,
        body: &mir::Body<'tcx>,
        place: mir::Place<'tcx>,
        message: Ty<'tcx>,
    ) -> bool {
        (0..place.projection.len()).any(|len| {
            let prefix = mir::PlaceRef { local: place.local, projection: &place.projection[..len] };
            at_instance(tcx, self.subst, prefix.ty(body, tcx).ty) == message
        })
    }

    /// The messages `local` can be, each named by the local it first came
    /// into ([`Self::rooted`]): two held locals with no root in common are
    /// two messages (two receives, two parameters), and a switch over one
    /// says nothing about the other.
    fn roots(&self, local: mir::Local) -> Vec<mir::Local> {
        let mut seen: FxHashSet<mir::Local> = FxHashSet::default();
        let mut stack = vec![local];
        let mut roots: Vec<mir::Local> = Vec::new();
        while let Some(local) = stack.pop() {
            if !seen.insert(local) {
                continue;
            }
            let from = &self.sources[local.as_usize()];
            if self.rooted.contains(&local) || from.is_empty() {
                roots.push(local);
            }
            stack.extend(from.iter().copied());
        }
        roots.sort_unstable();
        roots
    }

    /// Every local the value in `local` came through.
    fn ancestors(&self, local: mir::Local, out: &mut FxHashSet<mir::Local>) {
        let mut current = Some(local);
        while let Some(local) = current {
            if !out.insert(local) {
                break;
            }
            current = self.source[local.as_usize()];
        }
    }
}

/// Whether a value of type `ty`, which can hold a `message`, can also hold
/// none: on the way down to the message some enum has a variant with no
/// room for one (`Option`, `Result`, `Admit::Skip`), at any depth: in a
/// field, a tuple, behind a `Box`. A struct or a tuple around the message
/// always carries it.
fn may_lack<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>, message: Ty<'tcx>, depth: usize) -> bool {
    if ty == message || depth > 6 {
        return false;
    }
    let names = |ty: Ty<'tcx>| names_message(tcx, ty, message, 0);
    match *ty.kind() {
        ty::Adt(adt, args) => {
            let fields = |variant: &ty::VariantDef| -> Vec<Ty<'tcx>> {
                variant.fields.iter().map(|field| field.ty(tcx, args).skip_norm_wip()).collect()
            };
            // A std pointer or collection keeps what it holds out of its
            // fields' types: read its arguments.
            let hidden = crate::def_is_in_sysroot_resident_crate(tcx, adt.did())
                && !adt.all_fields().any(|field| names(field.ty(tcx, args).skip_norm_wip()));
            if hidden {
                return args
                    .types()
                    .any(|arg| names(arg) && may_lack(tcx, arg, message, depth + 1));
            }
            (adt.is_enum()
                && adt.variants().iter().any(|variant| !fields(variant).into_iter().any(names)))
                || adt.variants().iter().any(|variant| {
                    fields(variant)
                        .into_iter()
                        .any(|field| names(field) && may_lack(tcx, field, message, depth + 1))
                })
        }
        ty::Tuple(fields) => {
            fields.iter().any(|field| names(field) && may_lack(tcx, field, message, depth + 1))
        }
        ty::Ref(_, inner, _) | ty::RawPtr(inner, _) | ty::Array(inner, _) | ty::Slice(inner) => {
            may_lack(tcx, inner, message, depth + 1)
        }
        _ => false,
    }
}

/// Whether a value of type `ty` can hold a `message`: the type names it
/// (`Option<Wake>`, `(u8, Wake)`), or is, or is built from, one of the
/// crate's own types with a field that does (`enum Admit { Run(Wake), Skip }`,
/// a wrapper that names the message in no type argument, an `Rc` of one).
fn names_message<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>, message: Ty<'tcx>, depth: usize) -> bool {
    let ty = tcx.erase_and_anonymize_regions(ty);
    // Every type the type is built from, with the fields of the crate's own
    // types wherever one appears (`Rc<Stamped>`, `(u32, Admit)`).
    ty.walk().any(|arg| {
        let GenericArgKind::Type(part) = arg.kind() else { return false };
        part == message
            || match *part.kind() {
                ty::Adt(adt, args) if adt.did().is_local() && depth < 3 => {
                    adt.all_fields().any(|field| {
                        names_message(tcx, field.ty(tcx, args).skip_norm_wip(), message, depth + 1)
                    })
                }
                _ => false,
            }
    })
}

/// Which locals of `body` are the message it holds: its by-value parameters of
/// the message type (`seeds`, when given, names the ones a caller hands the
/// message it holds; another parameter of the type is a value the caller
/// built), or what a std receive returns, and from there ONLY what is that
/// same value: a move or copy of it, a reference to it, a field of a tuple or
/// aggregate built with it, what a wrapper around it unwraps to, the result of
/// code outside the crate given a wrapper or a reference to it
/// (`Result::unwrap`, `Clone::clone`) or the message and no other value of its
/// type (`Box::new`), and the result of a local fn given it by value that
/// `hands_back` says returns its parameter (a filter).
///
/// Not the message: its payload (a field of the message is a new value, even
/// one of the same type), a value computed from it, the result of outside
/// code given the message beside another value of its type (`mem::replace`
/// returns the OLD value), what a local fn returns that does not return its
/// parameter, and a local once a `&mut` of it went to outside code
/// (`mem::swap`, `mem::take`). Locals are classed once for the whole body, not
/// per program point: one assigned the message on one path and another value
/// on another counts as the message.
fn held_message<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
    message: Ty<'tcx>,
    subst: Option<GenericArgs<'tcx>>,
    seeds: Option<&FxHashSet<usize>>,
    hands_back: &mut dyn FnMut(LocalDefId, GenericArgs<'tcx>, usize) -> Back,
) -> Held<'tcx> {
    let erased = |ty: Ty<'tcx>| at_instance(tcx, subst, ty);
    let known: std::cell::RefCell<FxHashMap<Ty<'tcx>, bool>> = Default::default();
    let mentions = |ty: Ty<'tcx>| {
        let ty = erased(ty);
        *known.borrow_mut().entry(ty).or_insert_with(|| names_message(tcx, ty, message, 0))
    };
    // What a destination of type `ty` is when it is given the message.
    let given = |ty: Ty<'tcx>| {
        if erased(ty) == message {
            Hold::Is
        } else if mentions(ty) {
            Hold::Wraps
        } else {
            Hold::No
        }
    };
    let count = body.local_decls.len();
    let mut held = Held {
        subst,
        locals: vec![Hold::No; count],
        fields: FxHashMap::default(),
        source: vec![None; count],
        sources: vec![Vec::new(); count],
        rooted: FxHashSet::default(),
        filters: Vec::new(),
        rewritten: FxHashSet::default(),
        clobbered: FxHashSet::default(),
    };
    for local in body.args_iter() {
        let ty = body.local_decls[local].ty;
        // The message; or, in a body a caller hands it to, a wrapper of it
        // in the parameter that caller named (`m: Box<Msg>`).
        let hold = if erased(ty) == message {
            Hold::Is
        } else if seeds.is_some_and(|seeds| seeds.contains(&local.as_usize())) && mentions(ty) {
            Hold::Wraps
        } else {
            Hold::No
        };
        if hold != Hold::No && seeds.is_none_or(|seeds| seeds.contains(&local.as_usize())) {
            held.locals[local.as_usize()] = hold;
            held.rooted.insert(local);
        }
    }
    let bare = |place: mir::Place<'tcx>| place.projection.is_empty().then_some(place.local);
    // The `&mut` borrows of whole locals, for `clobbered`: taken of the
    // local, or made from such a borrow by a reborrow or a move (MIR passes
    // `&mut *r`, not `r`).
    let mut exclusive: FxHashMap<mir::Local, mir::Local> = FxHashMap::default();
    loop {
        let mut grew = false;
        for data in body.basic_blocks.iter() {
            for statement in &data.statements {
                let mir::StatementKind::Assign(assign) = &statement.kind else { continue };
                let (target, rvalue) = &**assign;
                let Some(target) = bare(*target) else { continue };
                let of = match rvalue {
                    mir::Rvalue::Ref(_, mir::BorrowKind::Mut { .. }, place)
                    | mir::Rvalue::RawPtr(mir::RawPtrKind::Mut, place) => {
                        match place.projection.as_slice() {
                            [] => Some(place.local),
                            [mir::ProjectionElem::Deref] => exclusive.get(&place.local).copied(),
                            _ => None,
                        }
                    }
                    mir::Rvalue::Use(mir::Operand::Move(place) | mir::Operand::Copy(place), _) => {
                        bare(*place).and_then(|from| exclusive.get(&from).copied())
                    }
                    _ => None,
                };
                if let Some(of) = of {
                    grew |= exclusive.insert(target, of).is_none();
                }
            }
        }
        if !grew {
            break;
        }
    }
    loop {
        let mut grew = false;
        for (block, data) in body.basic_blocks.iter_enumerated() {
            for statement in &data.statements {
                let mir::StatementKind::Assign(assign) = &statement.kind else { continue };
                let (target, rvalue) = &**assign;
                // A message stored into a field of a value the body holds
                // (`run.tail = next`): the field is that message too.
                if let (
                    [mir::ProjectionElem::Field(field, _)],
                    mir::Rvalue::Use(mir::Operand::Copy(from) | mir::Operand::Move(from), _),
                ) = (target.projection.as_slice(), rvalue)
                {
                    if let Some(from) = bare(*from) {
                        if held.locals[from.as_usize()] != Hold::No {
                            grew |= held.build(target.local, field.as_usize(), from);
                        }
                    }
                }
                let Some(target) = bare(*target) else { continue };
                let ty = body.local_decls[target].ty;
                let (hold, sources) = match rvalue {
                    mir::Rvalue::Use(mir::Operand::Copy(place) | mir::Operand::Move(place), _)
                    | mir::Rvalue::CopyForDeref(place) => {
                        let base = held.locals[place.local.as_usize()];
                        // What a tuple's field was built from: the field
                        // itself, or a read through it (`(t.0 as Ok).0` of
                        // `(rx.recv(), rx.recv())` is the FIRST receive's
                        // message, and `t.1`'s the second's).
                        let built = held.read_from(*place);
                        let hold = match (base, place.projection.as_slice()) {
                            (base, []) => base,
                            _ if held.is_message(tcx, body, *place, message) => Hold::Is,
                            (_, [mir::ProjectionElem::Field(field, _)])
                                if held
                                    .built(place.local, *field)
                                    .iter()
                                    .any(|local| held.locals[local.as_usize()] == Hold::Refers) =>
                            {
                                Hold::Refers
                            }
                            // What a wrapper unwraps to, short of the
                            // message's own payload.
                            (Hold::Wraps, [_, ..])
                                if !held.into_payload(tcx, body, *place, message) =>
                            {
                                given(ty)
                            }
                            _ => Hold::No,
                        };
                        (hold, built)
                    }
                    mir::Rvalue::Ref(_, _, place) | mir::Rvalue::RawPtr(_, place) => {
                        // A reference to a wrapper, or a reborrow of one
                        // (`&mut *iter`, as a `for` loop makes).
                        let wrapper = match place.projection.as_slice() {
                            [] | [mir::ProjectionElem::Deref] => {
                                held.locals[place.local.as_usize()] == Hold::Wraps
                            }
                            _ => false,
                        };
                        let hold = if held.is_message(tcx, body, *place, message) {
                            Hold::Refers
                        } else if wrapper {
                            Hold::Wraps
                        } else {
                            Hold::No
                        };
                        // (`ref first` out of `(rx.recv(), rx.recv())`: a
                        // reference to the first receive's message.)
                        (hold, held.read_from(*place))
                    }
                    // The pointer read out of a `Box` to dereference it (`*b`
                    // after deref elaboration), or a pointer to the message
                    // cast to another pointer type: to what it pointed to.
                    mir::Rvalue::Cast(_, operand, cast_ty) => {
                        let Some(place) = operand.place() else { continue };
                        let pointee = match *erased(*cast_ty).kind() {
                            ty::RawPtr(pointee, _) | ty::Ref(_, pointee, _) => pointee,
                            _ => continue,
                        };
                        let hold = match held.locals[place.local.as_usize()] {
                            Hold::Wraps if !place.projection.is_empty() && pointee == message => {
                                Hold::Refers
                            }
                            Hold::Refers if place.projection.is_empty() && pointee == message => {
                                Hold::Refers
                            }
                            _ => Hold::No,
                        };
                        (hold, vec![place.local])
                    }
                    mir::Rvalue::Aggregate(_, operands) => {
                        let mut built = None;
                        for (index, operand) in operands.iter().enumerate() {
                            let Some(local) = operand.place().and_then(bare) else { continue };
                            match held.locals[local.as_usize()] {
                                Hold::Is => {
                                    built = Some(local);
                                    grew |= held.build(target, index, local);
                                }
                                // `(&state, &msg)`: read back through the field.
                                Hold::Refers => {
                                    grew |= held.build(target, index, local);
                                }
                                // A wrapper around a wrapper (`(rx.recv(),
                                // state)`, `Some((seq, m))`) is one; beside
                                // another value of the type (`(rx.recv(),
                                // &last)`) it is read back through its field.
                                Hold::Wraps => {
                                    built = Some(local);
                                    grew |= held.build(target, index, local);
                                }
                                Hold::No => {}
                            }
                        }
                        // A wrapper (`Some(wake)`, `Admit::Run(wake)`,
                        // `(id, wake)`) holds the message and no other value
                        // of its type. `(prev, wake)` holds two, which are
                        // told apart by field.
                        let of_type = operands
                            .iter()
                            .filter(|operand| mentions(operand.ty(body, tcx)))
                            .count();
                        match built {
                            Some(local) if of_type == 1 => (given(ty), vec![local]),
                            _ => continue,
                        }
                    }
                    _ => continue,
                };
                if hold == Hold::No {
                    continue;
                }
                if held.locals[target.as_usize()] == Hold::No {
                    held.locals[target.as_usize()] = hold;
                    held.source[target.as_usize()] = sources.first().copied();
                    grew = true;
                }
                for source in sources {
                    if source != target && !held.sources[target.as_usize()].contains(&source) {
                        held.sources[target.as_usize()].push(source);
                        grew = true;
                    }
                }
            }
            let Some(mir::Terminator {
                kind: TerminatorKind::Call { func, args, destination, .. },
                ..
            }) = &data.terminator
            else {
                continue;
            };
            let Some((callee, callee_args)) = func.const_fn_def() else { continue };
            let callee_args = at_instance(tcx, subst, callee_args);
            // The body that runs: a trait method's impl, where it is known.
            let (run, run_args) = run_instance_by_call(tcx, body, callee, callee_args)
                .unwrap_or((callee, callee_args));
            let hold_of = |arg: &rustc_span::Spanned<mir::Operand<'tcx>>| {
                arg.node.place().and_then(bare).map(|local| (held.locals[local.as_usize()], local))
            };
            // A clone of the message is the message, whichever impl runs: a
            // derived one is a local body that builds each variant anew, which
            // no reading of that body would call handing its parameter back.
            let outside = !run.is_local()
                || tcx
                    .trait_of_assoc(callee)
                    .is_some_and(|trait_def| tcx.lang_items().clone_trait() == Some(trait_def));
            // A `&mut` of a held local handed to a call: the local is what
            // that code leaves there (`mem::swap`, `mem::take`, a local
            // helper that does either).
            {
                let lent: Vec<mir::Local> = args
                    .iter()
                    .filter_map(|arg| arg.node.place().and_then(bare))
                    .filter_map(|local| exclusive.get(&local).copied())
                    .filter(|of| held.locals[of.as_usize()] == Hold::Is)
                    .collect();
                for of in lent {
                    grew |= held.clobbered.insert(of);
                }
            }
            let Some(target) = bare(*destination) else { continue };
            // A local already classed still learns where else it gets a
            // message from.
            let classed = held.locals[target.as_usize()] != Hold::No;
            let ty = body.local_decls[target].ty;
            let (hold, source, filter) = if drains_message(tcx, callee, callee_args)
                .is_some_and(|drained| erased(drained) == message)
            {
                (given(ty), None, None)
            } else if outside {
                // Code outside the crate unwraps a wrapper or copies through
                // a reference (`Result::unwrap`, `Clone::clone`), or wraps the
                // message (`Box::new`). Given the message beside another
                // value of its type, it can return that one (`mem::replace`
                // returns the OLD value).
                let inner = args.iter().filter_map(hold_of).find_map(|(hold, local)| {
                    matches!(hold, Hold::Wraps | Hold::Refers).then_some(local)
                });
                let whole = args
                    .iter()
                    .filter_map(hold_of)
                    .find_map(|(hold, local)| (hold == Hold::Is).then_some(local));
                let only = args.iter().all(|arg| {
                    !mentions(arg.node.ty(body, tcx))
                        || hold_of(arg).is_some_and(|(hold, _)| hold != Hold::No)
                });
                // Given a callable that takes the message and returns one
                // (`map`, `and_then`), or an adapter built with one
                // (`Iterator::next` on a `Map`): the message goes into the
                // callable, and the result is what the callable made.
                if args
                    .iter()
                    .any(|arg| remakes_message(tcx, erased(arg.node.ty(body, tcx)), message))
                {
                    continue;
                }
                match (inner, whole) {
                    (Some(local), _) => (given(ty), Some(local), None),
                    (None, Some(local)) if only => (given(ty), Some(local), None),
                    _ => continue,
                }
            } else {
                // The held argument, with the callee's parameter it becomes.
                let from = args.iter().enumerate().find_map(|(position, arg)| {
                    hold_of(arg)
                        .filter(|(hold, _)| *hold == Hold::Is)
                        .map(|(_, local)| (position + 1, local))
                });
                let local_fn = run
                    .as_local()
                    .filter(|run| matches!(tcx.def_kind(*run), DefKind::Fn | DefKind::AssocFn));
                let back = match (from, local_fn) {
                    (Some((param, _)), Some(local_fn)) if mentions(ty) => {
                        hands_back(local_fn, run_args, param)
                    }
                    _ => Back::No,
                };
                match (from, back) {
                    (_, Back::No) | (None, _) => continue,
                    (Some((_, local)), back) => {
                        // The result can lack the message when its type is an
                        // enum with room for none (`Option`, `Admit::Skip`);
                        // a struct or a tuple around it always carries it.
                        let lacks = may_lack(tcx, erased(ty), message, 0);
                        let kind = match (back, lacks) {
                            (Back::Rewrites, _) => Filter::MayRewrite,
                            (_, true) => Filter::MayDrop,
                            (_, false) => Filter::Passes,
                        };
                        (given(ty), Some(local), Some((run, kind)))
                    }
                }
            };
            if hold == Hold::No {
                continue;
            }
            if !classed {
                held.locals[target.as_usize()] = hold;
                held.source[target.as_usize()] = source;
                if let Some((callee, kind)) = filter {
                    held.filters.push((target, callee, kind));
                }
                grew = true;
            }
            // What a rewriting callee returns is a message of its own: any
            // variant, whatever a switch before the call found.
            let rewrites = matches!(filter, Some((_, Filter::MayRewrite)));
            if rewrites {
                grew |= held.rewritten.insert(block);
            }
            let source = if rewrites { None } else { source };
            match source {
                Some(source) if source != target => {
                    if !held.sources[target.as_usize()].contains(&source) {
                        held.sources[target.as_usize()].push(source);
                        grew = true;
                    }
                }
                Some(_) => {}
                None => grew |= held.rooted.insert(target),
            }
        }
        if !grew {
            break;
        }
    }
    held
}

/// Whether the local fn `callee` hands the message it is given back: its
/// return value is the message parameter or a wrapper around it
/// ([`held_message`] over its own body). A fn that takes a message and returns
/// another one (a lookup, a default) does not.
fn hands_back<'tcx>(
    tcx: TyCtxt<'tcx>,
    hooks: &dyn CensusHooks<'tcx>,
    bodies: &FxHashSet<LocalDefId>,
    memo: &mut HandsBack<'tcx>,
    callee: LocalDefId,
    args: GenericArgs<'tcx>,
    message: Ty<'tcx>,
    param: Option<usize>,
) -> Back {
    // A generic callee is read at the instance the call names
    // (`fn traced<T>(v: T) -> T` given the message); one whose arguments are
    // not known where it is called, at its own parameters.
    let subst = (!args.has_non_region_param() && !args.is_empty()).then_some(args);
    let key = (callee, subst, message, param);
    if let Some(&known) = memo.get(&key) {
        return known;
    }
    // A cycle answers no.
    memo.insert(key, Back::No);
    if !bodies.contains(&callee) {
        return Back::No;
    }
    let mut result = Back::No;
    hooks.with_local_body(callee, &mut |body| {
        let seeds: Option<FxHashSet<usize>> = param.map(|param| FxHashSet::from_iter([param]));
        let held = held_message(
            tcx,
            body,
            message,
            subst,
            seeds.as_ref(),
            &mut |inner, inner_args, inner_param| {
                hands_back(tcx, hooks, bodies, memo, inner, inner_args, message, Some(inner_param))
            },
        );
        let is_held = |local: mir::Local| held.locals[local.as_usize()] != Hold::No;
        let mentions = |ty: Ty<'tcx>| names_message(tcx, at_instance(tcx, subst, ty), message, 0);
        // The locals some path gives ANOTHER value that can hold a message:
        // one built here, another parameter's, a call's result that the
        // given message is no part of. Through moves, to a fixpoint.
        // (A local every assignment of which builds a wrapper with nothing
        // in it, `None`, holds no message at all.)
        let mut built: FxHashMap<mir::Local, bool> = FxHashMap::default();
        for data in body.basic_blocks.iter() {
            for statement in &data.statements {
                let mir::StatementKind::Assign(assign) = &statement.kind else { continue };
                let (target, rvalue) = &**assign;
                if !target.projection.is_empty() {
                    continue;
                }
                let empty = matches!(rvalue, mir::Rvalue::Aggregate(_, operands)
                    if at_instance(tcx, subst, rvalue.ty(body, tcx)) != message
                        && !operands.iter().any(|operand| mentions(operand.ty(body, tcx))));
                let slot = built.entry(target.local).or_insert(true);
                *slot &= empty;
            }
            if let Some(mir::Terminator {
                kind: TerminatorKind::Call { destination, .. }, ..
            }) = &data.terminator
            {
                built.insert(destination.local, false);
            }
        }
        let vacant = |local: mir::Local| built.get(&local).copied().unwrap_or(false);
        let mut other: FxHashSet<mir::Local> = FxHashSet::default();
        loop {
            let mut grew = false;
            for data in body.basic_blocks.iter() {
                for statement in &data.statements {
                    let mir::StatementKind::Assign(assign) = &statement.kind else { continue };
                    let (target, rvalue) = &**assign;
                    if !target.projection.is_empty() || other.contains(&target.local) {
                        continue;
                    }
                    let another = |operand: &mir::Operand<'tcx>| match operand.place() {
                        Some(place) => {
                            mentions(place.ty(body, tcx).ty)
                                && !vacant(place.local)
                                && (!is_held(place.local) || other.contains(&place.local))
                        }
                        None => mentions(operand.ty(body, tcx)),
                    };
                    let is_other = match rvalue {
                        mir::Rvalue::Use(operand, _) => another(operand),
                        mir::Rvalue::CopyForDeref(place) => {
                            mentions(place.ty(body, tcx).ty)
                                && (!is_held(place.local) || other.contains(&place.local))
                        }
                        mir::Rvalue::Aggregate(_, operands) => {
                            at_instance(tcx, subst, rvalue.ty(body, tcx)) == message
                                || operands.iter().any(|operand| another(operand))
                        }
                        mir::Rvalue::Ref(..) | mir::Rvalue::RawPtr(..) => false,
                        _ => mentions(rvalue.ty(body, tcx)),
                    };
                    if is_other {
                        grew |= other.insert(target.local);
                    }
                }
                if let Some(mir::Terminator {
                    kind: TerminatorKind::Call { args, destination, .. },
                    ..
                }) = &data.terminator
                {
                    let given = args
                        .iter()
                        .any(|arg| arg.node.place().is_some_and(|place| is_held(place.local)));
                    if destination.projection.is_empty()
                        && !given
                        && mentions(body.local_decls[destination.local].ty)
                    {
                        grew |= other.insert(destination.local);
                    }
                }
            }
            if !grew {
                break;
            }
        }
        // It hands the message back when what it returns is the message it
        // was given, or a wrapper around it: on every path that returns one,
        // or on some.
        let returned = matches!(held.locals[mir::RETURN_PLACE.as_usize()], Hold::Is | Hold::Wraps);
        result = match (returned, other.contains(&mir::RETURN_PLACE)) {
            (false, _) => Back::No,
            (true, false) => Back::Yes,
            (true, true) => Back::Rewrites,
        };
    });
    memo.insert(key, result);
    result
}

/// [`hands_back`]'s answers: by callee, instance, message and the parameter
/// given the message (`None`: any by-value parameter of the type).
type HandsBack<'tcx> =
    FxHashMap<(LocalDefId, Option<GenericArgs<'tcx>>, Ty<'tcx>, Option<usize>), Back>;

/// Whether a callee given the message returns it ([`hands_back`]).
#[derive(Clone, Copy, PartialEq, Eq)]
enum Back {
    /// Never: what it returns holds another value, or none (a reply).
    No,
    /// On every path that returns one: a filter on the message's way.
    Yes,
    /// On some paths, and another value of the type on others (a relay
    /// unwrapped, a variant rewritten): what comes back is still dispatched
    /// as the message, as any variant, and the callee is a place the message
    /// goes as well.
    Rewrites,
}

/// What a local fn on the held message's way does with it.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Filter {
    Passes,
    MayDrop,
    MayRewrite,
}

/// How a consumer's body dispatches on the message it holds.
struct Dispatch {
    /// Per block, the variants the held message can be when it runs: whole
    /// at entry and where a new message is received, one variant in an arm
    /// of a switch over the held message (the innermost such switch decides),
    /// what is left in its `otherwise`, joined where paths meet. A block
    /// several arms reach has their union, and one every variant reaches (the
    /// code before the dispatch, after it, a drain loop's header) has all.
    live: Vec<VariantSet>,
    /// Each arm: the block an explicit switch target leads to, the variants
    /// it is the target of, and where its switch is in source.
    arms: Vec<(mir::BasicBlock, Vec<usize>, Span)>,
    /// The variants some switch gives a target of their own.
    armed: VariantSet,
    /// Whether some switch over the message has a reachable `otherwise`.
    catch_all: bool,
    /// The variants the compiler found cannot occur: those a switch whose
    /// `otherwise` is unreachable (an exhaustive `match`) gives no target.
    impossible: VariantSet,
    /// The local calls the held message passes through on its way to a
    /// switch: (name, whether the result can lack it).
    filters: Vec<(String, Filter)>,
    /// Switches in the body over another value of the message's type (a
    /// payload, a field, a second message), which are not counted.
    others: usize,
    /// The variants that can reach a switch that gives them a target: an arm
    /// for any other can take no message (an earlier switch, here or in the
    /// caller, took the variant).
    arriving: VariantSet,
    /// Per message the body holds ([`Held::roots`]) that some switch reads:
    /// the variants THAT message can be at each block. `live` is the whole
    /// body's answer, where the innermost switch decides whichever message it
    /// reads; a body that holds two (two receives, two parameters) narrows
    /// each by its own switches only.
    by_root: Vec<(mir::Local, Vec<VariantSet>)>,
    /// The blocks that give a held local another value.
    reset: FxHashSet<mir::BasicBlock>,
}

impl Dispatch {
    /// The variants the message in `locals` can be at `block`: by the
    /// switches over that message, or, when none reads it, what it came in
    /// as (`entry` for a parameter, any variant for a receive).
    fn at<'tcx>(
        found: Option<&Dispatch>,
        body: &mir::Body<'tcx>,
        held: &Held<'tcx>,
        entry: &VariantSet,
        block: mir::BasicBlock,
        locals: &[mir::Local],
    ) -> VariantSet {
        if locals.is_empty() {
            return entry.clone();
        }
        if found.is_some_and(|found| found.reset.contains(&block)) {
            return VariantSet::all(entry.len);
        }
        let mut set = VariantSet::none(entry.len);
        for &local in locals {
            for root in held.roots(local) {
                let flow =
                    found.and_then(|found| found.by_root.iter().find(|(seen, _)| *seen == root));
                match flow {
                    Some((_, live)) => {
                        set.union(&live[block.as_usize()]);
                    }
                    None if (1..=body.arg_count).contains(&root.as_usize()) => {
                        set.union(entry);
                    }
                    None => return VariantSet::all(entry.len),
                }
            }
        }
        set
    }
}

/// [`Dispatch`] for `body` and the message `held` in it, or `None` when the
/// body never switches over that message.
///
/// A switch counts when it reads the discriminant of the held message
/// ([`Held::is_message`]) in source: not on an unwind path, and not one drop
/// elaboration made to drop a partly moved value (those carry the drop's own
/// source position).
fn dispatch<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
    message: Ty<'tcx>,
    adt: ty::AdtDef<'tcx>,
    held: &Held<'tcx>,
    entry: &VariantSet,
) -> Option<Dispatch> {
    let erased = |ty: Ty<'tcx>| at_instance(tcx, held.subst, ty);
    let count = adt.variants().len();
    let callee_of = |terminator: &mir::Terminator<'tcx>| match &terminator.kind {
        TerminatorKind::Call { func, .. } => func.const_fn_def(),
        _ => None,
    };
    let variant_of = |value: u128| {
        adt.discriminants(tcx).find(|(_, discr)| discr.val == value).map(|(v, _)| v.as_usize())
    };
    let drops: FxHashSet<(Span, mir::SourceScope)> = body
        .basic_blocks
        .iter()
        .filter_map(|data| data.terminator.as_ref())
        .filter(|terminator| matches!(terminator.kind, TerminatorKind::Drop { .. }))
        .map(|terminator| (terminator.source_info.span, terminator.source_info.scope))
        .collect();
    // The switches over the held message: targets by variant, `otherwise`,
    // the local the message was read from, and the switch's place in source.
    type Switch = (Vec<(usize, mir::BasicBlock)>, mir::BasicBlock, Vec<mir::Local>, Span);
    let mut switches: FxHashMap<mir::BasicBlock, Switch> = FxHashMap::default();
    let mut others = 0;
    for (block, data) in body.basic_blocks.iter_enumerated() {
        let Some(terminator) = &data.terminator else { continue };
        let TerminatorKind::SwitchInt { discr, targets } = &terminator.kind else { continue };
        let Some(tested) = discr.place().filter(|place| place.projection.is_empty()) else {
            continue;
        };
        let read = data.statements.iter().find_map(|statement| {
            let mir::StatementKind::Assign(assign) = &statement.kind else { return None };
            let (target, rvalue) = &**assign;
            let mir::Rvalue::Discriminant(place) = rvalue else { return None };
            (target.local == tested.local && erased(place.ty(body, tcx).ty) == message)
                .then_some(*place)
        });
        let Some(read) = read else { continue };
        let source = (terminator.source_info.span, terminator.source_info.scope);
        if data.is_cleanup || drops.contains(&source) {
            continue;
        }
        if !held.is_message(tcx, body, read, message) {
            others += 1;
            continue;
        }
        let explicit: Vec<(usize, mir::BasicBlock)> = targets
            .iter()
            .filter_map(|(value, target)| Some((variant_of(value)?, target)))
            .collect();
        // The local the message was read from: for a tuple's field, also
        // one read in place through a wrapper in it (`(t.0 as Ok).0` of
        // `match (rx.recv(), rx.recv())`), the one moved into it.
        let origin = held.read_from(read);
        switches
            .insert(block, (explicit, targets.otherwise(), origin, terminator.source_info.span));
    }
    if switches.is_empty() {
        // A message with one variant has no switch to find (an irrefutable
        // match compiles to none). Its arm is the code that runs with the
        // message in hand: from where the body takes it out of what it came
        // in (`Ok(m)`) or reads its payload (`Msg::Only(k)`), or from entry
        // for a parameter, up to the next receive. Code before the first
        // receive and after the loop is outside it.
        if count != 1 {
            return None;
        }
        let holds = |local: mir::Local| {
            held.locals[local.as_usize()] == Hold::Is && !held.clobbered.contains(&local)
        };
        let mut taken: Vec<(mir::BasicBlock, Span)> = Vec::new();
        let mut reads_payload = false;
        let mut payload_at: Option<(mir::BasicBlock, Span)> = None;
        let held_at_entry = body.args_iter().any(|local| holds(local));
        for (block, data) in body.basic_blocks.iter_enumerated() {
            if data.is_cleanup {
                continue;
            }
            for statement in &data.statements {
                let mir::StatementKind::Assign(assign) = &statement.kind else { continue };
                let (target, rvalue) = &**assign;
                let place = match rvalue {
                    mir::Rvalue::Use(mir::Operand::Copy(place) | mir::Operand::Move(place), _)
                    | mir::Rvalue::CopyForDeref(place)
                    | mir::Rvalue::Ref(_, _, place)
                    | mir::Rvalue::Discriminant(place) => *place,
                    _ => continue,
                };
                // A read below the message: some shorter prefix is it.
                let payload = (0..place.projection.len()).any(|len| {
                    let prefix = tcx.mk_place_elems(&place.projection[..len]);
                    held.is_message(
                        tcx,
                        body,
                        mir::Place { local: place.local, projection: prefix },
                        message,
                    )
                });
                // The message taken out of its wrapper into a local.
                let whole = !place.projection.is_empty()
                    && target.projection.is_empty()
                    && holds(target.local)
                    && held.is_message(tcx, body, place, message);
                if payload || whole {
                    reads_payload |= payload;
                    taken.push((block, statement.source_info.span));
                    if payload && payload_at.is_none() {
                        payload_at = Some((block, statement.source_info.span));
                    }
                }
            }
            // The success edge of a switch over what the message came in
            // (`Ok(..)`, `Some(..)`): there the body has it, whether or not
            // it reads anything of it (`while let Ok(Wake::Tick) = ..`).
            let Some(mir::Terminator {
                kind: TerminatorKind::SwitchInt { discr, targets },
                source_info,
                ..
            }) = &data.terminator
            else {
                continue;
            };
            let Some(tested) = discr.place().filter(|place| place.projection.is_empty()) else {
                continue;
            };
            let wrapper = data.statements.iter().find_map(|statement| {
                let mir::StatementKind::Assign(assign) = &statement.kind else { return None };
                let (target, rvalue) = &**assign;
                let mir::Rvalue::Discriminant(place) = rvalue else { return None };
                (target.local == tested.local
                    && place.projection.is_empty()
                    && held.locals[place.local.as_usize()] == Hold::Wraps)
                    .then(|| erased(place.ty(body, tcx).ty))
            });
            let Some(ty::Adt(wrapper, wrapper_args)) = wrapper.map(|ty| *ty.kind()) else {
                continue;
            };
            if !wrapper.is_enum() {
                continue;
            }
            let carries = |variant: rustc_abi::VariantIdx| {
                wrapper.variant(variant).fields.iter().any(|field| {
                    names_message(tcx, field.ty(tcx, wrapper_args).skip_norm_wip(), message, 0)
                })
            };
            let mut named: FxHashSet<rustc_abi::VariantIdx> = FxHashSet::default();
            for (value, target) in targets.iter() {
                let Some((variant, _)) =
                    wrapper.discriminants(tcx).find(|(_, discr)| discr.val == value)
                else {
                    continue;
                };
                named.insert(variant);
                if carries(variant) {
                    taken.push((target, source_info.span));
                }
            }
            let unreachable = matches!(
                body.basic_blocks[targets.otherwise()].terminator.as_ref().map(|t| &t.kind),
                Some(TerminatorKind::Unreachable)
            );
            if !unreachable
                && wrapper
                    .variants()
                    .indices()
                    .any(|variant| !named.contains(&variant) && carries(variant))
            {
                taken.push((targets.otherwise(), source_info.span));
            }
        }
        if taken.is_empty() && !held_at_entry {
            return None;
        }
        // A body that only passes the message on is not where it goes: to a
        // body of the crate, through the Fn traits, or into another channel.
        // (One that gives it to other code outside the crate, `Vec::push`,
        // `drop`, is where it ends.)
        let passes_on = body.basic_blocks.iter().any(|data| {
            let Some(mir::Terminator { kind: TerminatorKind::Call { func, args, .. }, .. }) =
                &data.terminator
            else {
                return false;
            };
            let given = args.iter().filter_map(|arg| arg.node.place()).any(|place| {
                place.projection.is_empty()
                    && (holds(place.local)
                        || held.fields.iter().any(|(&(tuple, _), built)| {
                            tuple == place.local && built.iter().any(|from| holds(*from))
                        }))
            });
            if !given {
                return false;
            }
            let Some((callee, callee_args)) = func.const_fn_def() else { return true };
            let callee_args = at_instance(tcx, held.subst, callee_args);
            run_by_call(tcx, body, callee, callee_args).unwrap_or(callee).is_local()
                || tcx
                    .trait_of_assoc(callee)
                    .is_some_and(|trait_def| tcx.fn_trait_kind_from_def_id(trait_def).is_some())
                || is_std_channel_send(tcx, callee)
        });
        if passes_on && !reads_payload {
            return None;
        }
        let mut only = VariantSet::none(count);
        if entry.contains(0) {
            only.insert(0);
        }
        let receives = |block: mir::BasicBlock| {
            body.basic_blocks[block]
                .terminator
                .as_ref()
                .and_then(|terminator| callee_of(terminator))
                .and_then(|(callee, callee_args)| {
                    receives_message(tcx, callee, at_instance(tcx, held.subst, callee_args))
                })
                .is_some_and(|ty| erased(ty) == message)
        };
        // Whether the message is in hand when a block runs, on EVERY way
        // into it: from where the body takes hold of it to the next receive.
        // A loop's head, reached with the message over the back edge and
        // with none from entry, is outside the arm; so is what follows the
        // loop.
        let begins: FxHashSet<mir::BasicBlock> = taken.iter().map(|(block, _)| *block).collect();
        let mut in_hand: Vec<Option<bool>> = vec![None; body.basic_blocks.len()];
        in_hand[mir::START_BLOCK.as_usize()] = Some(held_at_entry);
        let mut queue = VecDeque::from([mir::START_BLOCK]);
        while let Some(block) = queue.pop_front() {
            let here = in_hand[block.as_usize()].unwrap_or(false) || begins.contains(&block);
            let after = here && !receives(block);
            let Some(terminator) = &body.basic_blocks[block].terminator else { continue };
            for to in terminator.successors() {
                let next = match in_hand[to.as_usize()] {
                    None => after,
                    Some(known) => known && after,
                };
                if in_hand[to.as_usize()] != Some(next) {
                    in_hand[to.as_usize()] = Some(next);
                    queue.push_back(to);
                }
            }
        }
        let live: Vec<VariantSet> = body
            .basic_blocks
            .indices()
            .map(|block| {
                if in_hand[block.as_usize()].unwrap_or(false) || begins.contains(&block) {
                    only.clone()
                } else {
                    VariantSet::none(count)
                }
            })
            .collect();
        // The arm is named where the variant's pattern is: at a read of the
        // payload when there is one (`Msg::Only(k)`), else where the message
        // is taken in hand.
        let (first, span) =
            payload_at.or_else(|| taken.first().copied()).unwrap_or((mir::START_BLOCK, DUMMY_SP));
        return Some(Dispatch {
            live,
            arms: vec![(first, vec![0], span)],
            armed: VariantSet::all(count),
            catch_all: false,
            impossible: VariantSet::none(count),
            filters: Vec::new(),
            others,
            arriving: only,
            by_root: Vec::new(),
            reset: FxHashSet::default(),
        });
    }
    // A held local given another value (`m = Msg::Idle;`): from there on it
    // can be any variant, whatever a switch before it found.
    let mut reset: FxHashSet<mir::BasicBlock> = FxHashSet::default();
    for (block, data) in body.basic_blocks.iter_enumerated() {
        for statement in &data.statements {
            let mir::StatementKind::Assign(assign) = &statement.kind else { continue };
            let (target, rvalue) = &**assign;
            if !target.projection.is_empty() || held.locals[target.local.as_usize()] != Hold::Is {
                continue;
            }
            let from_held = match rvalue {
                mir::Rvalue::Use(mir::Operand::Copy(place) | mir::Operand::Move(place), _)
                | mir::Rvalue::CopyForDeref(place) => {
                    held.locals[place.local.as_usize()] != Hold::No
                }
                _ => false,
            };
            if !from_held {
                reset.insert(block);
            }
        }
    }
    reset.extend(held.rewritten.iter().copied());
    // The same per message: a switch narrows the message it reads and no
    // other, and only a variant that arrives enters its arm.
    let reads: FxHashMap<mir::BasicBlock, Vec<mir::Local>> = switches
        .iter()
        .map(|(block, (_, _, origin, _))| {
            let mut roots: Vec<mir::Local> =
                origin.iter().flat_map(|local| held.roots(*local)).collect();
            roots.sort_unstable();
            roots.dedup();
            (*block, roots)
        })
        .collect();
    let mut roots: Vec<mir::Local> = reads.values().flatten().copied().collect();
    roots.sort_unstable();
    roots.dedup();
    // One flow per message the body holds is messages x blocks: a body with
    // hundreds of receives gets none, and every variant is taken to arrive.
    let many = roots.len() > 64;
    if many {
        roots.clear();
    }
    let by_root: Vec<(mir::Local, Vec<VariantSet>)> = roots
        .into_iter()
        .map(|root| {
            let mut live = vec![VariantSet::none(count); body.basic_blocks.len()];
            live[mir::START_BLOCK.as_usize()] = if (1..=body.arg_count).contains(&root.as_usize()) {
                entry.clone()
            } else {
                VariantSet::all(count)
            };
            let mut queue = VecDeque::from([mir::START_BLOCK]);
            while let Some(block) = queue.pop_front() {
                let Some(terminator) = &body.basic_blocks[block].terminator else { continue };
                let here = if reset.contains(&block) {
                    VariantSet::all(count)
                } else {
                    live[block.as_usize()].clone()
                };
                let mut flow = |to: mir::BasicBlock, set: &VariantSet, queue: &mut VecDeque<_>| {
                    if live[to.as_usize()].union(set) {
                        queue.push_back(to);
                    }
                };
                match switches.get(&block) {
                    Some((explicit, otherwise, _, _)) if reads[&block] == [root] => {
                        let mut rest = here.clone();
                        for &(variant, target) in explicit {
                            if here.contains(variant) {
                                let mut one = VariantSet::none(count);
                                one.insert(variant);
                                flow(target, &one, &mut queue);
                            }
                            rest.remove(variant);
                        }
                        flow(*otherwise, &rest, &mut queue);
                    }
                    _ => {
                        let fresh = callee_of(terminator)
                            .and_then(|(callee, callee_args)| {
                                let callee_args = at_instance(tcx, held.subst, callee_args);
                                receives_message(tcx, callee, callee_args)
                            })
                            .is_some_and(|ty| erased(ty) == message);
                        let out = if fresh { VariantSet::all(count) } else { here };
                        for to in terminator.successors() {
                            flow(to, &out, &mut queue);
                        }
                    }
                }
            }
            (root, live)
        })
        .collect();
    // Whether `variant` can be what the switch at `block` reads.
    let arrives = |block: mir::BasicBlock, variant: usize| {
        many || reads[&block].iter().any(|root| {
            by_root
                .iter()
                .find(|(seen, _)| seen == root)
                .is_some_and(|(_, live)| live[block.as_usize()].contains(variant))
        })
    };
    // Forward, to a fixpoint: which variants the held message can be, for the
    // whole body. The innermost switch decides, whichever message it reads.
    let mut live = vec![VariantSet::none(count); body.basic_blocks.len()];
    live[mir::START_BLOCK.as_usize()] = entry.clone();
    let mut queue = VecDeque::from([mir::START_BLOCK]);
    while let Some(block) = queue.pop_front() {
        let data = &body.basic_blocks[block];
        let Some(terminator) = &data.terminator else { continue };
        let here = if reset.contains(&block) {
            VariantSet::all(count)
        } else {
            live[block.as_usize()].clone()
        };
        let mut flow = |to: mir::BasicBlock, set: &VariantSet, queue: &mut VecDeque<_>| {
            if live[to.as_usize()].union(set) {
                queue.push_back(to);
            }
        };
        if let Some((explicit, otherwise, _, _)) = switches.get(&block) {
            // In the arm for a variant the held message is that variant,
            // whatever an outer switch narrowed to: a body can hold two
            // messages (two parameters, a nested receive), and no block the
            // program can reach is left with no variant.
            // What is left for the `otherwise`: the variants the message
            // THIS switch reads can still be here, less its arms. `here` may
            // have been narrowed by a switch over another message the body
            // holds, whose variants say nothing of this one.
            let mut rest = VariantSet::none(count);
            for root in &reads[&block] {
                if let Some((_, own)) = by_root.iter().find(|(seen, _)| seen == root) {
                    rest.union(&own[block.as_usize()]);
                }
            }
            if rest.count() == 0 {
                rest = if many { here.clone() } else { VariantSet::all(count) };
            }
            for &(variant, target) in explicit {
                let mut one = VariantSet::none(count);
                one.insert(variant);
                rest.remove(variant);
                flow(target, &one, &mut queue);
            }
            if rest.count() == 0 {
                rest = VariantSet::all(count);
                for &(variant, _) in explicit {
                    rest.remove(variant);
                }
            }
            flow(*otherwise, &rest, &mut queue);
            continue;
        }
        // A receive brings a new message: any variant again.
        let fresh = callee_of(terminator)
            .and_then(|(callee, callee_args)| {
                receives_message(tcx, callee, at_instance(tcx, held.subst, callee_args))
            })
            .is_some_and(|ty| erased(ty) == message);
        let out = if fresh { VariantSet::all(count) } else { here };
        for to in terminator.successors() {
            flow(to, &out, &mut queue);
        }
    }
    // Each variant's arm: its target in the switch with the most targets
    // that the variant can arrive at (one an earlier `if let` took never
    // reaches the main match's arm for it), else in any switch.
    let mut ranked: Vec<(mir::BasicBlock, &Switch)> =
        switches.iter().map(|(block, switch)| (*block, switch)).collect();
    ranked.sort_by_key(|(block, (explicit, ..))| (std::cmp::Reverse(explicit.len()), *block));
    let mut armed = VariantSet::none(count);
    for (_, (explicit, ..)) in &ranked {
        for &(variant, _) in explicit {
            armed.insert(variant);
        }
    }
    let mut placed = VariantSet::none(count);
    let mut arms: Vec<(mir::BasicBlock, Vec<usize>, Span)> = Vec::new();
    for arriving in [true, false] {
        for (block, (explicit, _, _, span)) in &ranked {
            for &(variant, target) in explicit {
                if placed.contains(variant) || (arriving && !arrives(*block, variant)) {
                    continue;
                }
                placed.insert(variant);
                match arms.iter_mut().find(|(seen, _, _)| *seen == target) {
                    Some((_, variants, _)) => variants.push(variant),
                    None => arms.push((target, vec![variant], *span)),
                }
            }
        }
    }
    arms.sort_by_key(|(_, variants, _)| variants.iter().copied().min());
    let reachable = |block: mir::BasicBlock| {
        !matches!(
            body.basic_blocks[block].terminator.as_ref().map(|terminator| &terminator.kind),
            Some(TerminatorKind::Unreachable)
        )
    };
    let catch_all = switches.values().any(|(_, otherwise, _, _)| reachable(*otherwise));
    let mut impossible = VariantSet::none(count);
    for (explicit, otherwise, _, _) in switches.values() {
        if reachable(*otherwise) {
            continue;
        }
        for variant in 0..count {
            if !explicit.iter().any(|(seen, _)| *seen == variant) {
                impossible.insert(variant);
            }
        }
    }
    // The filters whose result reached a switch.
    let mut dispatched: FxHashSet<mir::Local> = FxHashSet::default();
    for (_, _, read, _) in switches.values() {
        for &local in read {
            held.ancestors(local, &mut dispatched);
        }
    }
    let mut filters: Vec<(String, Filter)> = Vec::new();
    for &(result, callee, keeps) in &held.filters {
        let name = tcx.def_path_str(callee);
        if dispatched.contains(&result) && !filters.iter().any(|(seen, _)| *seen == name) {
            filters.push((name, keeps));
        }
    }
    let mut arriving = VariantSet::none(count);
    for (block, (explicit, ..)) in &switches {
        for &(variant, _) in explicit {
            if arrives(*block, variant) {
                arriving.insert(variant);
            }
        }
    }
    Some(Dispatch {
        live,
        arms,
        armed,
        catch_all,
        impossible,
        filters,
        others,
        arriving,
        by_root,
        reset,
    })
}

/// Where `def`'s source matches on variants of `adt`: for each `match`,
/// `if let` and `let ... else`, its span and, per arm, the variants its pattern
/// names with the pattern's span. MIR gives an arm's first block, which for an
/// arm with no code of its own (`Msg::Stop => continue`) is wherever the jump
/// lands.
fn arm_spans<'tcx>(
    tcx: TyCtxt<'tcx>,
    def: LocalDefId,
    adt: ty::AdtDef<'tcx>,
) -> Vec<(Span, Vec<(usize, Span)>)> {
    use rustc_hir::intravisit::{self, Visitor};
    struct Arms<'tcx> {
        tcx: TyCtxt<'tcx>,
        typeck: &'tcx ty::TypeckResults<'tcx>,
        adt: ty::AdtDef<'tcx>,
        matches: Vec<(Span, Vec<(usize, Span)>)>,
    }
    impl<'tcx> Arms<'tcx> {
        fn variant(&self, qpath: &rustc_hir::QPath<'tcx>, id: rustc_hir::HirId) -> Option<usize> {
            use rustc_hir::def::{CtorOf, Res};
            let variants = self.adt.variants();
            match self.typeck.qpath_res(qpath, id) {
                Res::Def(DefKind::Variant, variant) => {
                    variants.iter().position(|candidate| candidate.def_id == variant)
                }
                Res::Def(DefKind::Ctor(CtorOf::Variant, _), ctor) => {
                    variants.iter().position(|candidate| candidate.ctor_def_id() == Some(ctor))
                }
                // A constant of the message's type is the variant it
                // evaluates to (`const IDLE: Msg = Msg::B;`), when the
                // constant is not generic.
                Res::Def(DefKind::Const { .. } | DefKind::AssocConst { .. }, constant) => {
                    let ty = self.tcx.type_of(constant).instantiate_identity().skip_norm_wip();
                    if ty.ty_adt_def() != Some(self.adt) || ty.has_non_region_param() {
                        return None;
                    }
                    let value = self.tcx.const_eval_poly(constant).ok()?;
                    self.tcx
                        .try_destructure_mir_constant_for_user_output(value, ty)?
                        .variant
                        .map(|variant| variant.as_usize())
                }
                _ => None,
            }
        }

        fn variants(&self, pat: &'tcx rustc_hir::Pat<'tcx>, out: &mut Vec<usize>) {
            use rustc_hir::PatKind;
            match pat.kind {
                PatKind::Or(pats) => pats.iter().for_each(|pat| self.variants(pat, out)),
                PatKind::TupleStruct(ref qpath, pats, _) => match self.variant(qpath, pat.hir_id) {
                    Some(variant) => out.push(variant),
                    None => pats.iter().for_each(|pat| self.variants(pat, out)),
                },
                PatKind::Struct(ref qpath, fields, _) => match self.variant(qpath, pat.hir_id) {
                    Some(variant) => out.push(variant),
                    None => fields.iter().for_each(|field| self.variants(field.pat, out)),
                },
                PatKind::Expr(expr) => {
                    if let rustc_hir::PatExprKind::Path(ref qpath) = expr.kind {
                        out.extend(self.variant(qpath, expr.hir_id));
                    }
                }
                PatKind::Tuple(pats, _) => pats.iter().for_each(|pat| self.variants(pat, out)),
                PatKind::Binding(_, _, _, Some(pat))
                | PatKind::Deref(pat)
                | PatKind::Ref(pat, _, _)
                | PatKind::Guard(pat, _) => self.variants(pat, out),
                _ => {}
            }
        }

        fn arms(&mut self, whole: Span, pats: impl Iterator<Item = &'tcx rustc_hir::Pat<'tcx>>) {
            let mut found = Vec::new();
            for pat in pats {
                let mut variants = Vec::new();
                self.variants(pat, &mut variants);
                found.extend(variants.into_iter().map(|variant| (variant, pat.span)));
            }
            if !found.is_empty() {
                self.matches.push((whole, found));
            }
        }
    }
    impl<'tcx> Visitor<'tcx> for Arms<'tcx> {
        fn visit_expr(&mut self, expr: &'tcx rustc_hir::Expr<'tcx>) {
            match expr.kind {
                rustc_hir::ExprKind::Match(_, arms, _) => {
                    self.arms(expr.span, arms.iter().map(|arm| arm.pat))
                }
                rustc_hir::ExprKind::Let(binding) => {
                    self.arms(binding.span, std::iter::once(binding.pat))
                }
                // A closure is its own body.
                rustc_hir::ExprKind::Closure(_) => return,
                _ => {}
            }
            intravisit::walk_expr(self, expr);
        }

        fn visit_local(&mut self, local: &'tcx rustc_hir::LetStmt<'tcx>) {
            self.arms(local.span, std::iter::once(local.pat));
            intravisit::walk_local(self, local);
        }
    }
    let Some(body) = tcx.hir_maybe_body_owned_by(def) else { return Vec::new() };
    let mut arms = Arms { tcx, typeck: tcx.typeck(def), adt, matches: Vec::new() };
    arms.visit_expr(&body.value);
    arms.matches
}

/// The consumer census, after the send census (`-Ztrust-send-census`). For
/// each enum some thread sends, its consumers: the bodies that come to hold
/// the message ([`Holds`]: a drain loop, a handler foreign code calls with it,
/// and what they pass it on to by value, not handed back) and that switch over
/// the message they hold ([`held_message`], [`dispatch`]). A body is named
/// only when one of those hands it the message: one nothing hands a message
/// to is not, however it matches on the type. An async body is not examined:
/// its message lives in the coroutine's state across an await, where this
/// census does not follow it. A note at the consumer names the local calls the
/// message passes through on its way to the switch (`admit_wake_before_commit`,
/// which may drop it), which variants a switch gives an arm of their own, and,
/// against the send census, the variants no enumerated thread sends over
/// resolved calls and those sent but left to a catch-all. A note at each arm
/// names the threads that send its variants.
fn report_consumers<'tcx>(
    render: &Render<'_, 'tcx>,
    hooks: &dyn CensusHooks<'tcx>,
    sent: &[Sent<'tcx>],
    messages: &[Ty<'tcx>],
    threads: &[Thread],
    emit: bool,
) -> (Vec<Consumer<'tcx>>, usize) {
    let tcx = render.tcx;
    let mut consumers: Vec<Consumer<'tcx>> = Vec::new();
    // The async bodies that take a message, which are not examined.
    let mut unexamined = 0;
    if messages.is_empty() {
        return (consumers, unexamined);
    }
    let erased = |ty: Ty<'tcx>| tcx.erase_and_anonymize_regions(ty);
    let defs = runtime_bodies(tcx);
    let bodies: FxHashSet<LocalDefId> = defs.iter().copied().collect();
    let mut memo: HandsBack<'tcx> = FxHashMap::default();
    // The instances the program makes of each generic local body: a generic
    // body is examined at them (`fn pump<F: FnMut(Msg)>(rx, f: F)` at the
    // closure a caller gives it), a few at most.
    let mut instances: FxHashMap<LocalDefId, Vec<GenericArgs<'tcx>>> = FxHashMap::default();
    for (node, _) in render.census.expanded().nodes() {
        let Some(Key::Body { def, args, .. }) = render.key(node) else { continue };
        let Some(local) = def.as_local() else { continue };
        if args.is_empty() || args.has_non_region_param() || !bodies.contains(&local) {
            continue;
        }
        let known = instances.entry(local).or_default();
        if known.len() < 8 && !known.contains(&args) {
            known.push(args);
        }
    }
    let substs = |def: LocalDefId| -> Vec<Option<GenericArgs<'tcx>>> {
        match instances.get(&def) {
            Some(known) if !known.is_empty() => known.iter().copied().map(Some).collect(),
            _ => vec![None],
        }
    };
    // The local bodies a call may run, each with its instance's arguments:
    // the callee itself; for a trait method, the body it resolves to (an
    // impl's, or the trait's own provided one), or every local impl when the
    // receiver's type is not known here (`H: Handler`, `dyn Handler`).
    let run_by = |body: &mir::Body<'tcx>, callee: DefId, callee_args: GenericArgs<'tcx>| {
        let local_fn = |def: DefId| def.as_local().filter(|def| bodies.contains(def));
        let identity = |def: LocalDefId| (def, GenericArgs::identity_for_item(tcx, def));
        let Some(trait_def) = tcx.trait_of_assoc(callee) else {
            return local_fn(callee).map(|def| (def, callee_args)).into_iter().collect::<Vec<_>>();
        };
        if let Some((def, args)) = run_instance_by_call(tcx, body, callee, callee_args) {
            if let Some(def) = local_fn(def) {
                return vec![(def, args)];
            }
        }
        let mut run: Vec<(LocalDefId, GenericArgs<'tcx>)> = tcx
            .all_impls(trait_def)
            .filter_map(|owner| tcx.impl_item_implementor_ids(owner).get(&callee).copied())
            .filter_map(local_fn)
            .map(identity)
            .collect();
        run.extend(local_fn(callee).map(identity));
        run
    };
    // An implementation of another crate's trait method is what foreign code
    // calls with the message, unless the census sees that only the crate's
    // own code calls it: resolved calls from other local bodies, and no call
    // or hand-off from anywhere else (an `impl From<Msg>` used only on a
    // value its caller builds). One nothing is seen to call is foreign
    // code's: a handler the census did not see handed over.
    let expanded = render.census.expanded();
    let mut called_locally: FxHashSet<DefId> = FxHashSet::default();
    let mut called_otherwise: FxHashSet<DefId> = FxHashSet::default();
    for edge in expanded.edges() {
        if !matches!(edge.class, EdgeClass::Run | EdgeClass::Approx) {
            continue;
        }
        let Some(Key::Body { def: to, .. }) = render.key(edge.to) else { continue };
        if !to.is_local() {
            continue;
        }
        match render.key(edge.from) {
            Some(Key::Body { def, .. }) if def == to => {}
            Some(Key::Body { def, .. }) if def.is_local() && edge.class == EdgeClass::Run => {
                called_locally.insert(to);
            }
            _ => {
                called_otherwise.insert(to);
            }
        }
    }
    let only_local_callers =
        |def: DefId| called_locally.contains(&def) && !called_otherwise.contains(&def);
    // Which bodies come to hold each message, and how. A root takes it off a
    // channel or is called with it by foreign code; the rest are handed it,
    // by value, by a body that holds it.
    let mut holds: Vec<FxHashMap<LocalDefId, Holds>> = vec![FxHashMap::default(); messages.len()];
    // The callables a dependency's pump is given with the receiver, each
    // with the body that hands it over.
    let mut pumped: Vec<Vec<(LocalDefId, LocalDefId)>> = vec![Vec::new(); messages.len()];
    // An async body's locals live in its state across an await.
    let examined = |def: LocalDefId| !tcx.is_coroutine(def.to_def_id());
    for &def in &defs {
        if !examined(def) {
            // Say so where such a body takes a message, not nothing.
            let captured: Vec<Ty<'tcx>> =
                match *tcx.type_of(def).instantiate_identity().skip_norm_wip().kind() {
                    ty::Coroutine(_, args) => {
                        args.as_coroutine().upvar_tys().iter().map(|ty| erased(ty)).collect()
                    }
                    _ => Vec::new(),
                };
            let mut taken: Vec<Ty<'tcx>> =
                messages.iter().copied().filter(|message| captured.contains(message)).collect();
            hooks.with_local_body(def, &mut |body| {
                for block in body.basic_blocks.iter() {
                    let Some(mir::Terminator { kind: TerminatorKind::Call { func, .. }, .. }) =
                        &block.terminator
                    else {
                        continue;
                    };
                    let Some((callee, callee_args)) = func.const_fn_def() else { continue };
                    let Some(drained) = drains_message(tcx, callee, callee_args) else { continue };
                    let drained = erased(drained);
                    if messages.contains(&drained) && !taken.contains(&drained) {
                        taken.push(drained);
                    }
                }
            });
            if !taken.is_empty() {
                unexamined += 1;
                if emit {
                    let names: Vec<String> =
                        taken.iter().map(|message| format!("`{message}`")).collect();
                    tcx.dcx()
                        .struct_span_note(
                            tcx.def_span(def),
                            format!(
                                "consumer census: `{}` is async and takes {} (off a channel, or as \
                                 an argument): an async body is not examined, since a message held \
                                 across an await lives in the coroutine's state",
                                tcx.def_path_str(def),
                                and_list(&names)
                            ),
                        )
                        .emit();
                }
            }
            continue;
        }
        let foreign = (tcx.def_kind(def) == DefKind::AssocFn)
            .then(|| tcx.impl_of_assoc(def.to_def_id()))
            .flatten()
            .and_then(|owner| tcx.impl_opt_trait_id(owner))
            .filter(|trait_def| !trait_def.is_local() && !only_local_callers(def.to_def_id()));
        hooks.with_local_body(def, &mut |body| {
            // A generic body, at the instances the program makes of it: one
            // generic over its message (`fn pump<T>(rx: Receiver<Msg<T>>)`)
            // takes the `Msg<u8>` a thread sends only there.
            for subst in substs(def) {
                for (index, &message) in messages.iter().enumerate() {
                    let by_value = body.args_iter().any(|local| {
                        at_instance(tcx, subst, body.local_decls[local].ty) == message
                    });
                    if let (Some(trait_def), true) = (foreign, by_value) {
                        // One that hands the message back is a filter the
                        // foreign code runs, not where the message goes.
                        let own = subst.unwrap_or_else(|| GenericArgs::identity_for_item(tcx, def));
                        let back =
                            hands_back(tcx, hooks, &bodies, &mut memo, def, own, message, None);
                        if back != Back::Yes {
                            holds[index].insert(def, Holds::Foreign(trait_def));
                        }
                    }
                    for block in body.basic_blocks.iter() {
                        let Some(mir::Terminator {
                            kind: TerminatorKind::Call { func, args, .. },
                            ..
                        }) = &block.terminator
                        else {
                            continue;
                        };
                        let Some((callee, callee_args)) = func.const_fn_def() else { continue };
                        let callee_args = at_instance(tcx, subst, callee_args);
                        if drains_message(tcx, callee, callee_args)
                            .is_some_and(|drained| erased(drained) == message)
                        {
                            holds[index].entry(def).or_insert(Holds::Drains);
                            continue;
                        }
                        // The channel's receiver handed to code outside the
                        // crate along with a closure or fn of the crate's
                        // that takes the message (a dependency's pump): that
                        // code calls it with each message.
                        let run = run_by_call(tcx, body, callee, callee_args).unwrap_or(callee);
                        if run.is_local() {
                            continue;
                        }
                        let arg_ty = |arg: &rustc_span::Spanned<mir::Operand<'tcx>>| {
                            at_instance(tcx, subst, arg.node.ty(body, tcx))
                        };
                        let gives_receiver = args.iter().any(|arg| {
                            matches!(*arg_ty(arg).peel_refs().kind(), ty::Adt(adt, adt_args)
                                if tcx.get_diagnostic_name(adt.did())
                                    .is_some_and(|name| name.as_str() == "MpscReceiver")
                                    && adt_args.types().next() == Some(message))
                        });
                        if gives_receiver {
                            for arg in args {
                                for callable in callables_taking(tcx, arg_ty(arg), message) {
                                    pumped[index].push((callable, def));
                                }
                            }
                        }
                    }
                }
            }
        });
    }
    // From the roots, by value, to a fixpoint. A body that is handed the
    // message is examined with what it is handed: the parameters that get
    // the held message (`seeds`; another parameter of the type is a value the
    // caller built) and the variants the message can still be at the call
    // (`entries`; a variant an arm of the caller took does not arrive).
    // `every`: the bodies outside code calls with the message, in any
    // by-value parameter of the type.
    // How many calls in the crate may run each local body. A body is read
    // with the variants a hand-off leaves only when that hand-off is the one
    // way into it: another call (with a value its caller built), an indirect
    // call, a thread, or code outside a library can give it any variant.
    let mut call_sites: FxHashMap<LocalDefId, usize> = FxHashMap::default();
    for &def in &defs {
        hooks.with_local_body(def, &mut |body| {
            for data in body.basic_blocks.iter() {
                let Some(mir::Terminator {
                    kind: TerminatorKind::Call { func, .. } | TerminatorKind::TailCall { func, .. },
                    ..
                }) = &data.terminator
                else {
                    continue;
                };
                let Some((callee, callee_args)) = func.const_fn_def() else { continue };
                for (target, _) in run_by(body, callee, callee_args) {
                    *call_sites.entry(target).or_default() += 1;
                }
            }
        });
    }
    let exported = {
        let library = tcx.entry_fn(()).is_none();
        let visibilities = tcx.effective_visibilities(());
        let level = rustc_middle::middle::privacy::Level::ReachableThroughImplTrait;
        move |def: LocalDefId| library && visibilities.is_public_at_level(def, level)
    };
    let one_way_in = |def: LocalDefId| {
        call_sites.get(&def).copied().unwrap_or(0) == 1
            && !called_otherwise.contains(&def.to_def_id())
            && !exported(def)
    };
    let mut seeds: Vec<FxHashMap<LocalDefId, FxHashSet<usize>>> =
        vec![FxHashMap::default(); messages.len()];
    let mut every: Vec<FxHashSet<LocalDefId>> = vec![FxHashSet::default(); messages.len()];
    let mut entries: Vec<FxHashMap<LocalDefId, VariantSet>> =
        vec![FxHashMap::default(); messages.len()];
    for (index, &message) in messages.iter().enumerate() {
        let ty::Adt(adt, _) = *message.kind() else { continue };
        let count = adt.variants().len();
        for &(callable, from) in &pumped[index] {
            if bodies.contains(&callable) && examined(callable) {
                holds[index].entry(callable).or_insert(Holds::From(from));
            }
        }
        let mut roots: Vec<LocalDefId> = holds[index].keys().copied().collect();
        roots.sort_unstable_by_key(|def| def.local_def_index.as_u32());
        for &root in &roots {
            every[index].insert(root);
            entries[index].insert(root, VariantSet::all(count));
        }
        let mut work: VecDeque<LocalDefId> = roots.into_iter().collect();
        // Every step grows a set, so the walk ends; the bound is a backstop.
        let mut steps = 0;
        while let Some(def) = work.pop_front() {
            steps += 1;
            if steps > 100_000 {
                break;
            }
            let seed = (!every[index].contains(&def))
                .then(|| seeds[index].get(&def).cloned().unwrap_or_default());
            let entry = entries[index].get(&def).cloned().unwrap_or_else(|| VariantSet::all(count));
            // What the body hands on: the callee, the parameters that get the
            // message (`None`: any of the type), and the variants at the call.
            let mut handed: Vec<(LocalDefId, Option<FxHashSet<usize>>, VariantSet)> = Vec::new();
            hooks.with_local_body(def, &mut |body| {
                for subst in substs(def) {
                    let held = held_message(
                        tcx,
                        body,
                        message,
                        subst,
                        seed.as_ref(),
                        &mut |callee, callee_args, param| {
                            hands_back(
                                tcx,
                                hooks,
                                &bodies,
                                &mut memo,
                                callee,
                                callee_args,
                                message,
                                Some(param),
                            )
                        },
                    );
                    let found = dispatch(tcx, body, message, adt, &held, &entry);
                    // The variants the message handed on can be at the call.
                    let at = |block: mir::BasicBlock, locals: &[mir::Local]| {
                        Dispatch::at(found.as_ref(), body, &held, &entry, block, locals)
                    };
                    let is_held = |local: mir::Local| {
                        held.locals[local.as_usize()] == Hold::Is
                            && !held.clobbered.contains(&local)
                    };
                    // A wrapper around it (`Box::new(m)`, the receive's own
                    // `Result`): a callee given one by value unwraps it.
                    let is_wrapper = |local: mir::Local| {
                        held.locals[local.as_usize()] == Hold::Wraps
                            && !held.clobbered.contains(&local)
                    };
                    for (block, data) in body.basic_blocks.iter_enumerated() {
                        let Some(mir::Terminator {
                            kind: TerminatorKind::Call { func, args, .. },
                            ..
                        }) = &data.terminator
                        else {
                            continue;
                        };
                        let Some((callee, callee_args)) = func.const_fn_def() else { continue };
                        let callee_args = at_instance(tcx, subst, callee_args);
                        if drains_message(tcx, callee, callee_args).is_some() {
                            continue;
                        }
                        let bare = |arg: &rustc_span::Spanned<mir::Operand<'tcx>>| {
                            arg.node.place().filter(|place| place.projection.is_empty())
                        };
                        // Given the HELD message by value, not any value of
                        // its type: a fn handed a fresh one consumes nothing.
                        // A call through the Fn traits passes its arguments
                        // as one tuple after the callee (`fields`: which of
                        // them is the message).
                        let tupled = tcx.trait_of_assoc(callee).is_some_and(|trait_def| {
                            tcx.fn_trait_kind_from_def_id(trait_def).is_some()
                        });
                        let mut params: FxHashSet<usize> = FxHashSet::default();
                        let mut fields: FxHashSet<usize> = FxHashSet::default();
                        let mut given: Vec<mir::Local> = Vec::new();
                        for (position, arg) in args.iter().enumerate() {
                            let Some(place) = bare(arg) else { continue };
                            if tupled {
                                if position == 1 {
                                    for (&(tuple, field), built) in &held.fields {
                                        for &from in built {
                                            if tuple == place.local && is_held(from) {
                                                fields.insert(field);
                                                given.push(from);
                                            }
                                        }
                                    }
                                }
                            } else if is_held(place.local)
                                || (is_wrapper(place.local)
                                    && matches!(arg.node, mir::Operand::Move(_)))
                            {
                                params.insert(position + 1);
                                given.push(place.local);
                            }
                        }
                        given.sort_unstable();
                        if !(params.is_empty() && fields.is_empty())
                            && matches!(tcx.def_kind(callee), DefKind::Fn | DefKind::AssocFn)
                        {
                            let output = erased_sig(tcx, callee, Some(callee_args)).output();
                            let output = at_instance(tcx, None, output);
                            let returns = names_message(tcx, output, message, 0);
                            for (target, target_args) in run_by(body, callee, callee_args) {
                                // The callable's own parameters: a closure's
                                // come after its environment, a fn item's
                                // (`f(app, w)` with `f` the fn `on`) first.
                                let params: FxHashSet<usize> = if tupled {
                                    let first =
                                        if tcx.is_closure_like(target.to_def_id()) { 2 } else { 1 };
                                    fields.iter().map(|field| field + first).collect()
                                } else {
                                    params.clone()
                                };
                                // A callee that hands the message back is a
                                // filter on its way, not where it goes.
                                // (One that may rewrite it is both.)
                                if returns
                                    && params.iter().any(|param| {
                                        hands_back(
                                            tcx,
                                            hooks,
                                            &bodies,
                                            &mut memo,
                                            target,
                                            target_args,
                                            message,
                                            Some(*param),
                                        ) == Back::Yes
                                    })
                                {
                                    continue;
                                }
                                handed.push((target, Some(params.clone()), at(block, &given)));
                            }
                        }
                        // A callable handed to code outside the crate along
                        // with the message, or with what it comes in
                        // (`rx.iter().for_each(|m| ..)`): that code calls it
                        // with the message.
                        let run = run_by_call(tcx, body, callee, callee_args).unwrap_or(callee);
                        let with_message: Vec<mir::Local> = args
                            .iter()
                            .filter_map(|arg| bare(arg))
                            .map(|place| place.local)
                            .filter(|local| {
                                matches!(held.locals[local.as_usize()], Hold::Is | Hold::Wraps)
                                    && !held.clobbered.contains(local)
                            })
                            .collect();
                        if run.is_local() || with_message.is_empty() {
                            continue;
                        }
                        for arg in args {
                            let handed_ty = at_instance(tcx, subst, arg.node.ty(body, tcx));
                            for callable in callables_taking(tcx, handed_ty, message) {
                                handed.push((callable, None, at(block, &with_message)));
                            }
                        }
                    }
                }
            });
            for (callee, params, live) in handed {
                if !examined(callee) || !bodies.contains(&callee) {
                    continue;
                }
                // A root already takes every parameter and every variant.
                if matches!(holds[index].get(&callee), Some(Holds::Drains | Holds::Foreign(_))) {
                    continue;
                }
                let mut grew = false;
                if let std::collections::hash_map::Entry::Vacant(slot) = holds[index].entry(callee)
                {
                    slot.insert(Holds::From(def));
                    grew = true;
                }
                match params {
                    Some(params) if !every[index].contains(&callee) => {
                        let slot = seeds[index].entry(callee).or_default();
                        for param in params {
                            grew |= slot.insert(param);
                        }
                    }
                    Some(_) => {}
                    None => grew |= every[index].insert(callee),
                }
                let live = if one_way_in(callee) { live } else { VariantSet::all(count) };
                grew |= entries[index]
                    .entry(callee)
                    .or_insert_with(|| VariantSet::none(count))
                    .union(&live);
                if grew {
                    work.push_back(callee);
                }
            }
        }
    }
    let unnamed = threads.iter().filter(|thread| !thread.known).count();
    for def in defs {
        if holds.iter().all(|held| !held.contains_key(&def)) {
            continue;
        }
        hooks.with_local_body(def, &mut |body| {
            for (index, &message) in messages.iter().enumerate() {
                let Some(&how) = holds[index].get(&def) else { continue };
                let ty::Adt(adt, _) = *message.kind() else { continue };
                let seed = (!every[index].contains(&def))
                    .then(|| seeds[index].get(&def).cloned().unwrap_or_default());
                let entry = entries[index]
                    .get(&def)
                    .cloned()
                    .unwrap_or_else(|| VariantSet::all(adt.variants().len()));
                // A generic body is reported at the first instance the
                // program makes of it at which it dispatches on THIS message
                // (one generic over its message holds another at another).
                let found = substs(def).into_iter().find_map(|subst| {
                    let held = held_message(
                        tcx,
                        body,
                        message,
                        subst,
                        seed.as_ref(),
                        &mut |callee, callee_args, param| {
                            hands_back(
                                tcx,
                                hooks,
                                &bodies,
                                &mut memo,
                                callee,
                                callee_args,
                                message,
                                Some(param),
                            )
                        },
                    );
                    dispatch(tcx, body, message, adt, &held, &entry)
                });
                let Some(found) = found else { continue };
                let consumer = tcx.def_path_str(def);
                let names: Vec<String> =
                    adt.variants().iter().map(|variant| variant.name.to_string()).collect();
                let total = names.len();
                // The variants left to a catch-all, when one can run, and
                // those that have no arm because they cannot occur.
                let unarmed = |variant: &usize| !found.armed.contains(*variant);
                let rest: Vec<String> = (0..total)
                    .filter(unarmed)
                    .filter(|variant| found.catch_all && !found.impossible.contains(*variant))
                    .map(|variant| names[variant].clone())
                    .collect();
                let never = (0..total)
                    .filter(unarmed)
                    .filter(|variant| !found.catch_all || found.impossible.contains(*variant))
                    .count();
                let rows: Vec<&Sent<'tcx>> =
                    sent.iter().filter(|row| row.message == message).collect();
                let sent_names: BTreeSet<&String> =
                    rows.iter().flat_map(|row| row.variants.iter()).collect();
                let untraced = rows.iter().filter(|row| row.untraced).count();
                let indirect = rows.iter().filter(|row| row.indirect).count();
                let qualified = |name: &String| format!("`{message}::{name}`");
                let mut text = match how {
                    Holds::Drains => {
                        format!("consumer census: `{consumer}` drains a channel of `{message}`")
                    }
                    Holds::Foreign(trait_def) => format!(
                        "consumer census: `{consumer}` receives `{message}` by value from foreign \
                         code (it implements `{}`)",
                        tcx.def_path_str(trait_def)
                    ),
                    Holds::From(caller) => format!(
                        "consumer census: `{consumer}` receives `{message}` by value from `{}`",
                        tcx.def_path_str(caller)
                    ),
                };
                if !found.filters.is_empty() {
                    let through: Vec<String> = found
                        .filters
                        .iter()
                        .map(|(name, kind)| {
                            let does = match kind {
                                Filter::Passes => "which passes it on",
                                Filter::MayDrop => "which may drop it",
                                Filter::MayRewrite => "which may rewrite it",
                            };
                            format!("`{name}` ({does})")
                        })
                        .collect();
                    text.push_str(&format!(", through {}", and_list(&through)));
                }
                let armed = found.armed.count();
                if armed == total {
                    text.push_str(&format!(
                        "; its switch gives each of its {total} variants an arm"
                    ));
                } else {
                    text.push_str(&format!(
                        "; its switch gives {armed} of its {total} variants an arm"
                    ));
                    if !rest.is_empty() {
                        text.push_str(&format!(
                            ", and {} share the catch-all ({})",
                            rest.len(),
                            rest.join(", ")
                        ));
                    }
                    // No catch-all can run for these: the compiler found
                    // them uninhabited.
                    if never > 0 {
                        text.push_str(&format!(", and the other {never} cannot occur"));
                    }
                }
                if found.others > 0 {
                    text.push_str(&format!(
                        " ({} switch(es) over another `{message}` value in this body are not \
                         counted)",
                        found.others
                    ));
                }
                let left: Vec<String> =
                    rest.iter().filter(|name| sent_names.contains(name)).map(qualified).collect();
                if !left.is_empty() {
                    text.push_str(&format!(
                        ". Sent but left to the catch-all: {}",
                        and_list(&left)
                    ));
                }
                let unsent: Vec<String> =
                    names.iter().filter(|name| !sent_names.contains(name)).map(qualified).collect();
                // With every send traced, an unlisted variant is one no
                // enumerated thread sends. Otherwise it is only one no send
                // was traced to.
                let exact = untraced == 0 && unnamed == 0;
                if !unsent.is_empty() {
                    text.push_str(&if exact {
                        format!(
                            ". No enumerated thread sends {} over the calls the census resolved",
                            and_list(&unsent)
                        )
                    } else {
                        format!(". No send was traced to {}", and_list(&unsent))
                    });
                }
                if untraced > 0 {
                    text.push_str(&format!(
                        ". {untraced} thread(s) send `{message}` with a value the census could \
                         not trace to a variant"
                    ));
                }
                if indirect > 0 {
                    text.push_str(&format!(
                        ". {indirect} thread(s) may also reach a send of `{message}` behind an \
                         indirect call or a hand-off, which is not counted"
                    ));
                }
                if unnamed > 0 {
                    text.push_str(&format!(
                        ". {unnamed} thread(s) run a callable the census could not name, and \
                         what they send is not counted"
                    ));
                }
                consumers.push(Consumer {
                    def,
                    message,
                    names: names.clone(),
                    live: found.live,
                    by_root: found.by_root.into_iter().map(|(_, live)| live).collect(),
                });
                if !emit {
                    continue;
                }
                tcx.dcx().struct_span_note(tcx.def_span(def), text).emit();
                let matches = arm_spans(tcx, def, adt);
                // The pattern that names `variant` in the smallest `match`
                // around the switch.
                let pattern = |variant: usize, switch: Span| {
                    let mut within: Vec<&(Span, Vec<(usize, Span)>)> = matches
                        .iter()
                        .filter(|(whole, arms)| {
                            // No switch to place (a one-variant message): any
                            // pattern that names the variant.
                            (switch.is_dummy() || whole.contains(switch))
                                && arms.iter().any(|(seen, _)| *seen == variant)
                        })
                        .collect();
                    within.sort_by_key(|(whole, _)| whole.hi() - whole.lo());
                    let (_, arms) = within.first()?;
                    arms.iter().find(|(seen, _)| *seen == variant).map(|(_, span)| *span)
                };
                for (block, variants, switch) in found.arms {
                    let data = &body.basic_blocks[block];
                    let landing = data
                        .statements
                        .first()
                        .map(|statement| statement.source_info.span)
                        .or_else(|| data.terminator.as_ref().map(|t| t.source_info.span))
                        .unwrap_or_else(|| tcx.def_span(def));
                    // One note per source arm: two arms that only jump share
                    // their target block.
                    let mut by_span: Vec<(Span, Vec<usize>)> = Vec::new();
                    for variant in variants {
                        // A pattern that names no variant in source (a
                        // `const`) is found at its switch, not where the arm
                        // lands.
                        let span = pattern(variant, switch).unwrap_or(if switch.is_dummy() {
                            landing
                        } else {
                            switch
                        });
                        match by_span.iter_mut().find(|(seen, _)| *seen == span) {
                            Some((_, variants)) => variants.push(variant),
                            None => by_span.push((span, vec![variant])),
                        }
                    }
                    for (span, variants) in by_span {
                        let arm: Vec<&String> =
                            variants.iter().map(|variant| &names[*variant]).collect();
                        // In the send census's order: `main`, then each spawn.
                        let from: Vec<String> = rows
                            .iter()
                            .filter(|row| arm.iter().any(|name| row.variants.contains(*name)))
                            .map(|row| row.who.clone())
                            .collect();
                        let these: Vec<String> = arm.iter().map(|name| qualified(name)).collect();
                        let arrives =
                            variants.iter().any(|variant| found.arriving.contains(*variant));
                        // Behind a callee that may rewrite the message, an
                        // arm also takes what that callee makes of another
                        // variant, whoever sent that one.
                        let rewriters: Vec<String> = found
                            .filters
                            .iter()
                            .filter(|(_, kind)| *kind == Filter::MayRewrite)
                            .map(|(name, _)| format!("`{name}`"))
                            .collect();
                        let or_made = if rewriters.is_empty() {
                            String::new()
                        } else {
                            format!(", or what {} makes of another variant", and_list(&rewriters))
                        };
                        let text = if !arrives {
                            // An earlier switch, here or in the body that
                            // hands the message on, took the variant.
                            format!(
                                "consumer census: the arm for {} in `{consumer}` takes no message: \
                                 none reaches it as that variant (an earlier switch takes it)",
                                these.join(" | ")
                            )
                        } else if from.is_empty() && exact {
                            format!(
                                "consumer census: the arm for {} in `{consumer}` takes it from no \
                                 enumerated thread over the calls the census resolved{or_made}",
                                these.join(" | ")
                            )
                        } else if from.is_empty() {
                            format!(
                                "consumer census: the arm for {} in `{consumer}`: no send was \
                                 traced to it{or_made}",
                                these.join(" | ")
                            )
                        } else {
                            format!(
                                "consumer census: the arm for {} in `{consumer}` takes it from \
                                 {}{or_made}",
                                these.join(" | "),
                                and_list(&from)
                            )
                        };
                        tcx.dcx().struct_span_note(span, text).emit();
                    }
                }
            }
        });
    }
    (consumers, unexamined)
}

/// The local closures and fns a value of type `ty` is or holds (a closure,
/// a fn item, a `Loop<{closure}>` built around one), that take `message` as
/// a parameter: alone, or in the tuple a call through the Fn traits passes.
fn callables_taking<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>, message: Ty<'tcx>) -> Vec<LocalDefId> {
    let takes = |inputs: &[Ty<'tcx>]| {
        inputs.iter().any(|input| match *tcx.erase_and_anonymize_regions(*input).kind() {
            ty::Tuple(fields) => fields.iter().any(|field| field == message),
            _ => tcx.erase_and_anonymize_regions(*input) == message,
        })
    };
    let mut found: Vec<LocalDefId> = Vec::new();
    for arg in ty.walk() {
        let GenericArgKind::Type(part) = arg.kind() else { continue };
        let callable = match *part.kind() {
            ty::Closure(def, closure) => {
                let sig = closure.as_closure().sig();
                takes(sig.skip_binder().inputs()).then(|| def.as_local()).flatten()
            }
            ty::FnDef(def, fn_args) => {
                takes(erased_sig(tcx, def, Some(fn_args.skip_binder())).inputs())
                    .then(|| def.as_local())
                    .flatten()
            }
            _ => None,
        };
        if let Some(callable) = callable {
            if !found.contains(&callable) {
                found.push(callable);
            }
        }
    }
    found
}

/// The signature of the fn `def` (at `args`, or its own parameters) with its
/// late-bound regions erased like every other: `skip_binder` leaves them
/// bound, and a bound region compares unequal to the erased one in a type
/// taken from a body, and is refused by trait queries.
fn erased_sig<'tcx>(
    tcx: TyCtxt<'tcx>,
    def: DefId,
    args: Option<GenericArgs<'tcx>>,
) -> ty::FnSig<'tcx> {
    let sig = match args {
        Some(args) => tcx.fn_sig(def).instantiate(tcx, args).skip_norm_wip(),
        None => tcx.fn_sig(def).instantiate_identity().skip_norm_wip(),
    };
    tcx.erase_and_anonymize_regions(tcx.instantiate_bound_regions_with_erased(sig))
}

/// The local fns and closures whose bodies run at run time, in definition
/// order: what a census may read with [`CensusHooks::with_local_body`]. A
/// body in a const context (a `#[rustc_comptime]` fn) runs only at compile
/// time, and const evaluation has stolen its elaborated MIR by now.
fn runtime_bodies(tcx: TyCtxt<'_>) -> Vec<LocalDefId> {
    let mut defs: Vec<LocalDefId> = tcx
        .mir_keys(())
        .iter()
        .copied()
        .filter(|def| {
            matches!(tcx.def_kind(*def), DefKind::Fn | DefKind::AssocFn | DefKind::Closure)
                && !matches!(
                    tcx.hir_body_const_context(*def),
                    Some(
                        rustc_hir::ConstContext::Const { .. } | rustc_hir::ConstContext::Static(_)
                    )
                )
        })
        .collect();
    defs.sort_unstable_by_key(|def| def.local_def_index.as_u32());
    defs
}

/// Whether `thread` is the consumer's own: one whose resolved calls reach an
/// instance of it (`nodes`), or, when no thread's do (a handler foreign code
/// calls back, as winit's run loop calls `App::user_event`), `main`. One rule
/// for the shared-state and the writer census.
fn runs_consumer(thread: &Thread, threads: &[Thread], nodes: &[ReachNode]) -> bool {
    let runs = |thread: &Thread| nodes.iter().any(|node| thread.exact.contains(node));
    runs(thread) || (thread.is_main && !threads.iter().any(runs))
}

/// Whether the static `def` is a cell threads can share: not thread-local, and
/// `static mut` or of a type with interior mutability (an atomic, a `Mutex`).
fn is_shared_static(tcx: TyCtxt<'_>, def: DefId) -> bool {
    matches!(tcx.def_kind(def), DefKind::Static { nested: false, .. })
        && !tcx.is_thread_local_static(def)
        && (tcx.static_mutability(def) == Some(rustc_hir::Mutability::Mut)
            || !static_ty(tcx, def).is_freeze(tcx, ty::TypingEnv::fully_monomorphized()))
}

/// The type of the static `def`, as declared and normalized: one spelled
/// through an associated type (`<Flag as Cell>::Inner`) is the type it names.
fn static_ty<'tcx>(tcx: TyCtxt<'tcx>, def: DefId) -> Ty<'tcx> {
    let declared = tcx.type_of(def).instantiate_identity();
    tcx.try_normalize_erasing_regions(ty::TypingEnv::fully_monomorphized(), declared)
        .unwrap_or_else(|_| declared.skip_norm_wip())
}

/// How a shared static synchronizes, for the shared-state census: what a
/// model must know before it treats the cell under interleaving.
fn static_kind<'tcx>(tcx: TyCtxt<'tcx>, def: DefId, messages: &[Ty<'tcx>]) -> &'static str {
    if tcx.static_mutability(def) == Some(rustc_hir::Mutability::Mut) {
        return "unsynchronized (`static mut`)";
    }
    cell_kind(tcx, static_ty(tcx, def), messages)
}

/// How a value of type `ty` synchronizes. Only the sysroot's own types are
/// known by name: a program's `Mutex` or `AtomicThing` is whatever it wraps.
/// The kind is that of the parts that can change ([`interior_parts`]), where
/// they agree: a struct of atomics is atomic, an `Option<Mutex<_>>` a lock. A
/// set-once cell is set-once only when nothing it holds or points to can
/// change after: a `LazyLock<Mutex<_>>` is a lock, a `OnceLock<AtomicBool>` an
/// atomic, and so is a `OnceLock<Arc<Mutex<_>>>` or a `LazyLock<Vec<AtomicU8>>`.
/// Parts of different kinds (a lock and an atomic beside it), or one with no
/// known name, make it none of them: it is listed with its type.
fn cell_kind<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>, messages: &[Ty<'tcx>]) -> &'static str {
    // A walk that was cut short saw some of the parts: they decide no kind.
    let (parts, whole) = interior_parts(tcx, ty, messages);
    if !whole {
        return "interior-mutable";
    }
    let mut kinds: Vec<&'static str> = parts
        .into_iter()
        .map(|part| {
            let ty::Adt(adt, args) = *part.kind() else { return "interior-mutable" };
            match tcx.item_name(adt.did()).as_str() {
                name if name.starts_with("Atomic") => "atomic",
                "Mutex" | "RwLock" | "ReentrantLock" => "locked",
                "Once" => "set-once",
                "OnceLock" | "LazyLock" | "OnceCell" | "LazyCell" => match args.types().next() {
                    Some(held) => {
                        let (inner, whole) = interior_parts(tcx, held, messages);
                        if whole && inner.is_empty() {
                            "set-once"
                        } else {
                            cell_kind(tcx, held, messages)
                        }
                    }
                    None => "set-once",
                },
                _ => "interior-mutable",
            }
        })
        .collect();
    kinds.sort_unstable();
    kinds.dedup();
    match kinds.as_slice() {
        [one] => one,
        _ => "interior-mutable",
    }
}

/// How many instantiations of one generic type a type walk expands. A
/// polymorphically recursive type (`Nest<T>` holding a `Nest<Option<T>>`) has
/// a new instantiation at every step, and several such fields branch; a
/// struct with hundreds of fields of one generic type has as many, and all of
/// those are read.
const EXPANSIONS: usize = 4096;

/// Whether `adt` is one of `std::sync::mpsc`'s types (or of `mpmc`, behind
/// it): a channel endpoint or an iterator over one.
fn is_channel_type(tcx: TyCtxt<'_>, adt: ty::AdtDef<'_>) -> bool {
    in_std_module(tcx, adt.did(), "mpsc") || in_std_module(tcx, adt.did(), "mpmc")
}

/// What a shared-state walk does at a type: go on into what it holds, pass
/// over it, or end (the walk has its answer).
#[derive(Clone, Copy, PartialEq, Eq)]
enum Walk {
    Into,
    Skip,
    Stop,
}

/// Calls `visit` on every type a value of one of `roots` holds or leads to:
/// the one walk behind the questions the shared-state census asks of a type
/// ([`interior_parts`], [`reaching`], [`arc_cells`]).
///
/// A type outside the sysroot (the program's, or a dependency's) holds what
/// its FIELDS hold at that instance, and nothing else: its type arguments
/// say what it names (`Id<App>` around a `u32` holds no `App`). A sysroot
/// type holds its type arguments, since its fields hide them behind untyped
/// pointers; so a `PhantomData<T>` is a claim to a `T`, as std's own
/// collections use it. A fn pointer, a fn item and a `dyn` type name types
/// and hold none (`visit` still sees them). A message is what the channel
/// carries and is not entered, nor is a channel endpoint: the channel is the
/// model's FIFO. `link` is told each step of the walk, holder then held, also
/// one to a type the walk has met already: [`reaching`] reads answers for
/// many types off one walk with it.
///
/// Returns the types the walk met and did not enter because a bound cut it
/// there ([`EXPANSIONS`], a definition that keeps coming back larger): what
/// such a type holds is not known, and no answer may be read as if it held
/// nothing.
fn held_types<'tcx>(
    tcx: TyCtxt<'tcx>,
    roots: impl Iterator<Item = Ty<'tcx>>,
    messages: &[Ty<'tcx>],
    visit: &mut dyn FnMut(Ty<'tcx>) -> Walk,
    link: &mut dyn FnMut(Ty<'tcx>, Ty<'tcx>),
) -> Vec<Ty<'tcx>> {
    let mut cut: Vec<Ty<'tcx>> = Vec::new();
    let mut seen: FxHashSet<Ty<'tcx>> = FxHashSet::default();
    let mut expanded: FxHashMap<DefId, usize> = FxHashMap::default();
    // The way down to each type: the definitions entered on it ([`Grown`]).
    type Way = Option<std::rc::Rc<Grown>>;
    let mut work: VecDeque<(Option<Ty<'tcx>>, Ty<'tcx>, Way)> =
        roots.map(|root| (None, root, None)).collect();
    while let Some((holder, ty, way)) = work.pop_front() {
        // A type spelled through an associated type is the type it names.
        let ty = at_instance(tcx, None, ty);
        if let Some(holder) = holder {
            link(holder, ty);
        }
        if !seen.insert(ty) || messages.contains(&ty) {
            continue;
        }
        match visit(ty) {
            Walk::Into => {}
            Walk::Skip => continue,
            Walk::Stop => return cut,
        }
        let held = Some(ty);
        match *ty.kind() {
            ty::FnPtr(..) | ty::FnDef(..) | ty::Dynamic(..) => {}
            ty::Adt(adt, _) if is_channel_type(tcx, adt) => {}
            ty::Adt(adt, args) if crate::def_is_in_sysroot_resident_crate(tcx, adt.did()) => {
                work.extend(args.types().map(|inner| (held, inner, way.clone())));
            }
            ty::Adt(adt, args) => {
                let count = expanded.entry(adt.did()).or_default();
                // (Inside a binder a type can name a bound region, which no
                // query on a field's type accepts.)
                if *count >= EXPANSIONS || ty.has_escaping_bound_vars() {
                    cut.push(ty);
                    continue;
                }
                // Polymorphic recursion: the definition entered again on
                // this way, at a type larger than any it had on the way,
                // more than a few times over. (A definition that comes back
                // at types that do not grow, or at two sizes in turn, is
                // ordinary nesting.)
                let size = ty.walk().count();
                let (mut grown, mut largest) = (0, size);
                let mut up = way.as_deref();
                while let Some(step) = up {
                    if step.def == adt.did() {
                        grown = step.grown + usize::from(size > step.largest);
                        largest = size.max(step.largest);
                        break;
                    }
                    up = step.up.as_deref();
                }
                if grown > REENTRIES {
                    cut.push(ty);
                    continue;
                }
                *count += 1;
                let way = Some(std::rc::Rc::new(Grown { def: adt.did(), largest, grown, up: way }));
                work.extend(
                    adt.all_fields()
                        .map(|field| (held, field.ty(tcx, args).skip_norm_wip(), way.clone())),
                );
            }
            ty::Ref(_, inner, _)
            | ty::RawPtr(inner, _)
            | ty::Array(inner, _)
            | ty::Slice(inner)
            | ty::Pat(inner, _) => work.push_back((held, inner, way)),
            ty::Tuple(fields) => work.extend(fields.iter().map(|inner| (held, inner, way.clone()))),
            ty::Closure(_, args) => work.extend(
                args.as_closure().upvar_tys().iter().map(|inner| (held, inner, way.clone())),
            ),
            ty::CoroutineClosure(_, args) => work.extend(
                args.as_coroutine_closure()
                    .upvar_tys()
                    .iter()
                    .map(|inner| (held, inner, way.clone())),
            ),
            ty::Coroutine(_, args) => work.extend(
                args.as_coroutine().upvar_tys().iter().map(|inner| (held, inner, way.clone())),
            ),
            _ => {}
        }
    }
    cut
}

/// One definition a type walk entered on its way down ([`held_types`]): the
/// largest type it had on the way so far, and how many times on this way it
/// had come back larger than that.
struct Grown {
    def: DefId,
    largest: usize,
    grown: usize,
    up: Option<std::rc::Rc<Grown>>,
}

/// The types a walk from `roots` meets ([`held_types`]) that are, hold or
/// lead to a type `target` accepts. One walk answers for every root: asking
/// each root on its own is a walk per root, and on a polymorphically
/// recursive family, where a walk runs to its bound, thousands of them. A
/// With `cut_reaches`, a type the walk was cut at counts as one that leads to
/// a target: what it holds was not read (asked for "can it hold a cell",
/// where a no must be known; not for "does it hold the consumer's value",
/// where a yes is a statement the note makes).
fn reaching<'tcx>(
    tcx: TyCtxt<'tcx>,
    roots: &[Ty<'tcx>],
    messages: &[Ty<'tcx>],
    target: &dyn Fn(Ty<'tcx>) -> bool,
    cut_reaches: bool,
) -> FxHashSet<Ty<'tcx>> {
    let mut holders: FxHashMap<Ty<'tcx>, Vec<Ty<'tcx>>> = FxHashMap::default();
    let mut work: Vec<Ty<'tcx>> = Vec::new();
    let cut = held_types(
        tcx,
        roots.iter().copied(),
        messages,
        &mut |ty| {
            // What is under a target is not asked about.
            if target(ty) {
                work.push(ty);
                Walk::Skip
            } else {
                Walk::Into
            }
        },
        &mut |holder, held| holders.entry(held).or_default().push(holder),
    );
    if cut_reaches {
        work.extend(cut);
    }
    let mut reach: FxHashSet<Ty<'tcx>> = work.iter().copied().collect();
    while let Some(ty) = work.pop() {
        for &holder in holders.get(&ty).map_or(&[][..], Vec::as_slice) {
            if reach.insert(holder) {
                work.push(holder);
            }
        }
    }
    reach
}

/// Whether `part` is a cell: a std type with interior mutability that is one
/// itself (known by name) or has nothing to look into, or a `dyn` type (what
/// is behind it is not known here). An `Option<Mutex<_>>` or a
/// `ManuallyDrop<AtomicU8>` is not one: the cell is what it holds.
fn is_cell<'tcx>(tcx: TyCtxt<'tcx>, part: Ty<'tcx>) -> bool {
    match *part.kind() {
        ty::Dynamic(..) => true,
        ty::Adt(adt, args) => {
            crate::def_is_in_sysroot_resident_crate(tcx, adt.did())
                && !is_channel_type(tcx, adt)
                && !part.has_param()
                && !part.has_escaping_bound_vars()
                && !part.is_freeze(tcx, ty::TypingEnv::fully_monomorphized())
                && (args.types().next().is_none() || {
                    let name = tcx.item_name(adt.did());
                    let name = name.as_str();
                    name.starts_with("Atomic")
                        || matches!(
                            name,
                            "Mutex"
                                | "RwLock"
                                | "ReentrantLock"
                                | "Once"
                                | "OnceLock"
                                | "LazyLock"
                                | "OnceCell"
                                | "LazyCell"
                                | "Cell"
                                | "RefCell"
                                | "UnsafeCell"
                                | "SyncUnsafeCell"
                        )
                })
        }
        _ => false,
    }
}

/// The types with interior mutability that a value of type `ty` holds or
/// points to (a few of them): `ty` itself, what a pointer or a collection
/// holds (`Arc<Mutex<_>>`, `Vec<AtomicU8>`, `&'static Registry`), or a field
/// of a type outside the sysroot (rustc's `Freeze` sees only what is stored
/// inline). A `dyn` type is taken to have it: what is behind it is not known
/// here. Not what a message carries, nor what is behind a channel endpoint
/// ([`held_types`]). With them, whether those are all of them: the walk ended
/// neither at a seventeenth part nor at a bound of its own.
fn interior_parts<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>,
    messages: &[Ty<'tcx>],
) -> (Vec<Ty<'tcx>>, bool) {
    let mut parts: Vec<Ty<'tcx>> = Vec::new();
    let mut stopped = false;
    let cut = held_types(
        tcx,
        std::iter::once(ty),
        messages,
        &mut |part| {
            if is_cell(tcx, part) {
                if parts.len() >= 16 {
                    stopped = true;
                    return Walk::Stop;
                }
                parts.push(part);
                // What a cell holds is under it, not beside it. Under a
                // LOCK it is still a part: an atomic in an `RwLock<HashMap>`
                // changes with the lock held shared, and one in an `Arc`
                // cloned out of a `Mutex` with no lock held.
                let lock = matches!(*part.kind(), ty::Adt(adt, _)
                    if matches!(tcx.item_name(adt.did()).as_str(), "Mutex" | "RwLock" | "ReentrantLock"));
                return if lock { Walk::Into } else { Walk::Skip };
            }
            Walk::Into
        },
        &mut |_, _| {},
    );
    let whole = !stopped && cut.is_empty();
    (parts, whole)
}

/// Every `Arc<T>` with interior mutability in or behind `T` that values of
/// `roots` can hold ([`held_types`]: through the fields of the program's
/// types and its dependencies'), regions erased. Only an `Arc` whose `T`
/// names a type or trait of the program counts: matched by type, an
/// `Arc<AtomicBool>` says nothing about which cell it is.
fn arc_cells<'tcx>(
    tcx: TyCtxt<'tcx>,
    roots: impl Iterator<Item = Ty<'tcx>>,
    messages: &[Ty<'tcx>],
) -> Vec<Ty<'tcx>> {
    // The `Arc`s the roots can hold, each with what it holds.
    let mut arcs: Vec<(Ty<'tcx>, Ty<'tcx>)> = Vec::new();
    let roots = roots.map(|ty| tcx.erase_and_anonymize_regions(ty));
    held_types(
        tcx,
        roots,
        messages,
        &mut |inner| {
            let ty::Adt(adt, args) = *inner.kind() else { return Walk::Into };
            if !tcx.is_diagnostic_item(sym::Arc, adt.did()) || inner.has_escaping_bound_vars() {
                return Walk::Into;
            }
            let held = args.type_at(0);
            let named = held.walk().any(|arg| match arg.kind() {
                GenericArgKind::Type(part) => match *part.kind() {
                    ty::Adt(adt, _) => !crate::def_is_in_sysroot_resident_crate(tcx, adt.did()),
                    ty::Dynamic(predicates, ..) => {
                        predicates.principal_def_id().is_some_and(|principal| {
                            !crate::def_is_in_sysroot_resident_crate(tcx, principal)
                        })
                    }
                    _ => false,
                },
                _ => false,
            });
            if named && !held.has_param() {
                arcs.push((inner, at_instance(tcx, None, held)));
            }
            Walk::Into
        },
        &mut |_, _| {},
    );
    // Which of those hold a cell: one walk for all of them.
    let held: Vec<Ty<'tcx>> = arcs.iter().map(|&(_, held)| held).collect();
    let interior = reaching(tcx, &held, messages, &|part| is_cell(tcx, part), true);
    arcs.into_iter().filter(|(_, held)| interior.contains(held)).map(|(arc, _)| arc).collect()
}

/// The shared-state census, after the consumer census (`-Ztrust-send-census`).
/// For each consumer, the cells it and another thread can both reach: the
/// crate's own statics with interior mutability (or `static mut`) that the
/// consumer and the thread read over the calls the census resolved, and an
/// `Arc` of interior-mutable data that the thread's closure captures and that
/// the consumer's arguments (its `self`) can hold, or that holds the type the
/// consumer runs on (`Arc<Mutex<App>>` beside `App::on_wake`), matched by
/// type. The thread that runs the consumer is left out: one whose resolved
/// calls reach it, or, when none does (a handler foreign code calls back, as
/// winit's run loop calls `App::user_event`), `main`. Threads that share the
/// same cells with a consumer get one note. A model may treat such a cell
/// under interleaving only if it publishes no data (design §3b.4); this census
/// names the cells, not their orderings.
fn report_shared<'tcx>(
    render: &Render<'_, 'tcx>,
    messages: &[Ty<'tcx>],
    threads: &[Thread],
    consumers: &[Consumer<'tcx>],
) {
    let tcx = render.tcx;
    let mut defs: Vec<LocalDefId> = Vec::new();
    for consumer in consumers {
        if !defs.contains(&consumer.def) {
            defs.push(consumer.def);
        }
    }
    if defs.is_empty() {
        return;
    }
    let expanded = render.census.expanded();
    let mut run_out: FxHashMap<ReachNode, Vec<ReachNode>> = FxHashMap::default();
    let mut read_out: FxHashMap<ReachNode, Vec<ReachNode>> = FxHashMap::default();
    for edge in expanded.edges() {
        match edge.class {
            EdgeClass::Run => run_out.entry(edge.from).or_default().push(edge.to),
            EdgeClass::Read => read_out.entry(edge.from).or_default().push(edge.to),
            _ => {}
        }
    }
    let is_seed = |node: ReachNode| {
        matches!(
            expanded.node(node),
            Some(ReachNodeKind::Program(ReachNodeSpec { body: NodeBody::Seed, .. }))
        )
    };
    let statics_of = |reach: &FxHashSet<ReachNode>| {
        // What the bodies read, and what those constants and statics point at
        // in turn (`static ALIAS: &AtomicBool = &HIDDEN`).
        let mut values: FxHashSet<ReachNode> = FxHashSet::default();
        let mut pending: Vec<ReachNode> = reach
            .iter()
            .flat_map(|node| read_out.get(node).map_or(&[][..], Vec::as_slice))
            .copied()
            .collect();
        while let Some(node) = pending.pop() {
            if values.insert(node) {
                pending.extend(read_out.get(&node).map_or(&[][..], Vec::as_slice));
            }
        }
        let mut statics: Vec<DefId> = values
            .iter()
            .filter_map(|&node| match render.key(node) {
                Some(Key::Value { def, .. }) if def.is_local() && is_shared_static(tcx, def) => {
                    Some(def)
                }
                _ => None,
            })
            .collect();
        statics.sort_by_key(|def| tcx.def_path_str(*def));
        statics.dedup();
        statics
    };
    // What a closure or an async body captures.
    let upvars = |ty: Ty<'tcx>| match *ty.kind() {
        ty::Closure(_, args) => arc_cells(tcx, args.as_closure().upvar_tys().iter(), messages),
        ty::Coroutine(_, args) => arc_cells(tcx, args.as_coroutine().upvar_tys().iter(), messages),
        ty::CoroutineClosure(_, args) => {
            arc_cells(tcx, args.as_coroutine_closure().upvar_tys().iter(), messages)
        }
        _ => Vec::new(),
    };
    let captures = |entry: Option<ReachNode>| {
        entry
            .and_then(|entry| entry_closure(render, entry))
            .map_or_else(Vec::new, |(_, closure)| upvars(closure))
    };
    let per_thread: Vec<(Vec<DefId>, Vec<Ty<'tcx>>)> =
        threads.iter().map(|thread| (statics_of(&thread.exact), captures(thread.entry))).collect();
    for consumer in defs {
        // Every instance of the consumer: a generic one is run at its
        // instances, never at its own parameters.
        let nodes: Vec<ReachNode> = expanded
            .nodes()
            .map(|(node, _)| node)
            .filter(|node| {
                matches!(render.key(*node), Some(Key::Body { def, .. }) if def == consumer.to_def_id())
            })
            .collect();
        if nodes.is_empty() {
            continue;
        }
        let mut reach: FxHashSet<ReachNode> = nodes.iter().copied().collect();
        let mut queue: VecDeque<ReachNode> = nodes.iter().copied().collect();
        while let Some(node) = queue.pop_front() {
            if is_seed(node) {
                continue;
            }
            for &to in run_out.get(&node).map_or(&[][..], Vec::as_slice) {
                if reach.insert(to) {
                    queue.push_back(to);
                }
            }
        }
        let statics = statics_of(&reach);
        // What the consumer's arguments can hold (a closure's, its captures),
        // and the types it runs on, at each instance the program makes of it
        // (a generic `self`, a provided method and a blanket impl run at
        // their instances) and, when it makes none, at its own parameters.
        // `fn_sig` is a fn item's alone.
        let generics = tcx.generics_of(consumer).count();
        let mut at: Vec<Option<GenericArgs<'tcx>>> = nodes
            .iter()
            .filter_map(|node| match render.key(*node) {
                Some(Key::Body { args, .. })
                    if args.len() == generics && !args.has_non_region_param() =>
                {
                    Some(Some(args))
                }
                _ => None,
            })
            .collect();
        at.dedup();
        if at.is_empty() {
            at.push(None);
        }
        let mut held: Vec<Ty<'tcx>> = Vec::new();
        let mut runs_on: Vec<Ty<'tcx>> = Vec::new();
        for args in at {
            let this = match args {
                Some(args) => tcx.type_of(consumer).instantiate(tcx, args).skip_norm_wip(),
                None => tcx.type_of(consumer).instantiate_identity().skip_norm_wip(),
            };
            let cells = match *this.kind() {
                ty::FnDef(..) => {
                    let sig = erased_sig(tcx, consumer.to_def_id(), args);
                    for input in sig.inputs() {
                        let on = receiver_pointee(tcx, at_instance(tcx, None, *input));
                        if matches!(on.kind(), ty::Adt(adt, _) if adt.did().is_local())
                            && !messages.contains(&on)
                            && !runs_on.contains(&on)
                        {
                            runs_on.push(on);
                        }
                    }
                    arc_cells(tcx, sig.inputs().iter().copied(), messages)
                }
                _ => upvars(this),
            };
            for cell in cells {
                if !held.contains(&cell) {
                    held.push(cell);
                }
            }
        }
        let name = tcx.def_path_str(consumer);
        // Threads that share the same cells with this consumer, together: on
        // a program whose every worker can drop a message that owns a cleanup
        // lease, dozens of threads share one list.
        let mut shared: Vec<(String, Vec<&Thread>)> = Vec::new();
        // The thread that runs the consumer shares nothing with itself. More
        // than one that runs it (a pool of workers on one handler) share
        // with each other every cell the consumer reaches.
        let runners =
            threads.iter().filter(|thread| runs_consumer(thread, threads, &nodes)).count();
        for (thread, (thread_statics, thread_arcs)) in threads.iter().zip(&per_thread) {
            let runs = runs_consumer(thread, threads, &nodes);
            if runs && runners < 2 {
                continue;
            }
            // The shared statics, grouped by how they synchronize.
            let mut groups: Vec<(&str, Vec<String>)> = Vec::new();
            for &def in thread_statics.iter().filter(|def| statics.contains(def)) {
                let kind = static_kind(tcx, def, messages);
                let name = if kind == "interior-mutable" {
                    format!("`{}` (`{}`)", tcx.def_path_str(def), static_ty(tcx, def))
                } else {
                    format!("`{}`", tcx.def_path_str(def))
                };
                match groups.iter_mut().find(|(seen, _)| *seen == kind) {
                    Some((_, names)) => names.push(name),
                    None => groups.push((kind, vec![name])),
                }
            }
            const ORDER: [&str; 5] = [
                "unsynchronized (`static mut`)",
                "atomic",
                "locked",
                "interior-mutable",
                "set-once",
            ];
            groups.sort_by_key(|(kind, _)| ORDER.iter().position(|seen| seen == kind));
            let both: Vec<String> = groups
                .iter()
                .map(|(kind, names)| {
                    let noun = if names.len() == 1 { "static" } else { "statics" };
                    format!("the {kind} {noun} {}", and_list(names))
                })
                .collect();
            let mut arcs: Vec<String> = thread_arcs
                .iter()
                .filter(|ty| held.contains(ty))
                .map(|ty| format!("`{ty}`"))
                .collect();
            // (A family of types that name each other at ever larger
            // instantiations holds as many `Arc`s as the walk has room for:
            // the first few stand for them.)
            const NAMED: usize = 12;
            if arcs.len() > NAMED {
                let more = arcs.len() - NAMED;
                arcs.truncate(NAMED);
                arcs.push(format!("{more} more"));
            }
            // An `Arc` of the very type the consumer runs on: one that holds
            // a value of it (an `Arc<Mutex<App>>`, or a type with one in a
            // field), not one that names it in a signature
            // (`Box<dyn Fn(&mut App)>`) or only as a type argument of its
            // own. One walk per type the consumer runs on.
            let rest: Vec<Ty<'tcx>> =
                thread_arcs.iter().copied().filter(|ty| !held.contains(ty)).collect();
            let holding: Vec<(Ty<'tcx>, FxHashSet<Ty<'tcx>>)> = if rest.is_empty() {
                Vec::new()
            } else {
                runs_on
                    .iter()
                    .map(|&on| (on, reaching(tcx, &rest, &[], &|part| part == on, false)))
                    .collect()
            };
            let own: Vec<String> = rest
                .iter()
                .filter_map(|ty| {
                    let at = at_instance(tcx, None, *ty);
                    let (on, _) = holding.iter().find(|(_, holders)| holders.contains(&at))?;
                    Some(format!("`{ty}` (the consumer runs on the `{on}` in it)"))
                })
                .collect();
            let mut parts: Vec<String> = Vec::new();
            if !both.is_empty() {
                parts.push(format!("both reach {}", both.join("; ")));
            }
            if !arcs.is_empty() {
                parts.push(format!("both hold {}, matched by type", and_list(&arcs)));
            }
            if !own.is_empty() {
                parts.push(format!("share {}, matched by type", and_list(&own)));
            }
            if parts.is_empty() {
                continue;
            }
            let mut cells = and_list(&parts);
            if runs {
                cells.push_str(&format!(
                    " (it is one of {runners} threads that run the consumer: they share these \
                     with each other)"
                ));
            }
            match shared.iter_mut().find(|(seen, _)| *seen == cells) {
                Some((_, group)) => group.push(thread),
                None => shared.push((cells, vec![thread])),
            }
        }
        for (cells, group) in shared {
            let first = group[0];
            let this = if first.span.is_some() {
                "this thread".to_owned()
            } else {
                format!("the thread {}", first.named)
            };
            let mut text = format!("shared-state census: {this} and the consumer `{name}` {cells}");
            if group.len() > 1 {
                let names: Vec<String> =
                    group[1..].iter().map(|thread| thread.named.clone()).collect();
                text.push_str(&format!(
                    ". So do {} other thread(s): {}",
                    names.len(),
                    and_list(&names)
                ));
            }
            note_at(tcx, first.span, text);
        }
    }
}

/// What holds a field on a path: a struct, by definition (any instantiation
/// of it), or a tuple type.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Holder<'tcx> {
    Adt(DefId),
    Tuple(Ty<'tcx>),
}

/// A field path on a consumer's argument, resolved for the writer census.
struct BoundPlace<'tcx> {
    /// `App.config.harness`.
    label: String,
    /// The types a write of a whole value of which replaces the field: the
    /// ones on the path, outermost first (`App`, `Config`), each `Box` on it
    /// as its own type (`Box<Config>`), and the crate's types that hold the
    /// root by value ([`holders`]).
    containers: Vec<Ty<'tcx>>,
    /// The path: each holder with the field taken in it. The last is the
    /// field itself.
    steps: Vec<(Holder<'tcx>, usize)>,
    /// The type of each step's holder (`App`, `Slot<Config>`), in step order.
    step_tys: Vec<Ty<'tcx>>,
    /// The type the path starts on.
    root: Ty<'tcx>,
    /// Which types hold a `root` by value ([`holds_by_value`]), found as
    /// writes of them are met.
    holders: std::cell::RefCell<FxHashMap<Ty<'tcx>, bool>>,
    /// The field's type.
    field_ty: Ty<'tcx>,
    /// The pointees of every `Box` on the path, and of the field when it is
    /// one: a write into a boxed value goes through a raw pointer to it.
    boxed: Vec<Ty<'tcx>>,
    /// Whether the field has interior mutability, so a `&` of it can write
    /// it: in itself, or in a value it owns ([`owns_interior`]).
    interior: bool,
    /// Whether some consumer takes the value it runs on by `&` (`&self`, an
    /// `Rc<Self>`): lending the whole value by `&` is then lending it to a
    /// consumer. Set as the consumers are found.
    shared: std::cell::Cell<bool>,
}

/// Whether a `&` of a value of type `ty` can lead to a write of it: the type
/// has interior mutability, in itself or in a value it OWNS through a `Box`
/// or one of std's collections (a `Box<Cell<u8>>`, a `Vec<AtomicU8>`: rustc's
/// `Freeze` sees only what is stored inline). Not behind an `Rc`, an `Arc`
/// or a pointer: what is there is shared, and no part of the value.
fn owns_interior<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>, depth: usize) -> bool {
    // A worklist: each type is asked once (an expression tree with twenty
    // fields of its own type is one question, not twenty to the sixth), and
    // no deeper than six types down, where a type that grows as it is
    // walked (`Nest<T>` holding a `Nest<(T, T)>`) would never end.
    let mut seen: FxHashSet<Ty<'tcx>> = FxHashSet::default();
    let mut work: Vec<(Ty<'tcx>, usize)> = vec![(ty, depth)];
    while let Some((part, depth)) = work.pop() {
        if part.has_param() || part.has_escaping_bound_vars() || !seen.insert(part) {
            continue;
        }
        if !part.is_freeze(tcx, ty::TypingEnv::fully_monomorphized()) {
            return true;
        }
        if depth > 6 {
            continue;
        }
        match *part.kind() {
            ty::Adt(adt, args) => {
                if tcx.is_diagnostic_item(sym::Rc, adt.did())
                    || tcx.is_diagnostic_item(sym::Arc, adt.did())
                {
                    continue;
                }
                if crate::def_is_in_sysroot_resident_crate(tcx, adt.did()) {
                    work.extend(args.types().map(|inner| (inner, depth + 1)));
                } else {
                    work.extend(adt.all_fields().map(|field| {
                        (at_instance(tcx, None, field.ty(tcx, args).skip_norm_wip()), depth + 1)
                    }));
                }
            }
            ty::Tuple(fields) => work.extend(fields.iter().map(|inner| (inner, depth + 1))),
            ty::Array(inner, _) | ty::Slice(inner) => work.push((inner, depth + 1)),
            _ => {}
        }
    }
    false
}

/// `segments` (`["config", "harness"]`) as a field path on `root`, through
/// structs, tuples (`pair.0`) and boxes of them, each field's type normalized
/// in `typing_env` (a field declared with an associated type), regions erased.
/// A segment may be a raw identifier (`r#type`).
fn resolve_place<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    root: Ty<'tcx>,
    segments: &[&str],
) -> Option<BoundPlace<'tcx>> {
    let mut ty = root;
    let mut containers = Vec::new();
    let mut boxed = Vec::new();
    let mut steps = Vec::new();
    let mut step_tys = Vec::new();
    for segment in segments {
        let segment = segment.strip_prefix("r#").unwrap_or(segment);
        while let Some(inner) = ty.boxed_ty() {
            // Replacing the box replaces what it holds.
            containers.push(ty);
            boxed.push(inner);
            ty = inner;
        }
        let declared = match *ty.kind() {
            ty::Adt(adt, args) if adt.is_struct() => {
                let (index, def) = adt
                    .non_enum_variant()
                    .fields
                    .iter_enumerated()
                    .find(|(_, def)| def.name.as_str() == segment)?;
                // Another crate's private field is no path a program writes
                // (`Pin`'s own `pointer`).
                if !adt.did().is_local() && !def.vis.is_public() {
                    return None;
                }
                steps.push((Holder::Adt(adt.did()), index.as_usize()));
                def.ty(tcx, args)
            }
            ty::Tuple(fields) => {
                let index: usize = segment.parse().ok()?;
                let field = *fields.get(index)?;
                steps.push((Holder::Tuple(ty), index));
                ty::Unnormalized::new_wip(field)
            }
            _ => return None,
        };
        containers.push(ty);
        step_tys.push(ty);
        ty = tcx
            .try_normalize_erasing_regions(typing_env, declared)
            .unwrap_or_else(|_| tcx.erase_and_anonymize_regions(declared.skip_norm_wip()));
    }
    if steps.is_empty() {
        return None;
    }
    let mut held = ty;
    while let Some(inner) = held.boxed_ty() {
        boxed.push(inner);
        held = inner;
    }
    let interior = owns_interior(tcx, ty, 0);
    Some(BoundPlace {
        label: format!("{root}.{}", segments.join(".")),
        containers,
        steps,
        step_tys,
        root,
        holders: std::cell::RefCell::new(FxHashMap::default()),
        field_ty: ty,
        boxed,
        interior,
        shared: std::cell::Cell::new(false),
    })
}

impl<'tcx> BoundPlace<'tcx> {
    /// Whether `ty` is the type the path starts on: the type itself, or, for
    /// a consumer generic over its `self`, an instance of it (`App<u8>` for
    /// `App<S>`).
    fn is_root(&self, ty: Ty<'tcx>) -> bool {
        ty == self.root || (self.root.has_non_region_param() && could_be(self.root, ty))
    }

    /// Whether a `&` of a value of type `ty` can write the bound field. Of a
    /// type on the path (`App`, `Config`): only when the field itself has
    /// interior mutability (a `Cell` beside the path is no way to the
    /// field). Of any other type: when it has interior mutability, in itself
    /// or in a value it owns (a `RefCell<App>`, a `Cell<u8>` inside the
    /// field).
    fn shared_writes(&self, tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> bool {
        if self.is_root(ty) || self.containers.contains(&ty) {
            self.interior
        } else {
            owns_interior(tcx, ty, 0)
        }
    }

    /// Whether a value of type `ty` holds the path's root by value, so that
    /// replacing a whole one replaces the field: one of the crate's types
    /// with the root in a field (`Host { app: App }`, `Host<App>`), a `Box`,
    /// an `Option`, a tuple or an array of one. Not through an `Arc` or an
    /// `Rc`, whose replacement drops a count. A generic root is matched by
    /// type nowhere.
    fn holds(&self, tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> bool {
        if ty == self.root || (self.root.has_non_region_param() && could_be(self.root, ty)) {
            return false;
        }
        if !matches!(ty.kind(), ty::Adt(..) | ty::Tuple(..) | ty::Array(..) | ty::Slice(..)) {
            return false;
        }
        holds_by_value(tcx, ty, self.root, &mut self.holders.borrow_mut())
    }
}

/// Whether a value of type `ty` holds a `root` by value ([`BoundPlace::holds`]).
/// `known` memoizes across calls; `expanded` bounds one search on a
/// polymorphically recursive type ([`EXPANSIONS`]).
fn holds_by_value<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>,
    root: Ty<'tcx>,
    known: &mut FxHashMap<Ty<'tcx>, bool>,
) -> bool {
    if let Some(&found) = known.get(&ty) {
        return found;
    }
    // (A consumer generic over its `self` runs on each instance of it.)
    let is_root = |ty: Ty<'tcx>| ty == root || (root.has_non_region_param() && could_be(root, ty));
    // A worklist: a type that holds its next instantiation by value
    // (`Nest<T>` with a `ManuallyDrop<Box<Nest<Option<T>>>>`) is as deep as
    // the bound lets it be, which a recursion would spend its stack on.
    let mut seen: FxHashSet<Ty<'tcx>> = FxHashSet::default();
    let mut expanded: FxHashMap<DefId, usize> = FxHashMap::default();
    let mut work: Vec<Ty<'tcx>> = vec![ty];
    let mut found = false;
    while let Some(part) = work.pop() {
        if is_root(part) {
            found = true;
            break;
        }
        if !seen.insert(part) {
            continue;
        }
        match *part.kind() {
            ty::Adt(adt, _)
                if tcx.is_diagnostic_item(sym::Arc, adt.did())
                    || tcx.is_diagnostic_item(sym::Rc, adt.did())
                    || adt.is_phantom_data() => {}
            // Replacing a box replaces what it holds.
            ty::Adt(adt, args) if adt.is_box() => work.push(args.type_at(0)),
            // What a type holds is in its fields, whichever crate defines
            // it: a type argument says what it names (`Weak<App>`,
            // `Sender<App>`, an `Id<App>` around a `PhantomData`), not what
            // it stores.
            ty::Adt(adt, args) => {
                let count = expanded.entry(adt.did()).or_default();
                if *count >= HOLDER_EXPANSIONS {
                    continue;
                }
                *count += 1;
                for field in adt.all_fields() {
                    // A field spelled through an associated type is the
                    // type it names.
                    let declared = field.ty(tcx, args);
                    work.push(if args.has_non_region_param() {
                        tcx.erase_and_anonymize_regions(declared.skip_norm_wip())
                    } else {
                        tcx.try_normalize_erasing_regions(
                            ty::TypingEnv::fully_monomorphized(),
                            declared,
                        )
                        .unwrap_or_else(|_| {
                            tcx.erase_and_anonymize_regions(declared.skip_norm_wip())
                        })
                    });
                }
            }
            ty::Tuple(fields) => work.extend(fields.iter()),
            ty::Array(element, _) | ty::Slice(element) => work.push(element),
            _ => {}
        }
    }
    known.insert(ty, found);
    found
}

/// How many instantiations of one definition [`holds_by_value`] opens: a
/// type that holds its next instantiation by value has no last one.
const HOLDER_EXPANSIONS: usize = 256;

/// The place of the `Box` a pointer was loaded out of, when `place` is one
/// read inside a box (`((_b.0: Unique<T>).0: NonNull<T>)`, as MIR dereferences
/// a box): the longest prefix of it that is a box, short of the whole.
fn box_loaded_from<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
    place: mir::Place<'tcx>,
) -> Option<mir::Place<'tcx>> {
    let len = (0..place.projection.len()).rev().find(|&len| {
        mir::PlaceRef { local: place.local, projection: &place.projection[..len] }
            .ty(body, tcx)
            .ty
            .is_box()
    })?;
    Some(mir::Place {
        local: place.local,
        projection: tcx.mk_place_elems(&place.projection[..len]),
    })
}

/// How a write to `place` may overlap `bound`, as the verb of a note ("this
/// writes `App.config.harness`") and whether its path passes the field itself
/// (not only a value that may hold it), or `None`.
///
/// A write counts only when it goes through a pointer, or into one of
/// `owners`: the consumer's own argument when it takes it by value, or a
/// local a consumer may run on because the body lends it out. A write into
/// any other local value is that body's own copy. It overlaps when its path passes the
/// field; or, by type alone, when it writes a whole value of a type that
/// holds the field (`self.config = config`), a whole pointee of the field's
/// type (`*slot = v`), or the pointee of a `Box` that is the field
/// (`self.config.boxed[0] = 1` is a write through a raw pointer to the boxed
/// value). A write that passes another field of a type on the path
/// (`self.config.theme`) is a sibling's, whichever value it is. A type on the
/// path is matched as the type it is: the same field of another instantiation
/// (`Slot<String>` for the path's `Slot<Config>`) is another type's, and
/// generic code that writes the whole value at a place on the path
/// (`self.inner = v` in `Slot<T>::set`) is a write of it at the instances
/// that make it one: a generic body is read at each instance the program
/// makes of it (`subst`), where its types are the instance's.
///
/// `beside` is set when the answer is `None` because the PATH says so: the
/// place is in a value on the path, at a field that is not the way to the
/// bound one (a sibling). A `None` without it is only "no type matched".
fn overlap<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
    place: mir::Place<'tcx>,
    bound: &BoundPlace<'tcx>,
    owners: &FxHashSet<mir::Local>,
    subst: Option<GenericArgs<'tcx>>,
    beside: &mut bool,
) -> Option<(String, bool)> {
    let prefix = |len: usize| {
        let ty = mir::PlaceRef { local: place.local, projection: &place.projection[..len] }
            .ty(body, tcx)
            .ty;
        at_instance(tcx, subst, ty)
    };
    // Whether a value of type `seen` can be the holder of step `step`: the
    // same type; or, where one of the two still has type parameters (a
    // generic body read as written, a generic consumer's `App<S>`), a type
    // the parameters can make it ([`could_be`]). Another instantiation
    // (`Slot<String>` for the path's `Slot<Config>`) is another type.
    let holds_step = |seen: Ty<'tcx>, step: usize| match (bound.steps[step].0, seen.kind()) {
        (Holder::Adt(def), ty::Adt(adt, _)) => {
            let declared = bound.step_tys[step];
            adt.did() == def
                && (seen == declared
                    || declared.has_non_region_param()
                    || (seen.has_non_region_param() && could_be(seen, declared)))
        }
        (Holder::Tuple(tuple), ty::Tuple(_)) => seen == tuple,
        _ => false,
    };
    let last = bound.steps.len().checked_sub(1)?;
    // A whole value assigned to a variable itself is a new value (`let mut
    // app = App { .. }`), not a write into one.
    if place.projection.is_empty() {
        return None;
    }
    let mut through = owners.contains(&place.local);
    let mut last_deref = None;
    // The last projection that took a field on the path, short of the field
    // itself, with its step.
    let mut on_path = None;
    for (index, elem) in place.projection.iter().enumerate() {
        match elem {
            mir::ProjectionElem::Deref => {
                through = true;
                last_deref = Some(index);
            }
            mir::ProjectionElem::Field(taken, _) if through => {
                let seen = prefix(index);
                let taken = taken.as_usize();
                // The deepest step it can be: a wrapper used at two places
                // on the path, read as written, is the field's own holder
                // at one instance and an outer one at another, and the
                // field's is the one that must not be missed.
                let step = (0..=last)
                    .rev()
                    .find(|&step| bound.steps[step].1 == taken && holds_step(seen, step));
                match step {
                    Some(step) if step == last => {
                        // (What a `Box` that is the field points to is the
                        // field: the whole of it.)
                        let whole = match &place.projection[index + 1..] {
                            [] => true,
                            [mir::ProjectionElem::Deref] => bound.field_ty.is_box(),
                            _ => false,
                        };
                        let verb = if whole { "writes" } else { "writes part of" };
                        return Some((verb.to_owned(), true));
                    }
                    Some(step) => on_path = Some((index, step)),
                    // Another field of a type on the path: a sibling's.
                    None if (0..=last).any(|step| holds_step(seen, step)) => {
                        *beside = true;
                        return None;
                    }
                    // A field of a value that holds the consumer's
                    // (`Session { app, backup }`, `(App, Config)`) that is
                    // not the way to it: a sibling of the value itself.
                    None if bound.holds(tcx, seen) => {
                        let next = prefix(index + 1);
                        if !bound.is_root(next) && !bound.holds(tcx, next) {
                            *beside = true;
                            return None;
                        }
                    }
                    None => {}
                }
            }
            _ => {}
        }
    }
    if !through {
        return None;
    }
    let ty = at_instance(tcx, subst, place.ty(body, tcx).ty);
    // (A container of a consumer generic over its `self` is each instance of
    // it: `App<Null>` for the path's `App<S>`.)
    let container = bound.containers.contains(&ty)
        || bound
            .containers
            .iter()
            .any(|container| container.has_non_region_param() && could_be(*container, ty));
    if container || bound.holds(tcx, ty) {
        return Some((format!("writes a whole `{ty}` holding"), false));
    }
    // Generic code, read as written, that writes the whole value at a place
    // on the path (`self.inner = v` in `Slot<T>::set`, for the path's
    // `Slot<Config>`): no type says so, the path does.
    if let Some((index, step)) = on_path {
        if index + 1 == place.projection.len()
            && ty.has_non_region_param()
            && could_be(ty, bound.step_tys[step + 1])
        {
            return Some((
                format!("writes a whole `{ty}`, in generic code the value holding"),
                false,
            ));
        }
    }
    let deref = last_deref?;
    if ty == bound.field_ty && deref + 1 == place.projection.len() {
        return Some((format!("writes a `{ty}` through a pointer, which may be"), false));
    }
    let pointee = prefix(deref + 1);
    if bound.boxed.contains(&pointee) && !bound.containers.contains(&pointee) {
        let part = if deref + 1 == place.projection.len() { "" } else { "part of " };
        return Some((format!("writes {part}a `{pointee}`, which may be the one boxed in"), false));
    }
    None
}

/// The type an argument is a pointer to, behind references and the pointers
/// a receiver can be (`Pin<&mut Self>`, `Box<Self>`, `Rc<Self>`, `Arc<Self>`).
fn receiver_pointee<'tcx>(tcx: TyCtxt<'tcx>, mut ty: Ty<'tcx>) -> Ty<'tcx> {
    loop {
        ty = ty.peel_refs();
        let inner = match *ty.kind() {
            ty::Adt(adt, args)
                if adt.is_box()
                    || tcx.is_lang_item(adt.did(), LangItem::Pin)
                    || tcx.is_diagnostic_item(sym::Arc, adt.did())
                    || tcx.is_diagnostic_item(sym::Rc, adt.did()) =>
            {
                args.types().next()
            }
            _ => None,
        };
        match inner {
            Some(inner) => ty = inner,
            None => break ty,
        }
    }
}

/// How a consumer reaches a site: through its arms for the variants in each
/// set, one set per message it dispatches on (blocks a switch over the message
/// has narrowed), and whether it also reaches it outside them (a block every
/// variant reaches: before the dispatch, after it, between a receive and the
/// switch).
type Reach = (Vec<VariantSet>, bool);

/// A consumer one of whose arguments has the path, with what attributing a
/// site to it needs.
struct Target<'a, 'tcx> {
    def: LocalDefId,
    /// Its dispatches: one per message type it consumes.
    group: Vec<&'a Consumer<'tcx>>,
    name: String,
    /// The argument, when the consumer takes it by value: it owns it, and a
    /// write into that local is a write of the field.
    owner: Option<mir::Local>,
    /// Where the consumer calls or drops: the blocks, by span, each with the
    /// fn it calls when the call names one.
    blocks_at: FxHashMap<Span, Vec<(mir::BasicBlock, Option<DefId>)>>,
    nodes: Vec<ReachNode>,
    /// It takes the value it runs on BY VALUE and returns one of its type
    /// (`fn step(self, m: Msg) -> Self`): the next state is a new value the
    /// census does not follow, so a field set while building it is no site.
    returns_next: bool,
}

/// One site that may write a field, with what reaches it.
struct WriteSite {
    /// The body the site is in.
    def: LocalDefId,
    span: Span,
    /// What it does to the field, as a note's verb ("writes", "takes a
    /// `&mut` of").
    verb: String,
    /// How each consumer of the field reaches it, in the field's order.
    reach: Vec<Reach>,
    /// The threads that reach it around every consumer, as a note names
    /// them.
    threads: Vec<String>,
    /// In a test build: nothing but the test harness reaches it.
    test_only: bool,
}

/// A field the path names: the type it resolves on, the consumers that run
/// on that type, and the sites that may write it.
struct WrittenField<'a, 'tcx> {
    root: Ty<'tcx>,
    bound: BoundPlace<'tcx>,
    targets: Vec<Target<'a, 'tcx>>,
    sites: Vec<WriteSite>,
}

/// How a note says `target` reaches a site.
fn reach_labels(target: &Target<'_, '_>, (arms, outside): &Reach) -> Vec<String> {
    let name = &target.name;
    let mut labels: Vec<String> = Vec::new();
    for (consumer, arms) in target.group.iter().zip(arms) {
        let total = consumer.names.len();
        let named = |variants: Vec<usize>| {
            let names: Vec<String> = variants
                .iter()
                .map(|variant| format!("`{}::{}`", consumer.message, consumer.names[*variant]))
                .collect();
            and_list(&names)
        };
        let over = if target.group.len() > 1 {
            format!(" over `{}`", consumer.message)
        } else {
            String::new()
        };
        let count = arms.count();
        if count == total && total > 1 {
            labels.push(format!("every arm of `{name}`{over}"));
        } else if count == 1 {
            labels.push(format!("the arm for {} in `{name}`", named(arms.iter().collect())));
        } else if count > 0 && (count <= 8 || count * 2 <= total) {
            labels
                .push(format!("the {count} arms for {} in `{name}`", named(arms.iter().collect())));
        } else if count > 0 {
            let others: Vec<usize> =
                (0..total).filter(|variant| !arms.contains(*variant)).collect();
            labels.push(format!("every arm of `{name}`{over} but those for {}", named(others)));
        }
    }
    if *outside {
        labels.push(format!("`{name}` outside its arms"));
    }
    labels
}

/// The arguments of the instance `node` is, when it is one of a generic body
/// with nothing left to instantiate.
fn instance_args<'tcx>(render: &Render<'_, 'tcx>, node: ReachNode) -> Option<GenericArgs<'tcx>> {
    match render.key(node) {
        Some(Key::Body { args, .. }) if !args.is_empty() && !args.has_non_region_param() => {
            Some(args)
        }
        _ => None,
    }
}

/// Whether the type `seen`, spelled with a generic body's own parameters,
/// can be `declared` at some instance: equal where it is concrete, anything
/// at a parameter or an associated type. (One parameter in two places is not
/// held to one type.)
fn could_be<'tcx>(seen: Ty<'tcx>, declared: Ty<'tcx>) -> bool {
    if seen == declared {
        return true;
    }
    match (seen.kind(), declared.kind()) {
        (ty::Param(_) | ty::Alias(..), _) => true,
        (ty::Adt(seen, seen_args), ty::Adt(declared, declared_args)) => {
            seen.did() == declared.did()
                && seen_args
                    .types()
                    .zip(declared_args.types())
                    .all(|(seen, declared)| could_be(seen, declared))
        }
        (ty::Tuple(seen), ty::Tuple(declared)) => {
            seen.len() == declared.len()
                && seen.iter().zip(declared.iter()).all(|(seen, declared)| could_be(seen, declared))
        }
        (ty::Ref(_, seen, seen_mut), ty::Ref(_, declared, declared_mut))
        | (ty::RawPtr(seen, seen_mut), ty::RawPtr(declared, declared_mut)) => {
            seen_mut == declared_mut && could_be(*seen, *declared)
        }
        (ty::Array(seen, _), ty::Array(declared, _)) | (ty::Slice(seen), ty::Slice(declared)) => {
            could_be(*seen, *declared)
        }
        // A fn item, and a closure of a generic fn (`outer<T>::{closure#0}`
        // for `outer<u8>::{closure#0}`): the same item, at arguments that
        // can be those. (A closure's arguments are its parent's, then types
        // made from them.)
        (ty::FnDef(seen, seen_args), ty::FnDef(declared, declared_args)) => {
            let (seen_args, declared_args) = (seen_args.skip_binder(), declared_args.skip_binder());
            seen == declared
                && seen_args.len() == declared_args.len()
                && seen_args
                    .types()
                    .zip(declared_args.types())
                    .all(|(seen, declared)| could_be(seen, declared))
        }
        (ty::Closure(seen, seen_args), ty::Closure(declared, declared_args))
        | (ty::Coroutine(seen, seen_args), ty::Coroutine(declared, declared_args))
        | (ty::CoroutineClosure(seen, seen_args), ty::CoroutineClosure(declared, declared_args)) => {
            seen == declared
                && seen_args.len() == declared_args.len()
                && seen_args
                    .types()
                    .zip(declared_args.types())
                    .all(|(seen, declared)| could_be(seen, declared))
        }
        (ty::FnPtr(seen, _), ty::FnPtr(declared, _)) => {
            let (seen, declared) = (seen.skip_binder(), declared.skip_binder());
            seen.inputs_and_output.len() == declared.inputs_and_output.len()
                && seen
                    .inputs_and_output
                    .iter()
                    .zip(declared.inputs_and_output.iter())
                    .all(|(seen, declared)| could_be(seen, declared))
        }
        _ => false,
    }
}

/// The variables of `body` a consumer may run on: every one of the type the
/// path starts on, or of a type that holds it by value (`Host { app }`, an
/// `Option<App>`, a `Box<App>`). The census cannot tell one value of the
/// consumer's type from another, so each is the consumer's: a parameter, a
/// call's result, a scratch value. What a body is still MAKING is told apart
/// where the sites are found ([`writer_origins::scan_writes`]), by the order
/// of its statements; the facts hold in any order.
fn owned_locals<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
    bound: &BoundPlace<'tcx>,
    subst: Option<GenericArgs<'tcx>>,
    closure: bool,
) -> FxHashSet<mir::Local> {
    let env = mir::Local::from_usize(1);
    body.local_decls
        .iter_enumerated()
        .filter(|(local, decl)| {
            let ty = at_instance(tcx, subst, decl.ty);
            !(closure && *local == env) && (bound.is_root(ty) || bound.holds(tcx, ty))
        })
        .map(|(local, _)| local)
        .collect()
}

/// The fn a call runs by its callee operand: a fn item named in place, or
/// one held in a variable (`let take = mem::take::<Config>; take(slot)`: the
/// variable's type is the fn item).
fn callee_of<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
    func: &mir::Operand<'tcx>,
) -> Option<(DefId, GenericArgs<'tcx>)> {
    func.const_fn_def().or_else(|| match *func.ty(body, tcx).kind() {
        ty::FnDef(def, args) => Some((def, args.skip_binder())),
        _ => None,
    })
}

/// Whether parameter `index` of the fn `def` is declared `&T`: nothing can be
/// written through what it is given, whatever the fn returns.
fn declared_shared(tcx: TyCtxt<'_>, def: DefId, index: usize) -> bool {
    matches!(tcx.def_kind(def), DefKind::Fn | DefKind::AssocFn)
        && tcx
            .fn_sig(def)
            .instantiate_identity()
            .skip_norm_wip()
            .skip_binder()
            .inputs()
            .get(index)
            .is_some_and(|input| matches!(input.kind(), ty::Ref(_, _, ty::Mutability::Not)))
}

/// Whether parameter `index` of the fn `def` is declared `&T` or `*const T`:
/// nothing can be written through what it is given.
fn declared_read_only(tcx: TyCtxt<'_>, def: DefId, index: usize) -> bool {
    matches!(tcx.def_kind(def), DefKind::Fn | DefKind::AssocFn)
        && tcx
            .fn_sig(def)
            .instantiate_identity()
            .skip_norm_wip()
            .skip_binder()
            .inputs()
            .get(index)
            .is_some_and(|input| {
                matches!(
                    input.kind(),
                    ty::Ref(_, _, ty::Mutability::Not) | ty::RawPtr(_, ty::Mutability::Not)
                )
            })
}

/// One place in a body that may write a bound field.
struct Write<'tcx> {
    def: LocalDefId,
    block: mir::BasicBlock,
    /// The block is on an unwind path.
    cleanup: bool,
    span: Span,
    verb: String,
    /// The instance the body was read at ([`instance_args`]), or as written.
    subst: Option<GenericArgs<'tcx>>,
}

/// The fields `path` names on message consumers' arguments, each with every
/// local site that may write it and what reaches the site over resolved calls
/// and drops: what the writer census reports ([`report_writers`]) and what a
/// declared binding is checked against.
fn written_fields<'a, 'tcx>(
    render: &Render<'_, 'tcx>,
    hooks: &dyn CensusHooks<'tcx>,
    sites: &[(Option<LocalDefId>, Span)],
    threads: &[Thread],
    consumers: &'a [Consumer<'tcx>],
    path: &str,
    prefer: &dyn Fn(&Consumer<'tcx>, &VariantSet) -> bool,
) -> Vec<WrittenField<'a, 'tcx>> {
    let tcx = render.tcx;
    let segments: Vec<&str> = path.split('.').map(str::trim).filter(|s| !s.is_empty()).collect();
    let expanded = render.census.expanded();
    let mut callers_of: FxHashMap<ReachNode, Vec<ReachEdge>> = FxHashMap::default();
    for edge in expanded.edges() {
        if edge.class == EdgeClass::Run {
            callers_of.entry(edge.to).or_default().push(*edge);
        }
    }
    let is_seed = |node: ReachNode| {
        matches!(
            expanded.node(node),
            Some(ReachNodeKind::Program(ReachNodeSpec { body: NodeBody::Seed, .. }))
        )
    };
    let mut bodies: FxHashMap<DefId, Vec<ReachNode>> = FxHashMap::default();
    for (node, _) in expanded.nodes() {
        if let Some(Key::Body { def, .. }) = render.key(node) {
            bodies.entry(def).or_default().push(node);
        }
    }
    // What an indirect call or a hand-off may run: a fn pointer's or a
    // `dyn`'s pool, a callback foreign code is given, a callable made into a
    // value (its address is taken: whoever holds it can call it).
    let mut indirect: FxHashSet<ReachNode> = FxHashSet::default();
    for edge in expanded.edges() {
        if matches!(edge.class, EdgeClass::Approx | EdgeClass::Create) && !is_seed(edge.from) {
            indirect.insert(edge.to);
        }
    }
    // A test build: the bodies under a `#[test]`'s marker (the closure the
    // harness's table holds, which calls the test fn).
    let testing = tcx.sess.is_test_crate();
    let marked = |def: DefId| {
        def.is_local() && {
            let root = tcx.typeck_root_def_id(def);
            #[allow(deprecated)]
            let marked = tcx.get_all_attrs(root).iter().any(|attr| {
                matches!(
                    attr,
                    rustc_attr_ir::Attribute::Parsed(
                        rustc_attr_ir::AttributeKind::RustcTestMarker(..)
                    )
                )
            });
            marked
        }
    };
    let test_entry = |node: ReachNode| {
        match render.key(node) {
        Some(Key::Body { def, .. }) => marked(def),
        // The fn-pointer shim the harness's table holds for that closure.
        Some(Key::Shim { instance, .. }) => {
            marked(instance.def_id())
                || instance.args.types().next().is_some_and(|callable| {
                    matches!(*callable.kind(), ty::Closure(def, _) | ty::FnDef(def, _) if marked(def))
                })
        }
        _ => false,
    }
    };
    let defs = runtime_bodies(tcx);
    // The consumers by body: one that takes two message types is one
    // consumer with a dispatch per type.
    let mut groups: Vec<(LocalDefId, Vec<&Consumer<'tcx>>)> = Vec::new();
    for consumer in consumers {
        match groups.iter_mut().find(|(def, _)| *def == consumer.def) {
            Some((_, group)) => group.push(consumer),
            None => groups.push((consumer.def, vec![consumer])),
        }
    }
    let runnable: FxHashSet<LocalDefId> = defs.iter().copied().collect();
    // Every fn that is not the crate's own and is used as a VALUE somewhere
    // in it, by what it takes: `let take: fn(&mut Config) -> Config =
    // mem::take`, `.map(mem::take)`, `&mem::take as &dyn Fn(..)`, a fn item
    // kept in a variable, in a `const`, a `static` or a promoted constant. A
    // call the census cannot resolve (through a fn pointer, a `dyn Fn`, a
    // type parameter) may run any of them: it is a site when it is handed a
    // pointer of a type one of them takes. A value made from the crate's own
    // fns runs a body that is read on its own. A generic body is read at
    // the instances the program makes of it, as everywhere here: one it
    // makes none of never runs, and keeps no value. `None` in the set: a fn
    // that takes a type still to be instantiated at an instance, which could
    // be any.
    let mut foreign_inputs: FxHashSet<Option<Ty<'tcx>>> = FxHashSet::default();
    {
        use rustc_middle::mir::visit::Visitor;
        struct Values<'a, 'tcx> {
            tcx: TyCtxt<'tcx>,
            runnable: &'a FxHashSet<LocalDefId>,
            inputs: &'a mut FxHashSet<Option<Ty<'tcx>>>,
            /// The instance the body is read at.
            subst: Option<GenericArgs<'tcx>>,
            /// The callee of the call being visited: a fn named there is
            /// called, not kept.
            called: Option<Span>,
        }
        impl<'a, 'tcx> Visitor<'tcx> for Values<'a, 'tcx> {
            fn visit_terminator(&mut self, terminator: &mir::Terminator<'tcx>, at: Location) {
                self.called = match &terminator.kind {
                    TerminatorKind::Call { func: mir::Operand::Constant(func), .. }
                    | TerminatorKind::TailCall { func: mir::Operand::Constant(func), .. } => {
                        Some(func.span)
                    }
                    _ => None,
                };
                self.super_terminator(terminator, at);
                self.called = None;
            }

            fn visit_const_operand(&mut self, constant: &mir::ConstOperand<'tcx>, _: Location) {
                let ty::FnDef(def, args) = *constant.ty().kind() else { return };
                if self.called == Some(constant.span)
                    || def.as_local().is_some_and(|def| self.runnable.contains(&def))
                {
                    return;
                }
                let args = at_instance(self.tcx, self.subst, args);
                let sig =
                    self.tcx.fn_sig(def).instantiate(self.tcx, args.skip_binder()).skip_norm_wip();
                let sig = self.tcx.instantiate_bound_regions_with_erased(sig);
                for input in sig.inputs() {
                    let input = at_instance(self.tcx, None, *input);
                    if !input.has_non_region_param() {
                        self.inputs.insert(Some(input));
                    } else if self.subst.is_some() {
                        self.inputs.insert(None);
                    }
                }
            }
        }
        let mut values = Values {
            tcx,
            runnable: &runnable,
            inputs: &mut foreign_inputs,
            subst: None,
            called: None,
        };
        for &def in &defs {
            let mut instances: Vec<Option<GenericArgs<'tcx>>> = Vec::new();
            for node in bodies.get(&def.to_def_id()).map_or(&[][..], Vec::as_slice) {
                let Some(args) = instance_args(render, *node) else { continue };
                if !instances.contains(&Some(args)) {
                    instances.push(Some(args));
                }
            }
            if instances.is_empty() {
                instances.push(None);
            }
            for subst in instances {
                values.subst = subst;
                hooks.with_local_body(def, &mut |body| values.visit_body(body));
                for promoted in tcx.promoted_mir(def).iter() {
                    values.visit_body(promoted);
                }
            }
        }
        values.subst = None;
        // (A `const` or `static` can hold one too: `static TAKE: fn(&mut
        // Config) -> Config = mem::take`.)
        for def in tcx.hir_body_owners() {
            let held = match tcx.def_kind(def) {
                DefKind::Static { .. } => true,
                DefKind::Const { .. } | DefKind::AssocConst { .. } => {
                    tcx.trivial_const(def).is_none()
                }
                _ => false,
            };
            if held {
                values.visit_body(tcx.mir_for_ctfe(def));
                for promoted in tcx.promoted_mir(def).iter() {
                    values.visit_body(promoted);
                }
            }
        }
    }
    // The path on `root`: as written, or, when it begins with the type's own
    // name (`App.level`, as every note prints it), the rest of it on that
    // type alone. Two consumer types can have a field of one spelling.
    let on_root = |typing_env: ty::TypingEnv<'tcx>, root: Ty<'tcx>| {
        resolve_place(tcx, typing_env, root, &segments).or_else(|| {
            // (With as much of its module path as tells it apart:
            // `ui::App.level`.)
            let named = match *root.kind() {
                ty::Adt(adt, _) => names_path(&item_path(tcx, adt.did()), segments[0]),
                _ => false,
            };
            (named && segments.len() > 1)
                .then(|| resolve_place(tcx, typing_env, root, &segments[1..]))
                .flatten()
        })
    };
    // The fields the path names: one per type it resolves on, with the
    // consumers that run on that type. Several can (aterm's `App` has its
    // event handler and three drain loops): the sites are the field's, and
    // each is named once.
    let mut fields: Vec<WrittenField<'a, 'tcx>> = Vec::new();
    for (def, group) in &groups {
        let def = *def;
        if segments.is_empty() {
            continue;
        }
        // What the consumer runs on: its arguments; for a closure (the one
        // `rx.iter().for_each(..)` is given inside a method), what it
        // captures.
        let inputs: Vec<Ty<'tcx>> = if tcx.is_closure_like(def.to_def_id()) {
            let mut inputs: Vec<Ty<'tcx>> =
                match *tcx.type_of(def).instantiate_identity().skip_norm_wip().kind() {
                    ty::Closure(_, args) => {
                        let closure = args.as_closure();
                        // Its own parameters (`|app: &mut App, w|`), which a
                        // call through the Fn traits passes as one tuple.
                        let mut inputs: Vec<Ty<'tcx>> = Vec::new();
                        for input in closure.sig().skip_binder().inputs() {
                            match *tcx.erase_and_anonymize_regions(*input).kind() {
                                ty::Tuple(fields) => inputs.extend(fields.iter()),
                                _ => inputs.push(tcx.erase_and_anonymize_regions(*input)),
                            }
                        }
                        inputs.extend(
                            closure
                                .upvar_tys()
                                .iter()
                                .map(|upvar| tcx.erase_and_anonymize_regions(upvar)),
                        );
                        inputs
                    }
                    _ => continue,
                };
            // It may capture only the fields it uses (`&mut self.level`),
            // none of which has the path: then it runs on what the fn it is
            // written in runs on.
            let outer = tcx.typeck_root_def_id(def.to_def_id());
            if matches!(tcx.def_kind(outer), DefKind::Fn | DefKind::AssocFn) {
                inputs.extend(erased_sig(tcx, outer, None).inputs().iter().copied());
            }
            inputs
        } else {
            erased_sig(tcx, def.to_def_id(), None).inputs().to_vec()
        };
        let captures = tcx.is_closure_like(def.to_def_id());
        let typing_env = ty::TypingEnv::post_analysis(tcx, def);
        let peeled = |root: Ty<'tcx>| receiver_pointee(tcx, root);
        // A trait's provided method runs on its implementors: `Self` there
        // is each local type that implements the trait, which names its
        // impl's generics, so its fields are read in the impl's environment.
        let implementors: Vec<(Ty<'tcx>, ty::TypingEnv<'tcx>)> = tcx
            .trait_of_assoc(def.to_def_id())
            .map(|trait_def| {
                tcx.all_impls(trait_def)
                    .filter(|owner| owner.is_local())
                    .map(|owner| {
                        let this = tcx.type_of(owner).instantiate_identity().skip_norm_wip();
                        (
                            peeled(tcx.erase_and_anonymize_regions(this)),
                            ty::TypingEnv::post_analysis(tcx, owner),
                        )
                    })
                    .collect()
            })
            .unwrap_or_default();
        // The first argument that has the path, on every type it can be:
        // one, or for a provided method each implementor that has it.
        let resolved: Vec<(usize, Ty<'tcx>, Ty<'tcx>, BoundPlace<'tcx>)> = inputs
            .iter()
            .enumerate()
            .map(|(index, &input)| {
                let root = peeled(input);
                let roots = match root.kind() {
                    ty::Param(param) if param.name == rustc_span::symbol::kw::SelfUpper => {
                        implementors.clone()
                    }
                    _ => vec![(root, typing_env)],
                };
                roots
                    .into_iter()
                    .filter_map(|(root, typing_env)| {
                        let bound = on_root(typing_env, root)?;
                        Some((index, input, root, bound))
                    })
                    .collect::<Vec<_>>()
            })
            .find(|found| !found.is_empty())
            .unwrap_or_default();
        // A consumer that takes no argument with the path may run on a
        // local of its own (`main` with `let mut app`, the loop inline): the
        // first variable of its body that has the path.
        let mut resolved = resolved;
        let mut local_owner = None;
        // (For a closure, a variable of the fn it is written in: the `app`
        // of `main`, of which it captures the fields it uses.)
        let holder = if captures {
            tcx.typeck_root_def_id(def.to_def_id())
                .as_local()
                .filter(|outer| runnable.contains(outer))
        } else {
            Some(def)
        };
        if let (true, Some(holder)) = (resolved.is_empty(), holder) {
            hooks.with_local_body(holder, &mut |body| {
                // (The variables are read off the debug info: a local's own
                // record of being one is not kept in every MIR phase.)
                let variables: Vec<mir::Local> = body
                    .var_debug_info
                    .iter()
                    .filter_map(|info| match info.value {
                        mir::VarDebugInfoContents::Place(place) => place.as_local(),
                        mir::VarDebugInfoContents::Const(_) => None,
                    })
                    .collect();
                for local in variables {
                    if local.as_usize() <= body.arg_count || !resolved.is_empty() {
                        continue;
                    }
                    let ty = tcx.erase_and_anonymize_regions(body.local_decls[local].ty);
                    let root = peeled(ty);
                    if let Some(bound) = on_root(typing_env, root) {
                        resolved.push((usize::MAX, ty, root, bound));
                        local_owner = (ty == root && !captures).then_some(local);
                    }
                }
            });
        }
        if resolved.is_empty() {
            continue;
        }
        // Where the consumer calls or drops, each with the fn that runs
        // there when it is known (the impl's, for a trait method).
        let mut blocks_at: FxHashMap<Span, Vec<(mir::BasicBlock, Option<DefId>)>> =
            FxHashMap::default();
        let mut unwind_at: FxHashMap<Span, Vec<(mir::BasicBlock, Option<DefId>)>> =
            FxHashMap::default();
        hooks.with_local_body(def, &mut |body| {
            for (block, data) in body.basic_blocks.iter_enumerated() {
                let Some(terminator) = &data.terminator else { continue };
                let callee = match &terminator.kind {
                    TerminatorKind::Call { func, .. } | TerminatorKind::TailCall { func, .. } => {
                        func.const_fn_def().map(|(callee, callee_args)| {
                            run_by_call(tcx, body, callee, callee_args).unwrap_or(callee)
                        })
                    }
                    TerminatorKind::Drop { .. } => None,
                    _ => continue,
                };
                // On the normal path; a call or drop that exists only on
                // an unwind path is kept apart, for when a span has no other.
                let at = if data.is_cleanup { &mut unwind_at } else { &mut blocks_at };
                at.entry(terminator.source_info.span).or_default().push((block, callee));
            }
        });
        for (span, calls) in unwind_at {
            blocks_at.entry(span).or_insert(calls);
        }
        for (index, input, root, bound) in resolved {
            let target = Target {
                def,
                group: group.clone(),
                name: tcx.def_path_str(def),
                // (A capture is a field of the closure's environment, never
                // the argument local itself.)
                owner: if index == usize::MAX {
                    local_owner
                } else {
                    (input == root && !captures).then_some(mir::Local::from_usize(index + 1))
                },
                blocks_at: blocks_at.clone(),
                nodes: bodies.get(&def.to_def_id()).cloned().unwrap_or_default(),
                returns_next: index != usize::MAX && input == root && !captures && {
                    // (The next value itself, or one inside what is handed
                    // back: an `Option<Self>`, a `(Self, Output)`.)
                    let output = erased_sig(tcx, def.to_def_id(), None).output();
                    receiver_pointee(tcx, output) == root || bound.holds(tcx, output)
                },
            };
            // (Whether this consumer takes the value by `&`: `&self`, an
            // `Rc<Self>` or an `Arc<Self>`, a closure that captures it so.)
            let by_ref = index != usize::MAX
                && match *input.kind() {
                    ty::Ref(_, _, ty::Mutability::Not) => true,
                    ty::Adt(adt, _) => {
                        tcx.is_diagnostic_item(sym::Rc, adt.did())
                            || tcx.is_diagnostic_item(sym::Arc, adt.did())
                    }
                    _ => false,
                };
            let field = match fields.iter().position(|field| field.root == root) {
                Some(at) => {
                    fields[at].targets.push(target);
                    &fields[at]
                }
                None => {
                    fields.push(WrittenField {
                        root,
                        bound,
                        targets: vec![target],
                        sites: Vec::new(),
                    });
                    &fields[fields.len() - 1]
                }
            };
            if by_ref {
                field.bound.shared.set(true);
            }
        }
    }
    for index in 0..fields.len() {
        let found = {
            let field = &fields[index];
            let (bound, targets) = (&field.bound, &field.targets);
            // Every site that may write the place.
            let mut writes: Vec<Write<'tcx>> = Vec::new();
            let mut lends: Lends<'tcx> = FxHashMap::default();
            // The instances each body is read at.
            let mut read_at: FxHashMap<LocalDefId, Vec<Option<GenericArgs<'tcx>>>> =
                FxHashMap::default();
            // The consumer's own by-value argument, in a body that is one.
            let owner_of = |body_def: LocalDefId| {
                targets.iter().find(|target| target.def == body_def).and_then(|target| target.owner)
            };
            // A consumer of the field runs in a body: it is one, or a
            // closure one is written inside.
            let consumes = |body_def: LocalDefId| {
                targets.iter().any(|target| {
                    let mut def = target.def;
                    loop {
                        if def == body_def {
                            return true;
                        }
                        if !tcx.is_closure_like(def.to_def_id()) {
                            return false;
                        }
                        def = tcx.local_parent(def);
                    }
                })
            };
            let scan = writer_origins::Scan {
                tcx,
                hooks,
                bound,
                runnable: &runnable,
                foreign_inputs: &foreign_inputs,
                owner_of: &owner_of,
                consumes: &consumes,
                consumer: &|def: DefId| targets.iter().any(|target| target.def.to_def_id() == def),
                walks: Default::default(),
            };
            // Each body's solution, kept for the closures written in it.
            let mut solutions: writer_origins::Solutions<'tcx> = FxHashMap::default();
            for &body_def in &defs {
                // A generic body is read at each instance the program makes
                // of it: its types are the instance's there (`*slot =
                // T::default()` writes a whole `Config` where `T` is `Config`
                // and nothing of the field where it is `String`), and a call
                // through its parameter runs the body that instance names. One
                // the program makes no instance of is read as written.
                let mut instances: Vec<Option<GenericArgs<'tcx>>> = Vec::new();
                for node in bodies.get(&body_def.to_def_id()).map_or(&[][..], Vec::as_slice) {
                    let Some(args) = instance_args(render, *node) else { continue };
                    if !instances.contains(&Some(args)) {
                        instances.push(Some(args));
                    }
                }
                if instances.is_empty() {
                    instances.push(None);
                }
                hooks.with_local_body(body_def, &mut |body| {
                    for &subst in &instances {
                        writer_origins::scan_writes(
                            &scan,
                            body,
                            body_def,
                            subst,
                            &mut solutions,
                            &mut lends,
                            &mut writes,
                        );
                    }
                });
                read_at.insert(body_def, instances);
            }
            let none = |target: &Target<'_, 'tcx>| -> Reach {
                let arms = target
                    .group
                    .iter()
                    .map(|consumer| VariantSet::none(consumer.names.len()))
                    .collect();
                (arms, false)
            };
            // The message types the field's consumers dispatch on, one bit
            // each (a type past the 64th is never "decided").
            let mut kinds: Vec<Ty<'tcx>> = Vec::new();
            for consumer in targets.iter().flat_map(|target| target.group.iter()) {
                if !kinds.contains(&consumer.message) {
                    kinds.push(consumer.message);
                }
            }
            let kind = |consumer: &Consumer<'tcx>| match kinds
                .iter()
                .position(|kind| *kind == consumer.message)
            {
                Some(index) if index < 64 => 1u64 << index,
                _ => 0,
            };
            // A block's part in a site's reach: the arms of each message
            // whose switch narrowed it, or, when none did, outside the arms.
            // A block the dataflow did not reach is outside them too: the
            // site is in the consumer all the same. `decided`: the messages
            // a dispatch nearer the site already narrowed. The innermost
            // dispatch on a message decides its arm across calls as it does
            // within a body: an arm that hands the consumer ANOTHER message
            // of the type (a replay loop that calls the handler again) is
            // not the arm that writes. Answers the messages narrowed here.
            let add = |target: &Target<'_, 'tcx>,
                       block: mir::BasicBlock,
                       decided: u64,
                       reach: &mut Reach| {
                let mut narrowed = 0u64;
                let (mut open, mut any) = (false, false);
                for (consumer, arms) in target.group.iter().zip(reach.0.iter_mut()) {
                    let bit = kind(consumer);
                    if decided & bit != 0 {
                        continue;
                    }
                    open = true;
                    let Some(live) = consumer.live.get(block.as_usize()) else { continue };
                    // (A message with one variant has one arm, which is all
                    // of them.)
                    let total = consumer.names.len();
                    let in_arm =
                        |set: &VariantSet| set.count() > 0 && (set.count() < total || total == 1);
                    // The body's answer, and each message's own: with two
                    // messages in hand a block after an inner switch over one
                    // is still in the other's arm. The set a binding allows
                    // is taken first (the block is in THAT arm), else the
                    // narrowest.
                    let mut chosen: Option<&VariantSet> = None;
                    let own = consumer.by_root.iter().filter_map(|per| per.get(block.as_usize()));
                    for set in std::iter::once(live).chain(own).filter(|set| in_arm(set)) {
                        let better = match chosen {
                            None => true,
                            Some(known) => {
                                let (new, old) = (prefer(consumer, set), prefer(consumer, known));
                                (new && !old) || (new == old && set.count() < known.count())
                            }
                        };
                        if better {
                            chosen = Some(set);
                        }
                    }
                    if let Some(set) = chosen {
                        arms.union(set);
                        narrowed |= bit;
                        any = true;
                    }
                }
                if open && !any {
                    reach.1 = true;
                }
                narrowed
            };
            // One site per source write: drop elaboration repeats an assignment on
            // its unwind path, and a repeated note is one site. A site is
            // attributed by its blocks on the normal path, and by its unwind
            // blocks only when it has no other.
            // (The instances a site was found at are kept: it is reached
            // through those nodes only.)
            type Found<'tcx> = (Write<'tcx>, Vec<mir::BasicBlock>, Vec<Option<GenericArgs<'tcx>>>);
            let mut sites_of: Vec<Found<'tcx>> = Vec::new();
            for write in writes {
                match sites_of.iter_mut().find(|(seen, _, _)| {
                    seen.def == write.def && seen.span == write.span && seen.verb == write.verb
                }) {
                    Some((seen, blocks, at)) => {
                        if !at.contains(&write.subst) {
                            at.push(write.subst);
                        }
                        if seen.cleanup && !write.cleanup {
                            seen.cleanup = false;
                            blocks.clear();
                        }
                        if seen.cleanup == write.cleanup && !blocks.contains(&write.block) {
                            blocks.push(write.block);
                        }
                    }
                    None => {
                        let (block, at) = (write.block, write.subst);
                        sites_of.push((write, vec![block], vec![at]));
                    }
                }
            }
            let mut found: Vec<WriteSite> = Vec::new();
            for (write, blocks, found_at) in &sites_of {
                let mut reach: Vec<Reach> = targets.iter().map(none).collect();
                // A site in a consumer's own body: its blocks there. `first`:
                // the messages every one of them is in an arm of.
                let inside = targets.iter().position(|target| target.def == write.def);
                let mut first = 0u64;
                if let Some(at) = inside {
                    first = u64::MAX;
                    for &block in blocks {
                        first &= add(&targets[at], block, 0, &mut reach[at]);
                    }
                    if blocks.is_empty() {
                        first = 0;
                    }
                }
                // The resolved calls back from the write's body, to every
                // consumer that reaches it: a consumer's part is its block at
                // its call, and the walk goes on through it, since an arm of
                // another consumer may call this one. `around`: everything
                // that reaches the body without going through a consumer
                // (nothing does when the body is one).
                let mut starts: Vec<ReachNode> =
                    bodies.get(&write.def.to_def_id()).cloned().unwrap_or_default();
                // A site found at an instance is reached through that
                // instance's nodes (`Slot::<Policy>::set`, not
                // `Slot::<String>::set`); one found in the body as written,
                // through the nodes that were read no other way.
                let read = read_at.get(&write.def);
                starts.retain(|node| {
                    let at = instance_args(render, *node)
                        .filter(|args| read.is_some_and(|read| read.contains(&Some(*args))));
                    found_at.contains(&at)
                });
                let mut around: FxHashSet<ReachNode> = FxHashSet::default();
                // The nodes that reach the site through a consumer, each with
                // the messages decided on EVERY such path from it.
                let mut through: FxHashMap<ReachNode, u64> = FxHashMap::default();
                if inside.is_none() {
                    around.extend(starts.iter().copied());
                } else {
                    through.extend(starts.iter().map(|node| (*node, first)));
                }
                // Each node with whether the path from it avoids every
                // consumer, and the messages decided on the path.
                let mut queue: Vec<(ReachNode, bool, u64)> =
                    starts.into_iter().map(|node| (node, inside.is_none(), first)).collect();
                // A node is read again when a path with fewer messages
                // decided reaches it.
                let enter = |through: &mut FxHashMap<ReachNode, u64>,
                             queue: &mut Vec<(ReachNode, bool, u64)>,
                             node: ReachNode,
                             decided: u64| {
                    match through.get(&node).copied() {
                        Some(known) if known & decided == known => {}
                        Some(known) => {
                            through.insert(node, known & decided);
                            queue.push((node, false, known & decided));
                        }
                        None => {
                            through.insert(node, decided);
                            queue.push((node, false, decided));
                        }
                    }
                };
                while let Some((node, clean, decided)) = queue.pop() {
                    for edge in callers_of.get(&node).map_or(&[][..], Vec::as_slice) {
                        if is_seed(edge.from) {
                            continue;
                        }
                        if let Some(at) =
                            targets.iter().position(|target| target.nodes.contains(&edge.from))
                        {
                            let ReachSite::Mir(site) = edge.site else { continue };
                            let Some(&(_, span)) = sites.get(site as usize) else { continue };
                            // The call the edge stands for: a macro can put calls
                            // of several fns at one span.
                            let to = match render.key(edge.to) {
                                Some(Key::Body { def, .. }) => Some(def),
                                _ => None,
                            };
                            let calls =
                                targets[at].blocks_at.get(&span).map_or(&[][..], Vec::as_slice);
                            let named = |wanted: &dyn Fn(Option<DefId>) -> bool| {
                                calls
                                    .iter()
                                    .filter(|(_, callee)| wanted(*callee))
                                    .map(|(block, _)| *block)
                                    .collect::<Vec<_>>()
                            };
                            let mut own = named(&|callee| to.is_some() && callee == to);
                            if own.is_empty() {
                                own = named(&|callee| {
                                    callee.is_none_or(|callee| tcx.trait_of_assoc(callee).is_some())
                                });
                            }
                            if own.is_empty() {
                                own = named(&|_| true);
                            }
                            // No block found for the call: the consumer
                            // reaches the site all the same, from where the
                            // census cannot say. Outside its arms, never
                            // nothing.
                            if own.is_empty() {
                                reach[at].1 = true;
                            }
                            let mut next = if own.is_empty() { decided } else { u64::MAX };
                            for block in own {
                                next &= decided | add(&targets[at], block, decided, &mut reach[at]);
                            }
                            enter(&mut through, &mut queue, edge.from, next);
                            continue;
                        }
                        if clean {
                            if around.insert(edge.from) {
                                queue.push((edge.from, true, 0));
                            }
                        } else if !around.contains(&edge.from) {
                            enter(&mut through, &mut queue, edge.from, decided);
                        }
                    }
                }
                let mut labels: Vec<String> = Vec::new();
                // A body on the way to the site, below the consumers, that
                // an indirect call or a hand-off may run: the census cannot
                // say what makes that call, so the site is reached from
                // elsewhere too. (A consumer is itself handed over, to the
                // run loop that calls it: that is its message, not this.)
                // (`around` is what reaches the site with no consumer on the
                // way; a thread's own entry is named as that thread.)
                // So is a body on such a way that no resolved call reaches
                // and no thread starts at: a callback only foreign code
                // calls, the job of a thread the census cannot name.
                let started =
                    |node: &ReachNode| threads.iter().any(|thread| thread.starts.contains(node));
                let uncalled = |node: &ReachNode| {
                    callers_of
                        .get(node)
                        .is_none_or(|edges| edges.iter().all(|edge| is_seed(edge.from)))
                };
                // In a test build the harness runs each `#[test]` fn through
                // a table of fn pointers: that actor is known.
                let tested = |node: &ReachNode| testing && test_entry(*node);
                let unattributed = |node: &&ReachNode| {
                    !targets.iter().any(|target| target.nodes.contains(*node))
                        && !started(node)
                        && !tested(node)
                };
                if around.iter().filter(unattributed).any(|node| indirect.contains(node)) {
                    labels.push(
                        "an indirect call or a hand-off (a fn pointer, a `dyn` call, a callback \
                         or a thread's job the census could not name: it cannot say which arm \
                         that is)"
                            .to_owned(),
                    );
                } else if around.iter().filter(unattributed).any(|node| uncalled(node)) {
                    labels.push(
                        "a body no resolved call reaches (code nothing calls, or that only \
                         code outside the crate calls)"
                            .to_owned(),
                    );
                }
                let by_tests = around.iter().any(|node| tested(node));
                for thread in threads {
                    // A thread reaches the write through a consumer (its
                    // arms) or around every one: only the second is another
                    // route.
                    if !thread.starts.iter().any(|start| around.contains(start)) {
                        continue;
                    }
                    let runs: Vec<&Target<'_, 'tcx>> = targets
                        .iter()
                        .filter(|target| runs_consumer(thread, threads, &target.nodes))
                        .collect();
                    labels.push(match runs.as_slice() {
                        [] if thread.is_main || thread.starts.len() != 1 => thread.named.clone(),
                        [] => format!("the thread {}", thread.named),
                        [one] => format!(
                            "{}, the consumer's own thread, outside `{}`",
                            thread.named, one.name
                        ),
                        _ => format!("{}, the consumers' own thread, outside them", thread.named),
                    });
                }
                // Only the test harness reaches it: no consumer, no thread,
                // nothing unattributed.
                let test_only = by_tests
                    && labels.is_empty()
                    && reach.iter().all(|(arms, outside)| {
                        !outside && arms.iter().all(|arms| arms.count() == 0)
                    });
                found.push(WriteSite {
                    def: write.def,
                    span: write.span,
                    verb: write.verb.clone(),
                    reach,
                    threads: labels,
                    test_only,
                });
            }
            found
        };
        fields[index].sites = found;
    }
    fields
}

/// The writer census (`-Ztrust-writer-census=<field path>`, design 2026-09-29
/// §3c.2's writers and arms). The path names a field of a message consumer's
/// argument: its `self` (`config.harness` on `App::user_event`'s `App`),
/// behind references and the pointers a receiver can be (`Pin<&mut Self>`,
/// `Box<Self>`, `Rc<Self>`), or the first other argument that has it. Each
/// local site that may write it gets one note naming what reaches the site
/// over resolved calls and drops. A site is a write that may overlap the field
/// ([`overlap`]), a `&mut` taken of the field or part of it (whatever it is
/// handed to: what is then written through it is not a second site), a `&`
/// of it when it has interior mutability, or a `&mut` of a value holding it
/// lent to code that can write a whole value through it where no type
/// matches the write: the sysroot's (`mem::replace`), or a fn whose parameter
/// there is generic and whose body writes through it ([`writes_through`]:
/// `fn reset<T: Default>(slot: &mut T)`). What reaches a site is a consumer
/// for some of its messages' variants (the variants the held message can be
/// at the site or at the consumer's call toward it, [`Dispatch::live`]),
/// another thread, or a consumer's own thread outside the consumers. Several
/// consumers can run on one type (an event handler and its drain loops): the
/// sites are the field's, named once with every consumer that reaches them,
/// and each consumer gets a summary. A protocol with one writer shows one
/// arm.
///
/// Not counted, and said in the docs: a write that code in another crate
/// makes itself through a `&mut` of a value holding the field when the census
/// has no body for it, and a field reached through a generic `self` or a
/// pointer the path does not name.
fn report_writers<'tcx>(
    render: &Render<'_, 'tcx>,
    hooks: &dyn CensusHooks<'tcx>,
    sites: &[(Option<LocalDefId>, Span)],
    threads: &[Thread],
    consumers: &[Consumer<'tcx>],
    unexamined: usize,
    refused: usize,
    path: &str,
) {
    let tcx = render.tcx;
    let fields = written_fields(render, hooks, sites, threads, consumers, path, &|_, _| false);
    if fields.is_empty() {
        let mut text = format!(
            "writer census: no message consumer has an argument with the field path `{path}`"
        );
        if unexamined > 0 {
            text.push_str(&format!(
                ". {unexamined} async body(ies) that take a message are not examined as consumers"
            ));
        }
        tcx.dcx().struct_note(text).emit();
    }
    for WrittenField { root, bound, targets, sites } in &fields {
        let mut written: Vec<Reach> = targets
            .iter()
            .map(|target| {
                let arms = target
                    .group
                    .iter()
                    .map(|consumer| VariantSet::none(consumer.names.len()))
                    .collect();
                (arms, false)
            })
            .collect();
        let mut written_threads: Vec<String> = Vec::new();
        let mut unreached = 0;
        for site in sites {
            let mut from: Vec<String> = Vec::new();
            for ((target, reach), written) in
                targets.iter().zip(&site.reach).zip(written.iter_mut())
            {
                from.extend(reach_labels(target, reach));
                for (written, arms) in written.0.iter_mut().zip(&reach.0) {
                    written.union(arms);
                }
                written.1 |= reach.1;
            }
            for label in &site.threads {
                if !written_threads.contains(label) {
                    written_threads.push(label.clone());
                }
                from.push(label.clone());
            }
            let text = if from.is_empty() {
                unreached += 1;
                let whose = match targets.as_slice() {
                    [one] => format!("no arm of `{}`", one.name),
                    _ => "no consumer's arm".to_owned(),
                };
                format!(
                    "writer census: this {} `{}`; {whose} and no enumerated thread reaches it \
                     over the calls the census resolved",
                    site.verb, bound.label
                )
            } else {
                format!(
                    "writer census: this {} `{}`; reached from {}",
                    site.verb,
                    bound.label,
                    and_list(&from)
                )
            };
            tcx.dcx().struct_span_note(site.span, text).emit();
        }
        // A summary at each consumer: the sites, and what of it reaches them.
        for (target, written) in targets.iter().zip(&written) {
            let mut text = format!(
                "writer census: `{}` may be written at {} site(s)",
                bound.label,
                sites.len()
            );
            let written_from: Vec<String> = reach_labels(target, written)
                .into_iter()
                .chain(written_threads.iter().cloned())
                .collect();
            if !written_from.is_empty() {
                text.push_str(&format!(", from {}", and_list(&written_from)));
            }
            if unreached > 0 {
                text.push_str(&format!(
                    "; {unreached} of them no arm and no enumerated thread reaches over the \
                     calls the census resolved"
                ));
            }
            let others: Vec<String> = targets
                .iter()
                .filter(|other| other.def != target.def)
                .map(|other| format!("`{}`", other.name))
                .collect();
            if !others.is_empty() {
                text.push_str(&format!(
                    ". {} other consumer(s) run on `{root}`, each with its own summary: {}",
                    others.len(),
                    and_list(&others)
                ));
            }
            if unexamined > 0 {
                text.push_str(&format!(
                    ". {unexamined} async body(ies) that take a message are not examined as \
                     consumers: a write only they reach is their callers' here"
                ));
            }
            if refused > 0 {
                text.push_str(&format!(
                    ". The census did not follow {refused} call(s) or drop(s) at a type nested \
                     close to the recursion limit: a write they reach is not counted"
                ));
            }
            if root.has_param() {
                text.push_str(
                    ". The consumer's `self` is generic: a write of a whole value is matched by \
                     type, and one of a type still to be instantiated is not seen",
                );
            }
            if bound.interior {
                text.push_str(
                    ". The field has interior mutability: a `&` of a value holding it can write \
                     it too, and only a `&` taken of the field itself is a site here",
                );
            }
            tcx.dcx().struct_span_note(tcx.def_span(target.def), text).emit();
        }
    }
}

/// Whether `def` is a fn that `name` names: `name` is the fn's own name, or
/// `Type::method` for a method of a local type (the type of the impl the
/// method is in). A closure is its enclosing fn. Compared by item names,
/// never by a printed path, which a diagnostic session trims.
fn names_fn(tcx: TyCtxt<'_>, def: LocalDefId, name: &str) -> bool {
    let path = fn_path(tcx, def);
    let given: Vec<&str> = name.split("::").map(str::trim).filter(|s| !s.is_empty()).collect();
    !given.is_empty()
        && given.len() <= path.len()
        && path[path.len() - given.len()..].iter().map(String::as_str).eq(given.iter().copied())
}

/// Whether `given` (`ui::App`, `Wake`) names the item whose path is `path`:
/// its segments are the path's last ones.
fn names_path(path: &[String], given: &str) -> bool {
    let given: Vec<&str> = given.split("::").map(str::trim).filter(|s| !s.is_empty()).collect();
    !given.is_empty()
        && given.len() <= path.len()
        && path[path.len() - given.len()..].iter().map(String::as_str).eq(given.iter().copied())
}

/// The path of the fn `def` is in (a closure's is its fn's), as a binding
/// writes one: its modules, then the type for a method (`App`, the impl's
/// own type) or the trait for a provided one, then its name. `crate` first.
fn fn_path(tcx: TyCtxt<'_>, def: LocalDefId) -> Vec<String> {
    item_path(tcx, tcx.typeck_root_def_id(def.to_def_id()))
}

/// [`fn_path`] for any item of the crate graph (a type, a fn).
fn item_path(tcx: TyCtxt<'_>, def: DefId) -> Vec<String> {
    let mut path: Vec<String> = Vec::new();
    let mut current = Some(def);
    while let Some(at) = current {
        if at.is_crate_root() {
            break;
        }
        match tcx.def_kind(at) {
            DefKind::Impl { .. } => {
                if let ty::Adt(adt, _) =
                    *tcx.type_of(at).instantiate_identity().skip_norm_wip().kind()
                {
                    path.push(tcx.item_name(adt.did()).to_string());
                }
            }
            _ => path.extend(tcx.opt_item_name(at).map(|name| name.to_string())),
        }
        current = tcx.opt_parent(at);
    }
    path.push("crate".to_owned());
    path.reverse();
    path
}

/// A declared binding against the code (design 2026-09-29 §3c.2, the
/// writers check). `binding` says its field is written only from the arms for
/// its `writers`, except by its `carried_by` fns. Every site the writer census
/// finds for the field ([`written_fields`]) is held to that: a site some other
/// arm reaches, one a consumer reaches outside its arms, one another thread
/// reaches, and one nothing resolved reaches are each a mismatch, and the
/// build fails at the declaration with the sites as notes. So does a path no
/// consumer has, and a writer that names no variant of a message the field's
/// consumers dispatch on: a typo is an error, not a binding that holds
/// vacuously.
///
/// The check is as strong as the census: a write the census does not count
/// (its documented limits: another crate's plain fn, an async consumer, a
/// generic `self`'s uninstantiated writes) is not seen here either, and the
/// `carried_by` fns are the author's claim, not a checked fact.
fn check_binding<'tcx>(
    render: &Render<'_, 'tcx>,
    hooks: &dyn CensusHooks<'tcx>,
    sites: &[(Option<LocalDefId>, Span)],
    cuts: &[ReachSite],
    threads: &[Thread],
    consumers: &[Consumer<'tcx>],
    unexamined: usize,
    binding: &FieldBinding,
) {
    let tcx = render.tcx;
    let FieldBinding { name, path, writers, carried_by, span } = binding;
    // A call in this crate that the census refused for a limit of its own:
    // what it runs is not in the graph, and may write the field.
    // (One in a dependency's generic code or in drop glue has no place in
    // this crate's source, and counts as much: it can call back into the
    // crate.)
    let mut refused: Vec<Span> = cuts
        .iter()
        .filter_map(|site| match site {
            ReachSite::Mir(id) => sites.get(*id as usize),
            _ => None,
        })
        .filter_map(|&(owner, at)| owner.map(|_| at))
        .collect();
    refused.sort_unstable_by_key(|at| (at.lo(), at.hi()));
    refused.dedup();
    if !cuts.is_empty() {
        let mut diag = tcx.dcx().struct_span_err(
            *span,
            format!(
                "binding `{name}` cannot be checked against the code: the census did not follow \
                 {} call(s) or drop(s), so a write they reach is not known",
                cuts.len()
            ),
        );
        match refused.first() {
            Some(&first) => {
                diag.span_note(
                    first,
                    "this one is at a type nested close to the recursion limit, or is one of \
                     too many instances of one generic body",
                );
            }
            None => {
                diag.note(
                    "they are in a dependency's generic code or in drop glue, at a type nested \
                     close to the recursion limit",
                );
            }
        }
        diag.help(
            "a larger `#![recursion_limit]` moves the first limit; the second is a generic fn \
             that calls itself at ever larger types",
        );
        diag.emit();
        return;
    }
    // A writer names a variant: by its own name, or as `Enum::Variant`.
    // (Every segment given counts: `Wake::Observed`, `ui::Wake::Observed`.)
    let names_variant = |writer: &str, consumer: &Consumer<'tcx>, variant: usize| {
        let (owner, last) = match writer.rsplit_once("::") {
            Some((owner, last)) => (Some(owner), last.trim()),
            None => (None, writer.trim()),
        };
        last == consumer.names[variant]
            && owner.is_none_or(|owner| match *consumer.message.kind() {
                ty::Adt(adt, _) => names_path(&item_path(tcx, adt.did()), owner),
                _ => false,
            })
    };
    // Where a block is in an arm of more than one message, the one the
    // binding declares is the arm it is checked as.
    let declared = |consumer: &Consumer<'tcx>, set: &VariantSet| {
        set.iter()
            .all(|variant| writers.iter().any(|writer| names_variant(writer, consumer, variant)))
    };
    let fields = written_fields(render, hooks, sites, threads, consumers, path, &declared);
    if fields.is_empty() {
        let mut diag = tcx.dcx().struct_span_err(
            *span,
            format!(
                "`{name}` binds the field path `{path}`, and no message consumer has an argument \
                 with that path"
            ),
        );
        if unexamined > 0 {
            diag.note(format!(
                "{unexamined} async body(ies) that take a message are not examined as consumers"
            ));
        }
        // With no graph there is no thread and no consumer to find: the
        // binding is not checked, which must not read as a wrong path.
        if let Some(fallback) = render.census.fallback() {
            diag.note(format!(
                "the spawn census fell back in this build ({fallback:?}), so it enumerated no \
                 thread and no consumer: the binding could not be checked"
            ));
        }
        diag.help(
            "the path names a field of the type a consumer runs on (`config.harness` for \
             `App.config.harness`); `-Ztrust-send-census` lists the consumers. A handler the \
             drain loop calls through a fn pointer or a `dyn` is not found as one",
        );
        diag.emit();
        return;
    }
    // A path two consumer types both have is two fields: the binding is
    // about one.
    if fields.len() > 1 {
        let on: Vec<String> =
            fields.iter().map(|field| format!("`{}`", field.bound.label)).collect();
        tcx.dcx()
            .struct_span_err(
                *span,
                format!(
                    "`{name}` binds the field path `{path}`, which is {} fields: {}",
                    fields.len(),
                    and_list(&on)
                ),
            )
            .with_help(
                "begin the path with the type it is on, with as much of its module path as \
                 tells it apart (`App.level`, `ui::App.level`)",
            )
            .emit();
        return;
    }
    // Each carried-by name is one fn of the crate: a name that spells two
    // would let a second one through, and one that spells none is a typo.
    let bodies = runtime_bodies(tcx);
    let mut carriers: Vec<LocalDefId> = Vec::new();
    for by in carried_by {
        let mut named: Vec<LocalDefId> = bodies
            .iter()
            .copied()
            .filter(|def| tcx.typeck_root_def_id(def.to_def_id()) == def.to_def_id())
            .filter(|def| names_fn(tcx, *def, by))
            .collect();
        named.dedup();
        match named.as_slice() {
            [one] => carriers.push(*one),
            [] => {
                tcx.dcx()
                    .struct_span_err(
                        *span,
                        format!("`{name}` names `{by}` as carrying the value over, which is no fn of this crate"),
                    )
                    .with_help("a carried-by entry is a fn's name, with as much of its path as tells it apart (`App::carry_over`, `reload::App::carry_over`)")
                    .emit();
                return;
            }
            several => {
                let paths: Vec<String> = several
                    .iter()
                    .map(|def| format!("`{}`", fn_path(tcx, *def).join("::")))
                    .collect();
                tcx.dcx()
                    .struct_span_err(
                        *span,
                        format!(
                            "`{name}` names `{by}` as carrying the value over, which is {} fns: {}",
                            several.len(),
                            and_list(&paths)
                        ),
                    )
                    .with_help("write as much of the path as tells them apart")
                    .emit();
                return;
            }
        }
    }
    let carried_in = |def: LocalDefId| {
        let root = tcx.typeck_root_def_id(def.to_def_id());
        carriers.iter().any(|carrier| carrier.to_def_id() == root)
    };
    for WrittenField { bound, targets, sites, .. } in &fields {
        let label = &bound.label;
        // Per consumer and message, the variants whose arms may write.
        let allowed: Vec<Vec<VariantSet>> = targets
            .iter()
            .map(|target| {
                target
                    .group
                    .iter()
                    .map(|consumer| {
                        let mut set = VariantSet::none(consumer.names.len());
                        for variant in 0..consumer.names.len() {
                            if writers.iter().any(|writer| names_variant(writer, consumer, variant))
                            {
                                set.insert(variant);
                            }
                        }
                        set
                    })
                    .collect()
            })
            .collect();
        let unknown: Vec<String> = writers
            .iter()
            .filter(|writer| {
                !targets.iter().any(|target| {
                    target.group.iter().any(|consumer| {
                        (0..consumer.names.len())
                            .any(|variant| names_variant(writer, consumer, variant))
                    })
                })
            })
            .map(|writer| format!("`{writer}`"))
            .collect();
        // A bare name that is a variant of two of the field's messages
        // would allow the arm of the one the author did not mean.
        let twice: Vec<String> = writers
            .iter()
            .filter_map(|writer| {
                let mut of: Vec<String> = targets
                    .iter()
                    .flat_map(|target| target.group.iter())
                    .filter(|consumer| {
                        (0..consumer.names.len())
                            .any(|variant| names_variant(writer, consumer, variant))
                    })
                    .map(|consumer| format!("`{}`", consumer.message))
                    .collect();
                of.sort();
                of.dedup();
                (of.len() > 1).then(|| format!("`{writer}` ({})", and_list(&of)))
            })
            .collect();
        if !twice.is_empty() {
            tcx.dcx()
                .struct_span_err(
                    *span,
                    format!(
                        "`{name}` names {} as a writer of `{label}`, a variant of more than one \
                         message its consumers dispatch on",
                        and_list(&twice)
                    ),
                )
                .with_help("name the enum too: `Enum::Variant`")
                .emit();
            continue;
        }
        // A consumer that takes its value by value and returns the next one
        // builds a new value: the census does not follow a field into it.
        let functional: Vec<String> = targets
            .iter()
            .filter(|target| target.returns_next)
            .map(|target| format!("`{}`", target.name))
            .collect();
        if !functional.is_empty() {
            tcx.dcx()
                .struct_span_err(
                    *span,
                    format!(
                        "`{name}` binds `{label}`, and {} takes the value it runs on by value \
                         and returns the next one: a field set while that value is built is not \
                         a write the census finds, so the binding cannot be checked",
                        and_list(&functional)
                    ),
                )
                .with_help("a consumer that takes `&mut self` is checked")
                .emit();
            continue;
        }
        // A consumer two threads run is two writers, whatever its arms.
        let mut shared: Vec<String> = Vec::new();
        for target in targets {
            let runners: Vec<String> = threads
                .iter()
                .filter(|thread| target.nodes.iter().any(|node| thread.exact.contains(node)))
                .map(|thread| thread.named.clone())
                .collect();
            if runners.len() > 1 {
                shared.push(format!("`{}` (run by {})", target.name, and_list(&runners)));
            }
        }
        if !shared.is_empty() {
            tcx.dcx()
                .struct_span_err(
                    *span,
                    format!(
                        "`{name}` binds `{label}`, and more than one thread runs its consumer: \
                         {}. A write in a declared arm is then made by each of them",
                        and_list(&shared)
                    ),
                )
                .with_help(
                    "one thread runs a consumer: the others post it a message. (A library's \
                     exported consumer can be called by its callers, which are a thread of \
                     their own here.)",
                )
                .emit();
            continue;
        }
        if !unknown.is_empty() {
            let messages: Vec<String> = targets
                .iter()
                .flat_map(|target| target.group.iter())
                .map(|consumer| format!("`{}`", consumer.message))
                .collect::<BTreeSet<String>>()
                .into_iter()
                .collect();
            tcx.dcx()
                .struct_span_err(
                    *span,
                    format!(
                        "`{name}` names {} as a writer of `{label}`, which is no variant of {}",
                        and_list(&unknown),
                        and_list(&messages)
                    ),
                )
                .with_help(
                    "a writer is a variant of a message the field's consumers dispatch on, by \
                     its name or as `Enum::Variant`",
                )
                .emit();
            continue;
        }
        // Each site, with what reaches it that the binding does not allow;
        // and the declared arms some site is reached from.
        let mut others: Vec<(Span, String)> = Vec::new();
        let mut carried = 0;
        let mut writing: Vec<Vec<VariantSet>> = allowed
            .iter()
            .map(|sets| sets.iter().map(|set| VariantSet::none(set.len)).collect())
            .collect();
        // In a test build, what only the harness reaches is test code.
        let mut tests = 0;
        for site in sites {
            if carried_in(site.def) {
                carried += 1;
                continue;
            }
            if site.test_only {
                tests += 1;
                continue;
            }
            let mut from: Vec<String> = Vec::new();
            let mut reached = !site.threads.is_empty();
            for (((target, (arms, outside)), allowed), writing) in
                targets.iter().zip(&site.reach).zip(&allowed).zip(writing.iter_mut())
            {
                reached |= *outside || arms.iter().any(|arms| arms.count() > 0);
                for (writing, arms) in writing.iter_mut().zip(arms) {
                    writing.union(arms);
                }
                let extra: Vec<VariantSet> = arms
                    .iter()
                    .zip(allowed)
                    .map(|(arms, allowed)| {
                        let mut extra = VariantSet::none(arms.len);
                        for variant in arms.iter().filter(|variant| !allowed.contains(*variant)) {
                            extra.insert(variant);
                        }
                        extra
                    })
                    .collect();
                from.extend(reach_labels(target, &(extra, *outside)));
            }
            from.extend(site.threads.iter().cloned());
            if !reached {
                from.push(
                    "nothing the census resolved (it cannot say which arm writes here)".to_owned(),
                );
            }
            if !from.is_empty() {
                others.push((
                    site.span,
                    format!("this {} `{label}`; reached from {}", site.verb, and_list(&from)),
                ));
            }
        }
        let arms: Vec<String> = writers.iter().map(|writer| format!("`{writer}`")).collect();
        let only = if arms.is_empty() {
            "to no arm".to_owned()
        } else {
            format!("to the arm(s) for {}", and_list(&arms))
        };
        let holds = if arms.is_empty() {
            format!("no arm writes `{label}`")
        } else {
            format!("`{label}` is written only from the arm(s) for {}", and_list(&arms))
        };
        let checked = sites.len() - carried - tests;
        if others.is_empty() {
            // It holds. Say so, with what was checked; and say when it holds
            // for want of a write, which is more likely a wrong path or a
            // write the census does not see than a field nobody writes.
            let idle: Vec<String> = writers
                .iter()
                .filter(|writer| {
                    !targets.iter().zip(&writing).any(|(target, writing)| {
                        target.group.iter().zip(writing).any(|(consumer, writing)| {
                            writing.iter().any(|variant| names_variant(writer, consumer, variant))
                        })
                    })
                })
                .map(|writer| format!("`{writer}`"))
                .collect();
            let mut text =
                format!("binding `{name}` holds: {holds}; {checked} write site(s) checked");
            if carried > 0 {
                let fns: Vec<String> =
                    carriers.iter().map(|def| format!("`{}`", tcx.def_path_str(*def))).collect();
                text.push_str(&format!(
                    ", and {carried} more in the fn(s) it says carry the value over ({})",
                    and_list(&fns)
                ));
            }
            if tests > 0 {
                text.push_str(&format!(
                    "; {tests} more that only test code reaches are not counted"
                ));
            }
            if bound.root.has_non_region_param() {
                text.push_str(
                    ". The consumer's `self` is generic: a write of a whole value is matched \
                     by type, and one of a type still to be instantiated is not seen",
                );
            }
            // An async consumer's arms are not told apart: a write there is a
            // site reached from outside every arm, so it fails the binding
            // and never passes it. Say that it was not read as a consumer.
            if unexamined > 0 {
                text.push_str(&format!(
                    " ({unexamined} async body(ies) that take a message are not examined as \
                     consumers: a write in one is attributed to what drives it, not to its own \
                     arms)"
                ));
            }
            if checked == 0 || !idle.is_empty() {
                if !idle.is_empty() {
                    text.push_str(&format!(
                        ". No write of the field is reached from the arm(s) for {} over the \
                         calls the census resolved",
                        and_list(&idle)
                    ));
                }
                tcx.dcx()
                    .struct_span_warn(*span, text)
                    .with_note(
                        "the binding holds for want of a write there: check the path and the \
                         arms, and that the write is not one the census cannot see (another \
                         crate's plain fn, an async consumer, an indirect call)",
                    )
                    .emit();
            } else {
                tcx.dcx().struct_span_note(*span, text).emit();
            }
            continue;
        }
        let mut diag = tcx.dcx().struct_span_err(
            *span,
            format!(
                "`{name}` binds `{label}` {only}, and {} of its {checked} write site(s) can be \
                 reached from elsewhere",
                others.len()
            ),
        );
        for (site, text) in others {
            diag.span_note(site, text);
        }
        diag.help(
            "options: move the write into a declared arm; add the arm that writes to the \
             binding's writers (and to the model); or, for a fn that only carries the value \
             over, name it in the binding's carried-by list",
        );
        diag.emit();
    }
}

/// Whether the std fn `def` only READS what its first parameter points to,
/// though that is a cell: `Cell::get`, an atomic's `load`, `RefCell::borrow`
/// and `RwLock::read` (the guard they hand back shows the value by `&`), a
/// `OnceCell`'s `get`, and the wrappers `format_args!` makes around what it
/// prints (`Argument::new_debug`: the `fmt` impl is handed a `&`).
fn std_reader(tcx: TyCtxt<'_>, def: DefId) -> bool {
    if !matches!(tcx.def_kind(def), DefKind::AssocFn)
        || !crate::def_is_in_sysroot_resident_crate(tcx, def)
    {
        return false;
    }
    let Some(of) = tcx.impl_of_assoc(def) else { return false };
    let ty::Adt(adt, _) = *tcx.type_of(of).instantiate_identity().skip_norm_wip().kind() else {
        return false;
    };
    let (owner, method) = (tcx.item_name(adt.did()), tcx.item_name(def));
    match (owner.as_str(), method.as_str()) {
        ("Cell" | "OnceCell" | "OnceLock", "get")
        | ("RefCell", "borrow" | "try_borrow")
        | ("RwLock", "read" | "try_read") => true,
        (owner, "load") => owner.starts_with("Atomic"),
        ("Argument", method) => method.starts_with("new_"),
        _ => false,
    }
}

/// Whether the std fn `def` only hands ON what it is given: a pointer into
/// it, a guard of it, an iterator over it, the value in another wrapper. It
/// writes nothing through a pointer it is handed (an iterator's `next`
/// advances the iterator). A LIST, by name, because no signature says it:
/// `mem::take` and `Option::insert` look like accessors by their types. A
/// std fn that is not on it, handed a pointer to a value that may hold the
/// field, is a site; so a missing name refuses a true binding and never
/// passes a false one.
fn std_passes_on(tcx: TyCtxt<'_>, def: DefId) -> bool {
    if !matches!(tcx.def_kind(def), DefKind::Fn | DefKind::AssocFn)
        || !crate::def_is_in_sysroot_resident_crate(tcx, def)
    {
        return false;
    }
    let name = tcx.item_name(def);
    // (Names std gives only to accessors and wrappers.)
    if matches!(
        name.as_str(),
        "as_mut"
            | "as_ref"
            | "as_deref"
            | "as_deref_mut"
            | "as_slice"
            | "as_mut_slice"
            | "as_ptr"
            | "as_mut_ptr"
            | "as_pin_mut"
            | "unwrap"
            | "expect"
            | "unwrap_unchecked"
            | "iter"
            | "iter_mut"
            | "into_iter"
            | "next"
            | "next_back"
            | "by_ref"
            | "get_mut"
            | "get_unchecked"
            | "get_unchecked_mut"
            | "first"
            | "first_mut"
            | "last"
            | "last_mut"
            | "split_at_mut"
            | "split_first_mut"
            | "split_last_mut"
            | "index"
            | "index_mut"
            | "deref"
            | "deref_mut"
            | "borrow"
            | "borrow_mut"
            | "try_borrow"
            | "try_borrow_mut"
            | "lock"
            | "try_lock"
            | "black_box"
            | "identity"
            | "new"
            | "from"
            | "clone"
            | "branch"
            | "from_residual"
            | "from_output"
            | "into_inner"
    ) {
        return true;
    }
    // (Names that are an accessor's only on some types: `RwLock::write` is,
    // `ptr::write` and `io::Write::write` are not.)
    let owner = tcx.impl_of_assoc(def).and_then(|of| {
        match *tcx.type_of(of).instantiate_identity().skip_norm_wip().kind() {
            ty::Adt(adt, _) => Some(tcx.item_name(adt.did())),
            _ => None,
        }
    });
    let Some(owner) = owner else { return false };
    matches!(
        (owner.as_str(), name.as_str()),
        ("RwLock", "read" | "write" | "try_read" | "try_write")
            // (A thread-local's key shows what it keeps, by `&`, to the
            // closure it is given.)
            | ("LocalKey", "with" | "try_with")
            | (
                "HashMap" | "BTreeMap" | "Vec" | "VecDeque" | "Option" | "OnceCell" | "OnceLock",
                "get"
            )
    ) || (owner.as_str().starts_with("Atomic") && name.as_str() == "get_mut")
}

/// The parameters of the std fn `callee` through which nothing is written
/// and no pointer is kept: declared `*const T`, in a fn whose result can hold
/// no pointer (a scalar, `()`, or a bare type parameter: `p.read()`,
/// `p.is_null()`, `ptr::eq`). A fn that returns a pointer, or a value that
/// may hold one (`cast`, `cast_mut`, `Rc::from_raw`), hands the pointer on.
/// And the receiver of a std fn that only reads a cell ([`std_reader`]).
fn read_only_params(tcx: TyCtxt<'_>, callee: DefId) -> Vec<usize> {
    if !matches!(tcx.def_kind(callee), DefKind::Fn | DefKind::AssocFn)
        || !crate::def_is_in_sysroot_resident_crate(tcx, callee)
    {
        return Vec::new();
    }
    if std_reader(tcx, callee) {
        return vec![0];
    }
    let sig = tcx.fn_sig(callee).instantiate_identity().skip_norm_wip().skip_binder();
    let holds_no_pointer = match sig.output().kind() {
        ty::Bool
        | ty::Char
        | ty::Int(_)
        | ty::Uint(_)
        | ty::Float(_)
        | ty::Never
        | ty::Param(_) => true,
        ty::Tuple(fields) => fields.is_empty(),
        _ => false,
    };
    if !holds_no_pointer {
        return Vec::new();
    }
    sig.inputs()
        .iter()
        .enumerate()
        .filter(|(_, input)| matches!(input.kind(), ty::RawPtr(_, ty::Mutability::Not)))
        .map(|(index, _)| index)
        .collect()
}

/// The body a call runs, with its instance's arguments, when it is known
/// where the call is: the callee itself, or for a trait method the impl's (or
/// the trait's provided one) that the call resolves to. `None` when the
/// receiver's type is not known here (a type parameter's method, a `dyn`'s)
/// or what runs is no fn item.
fn run_instance_by_call<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
    callee: DefId,
    callee_args: GenericArgs<'tcx>,
) -> Option<(DefId, GenericArgs<'tcx>)> {
    if tcx.trait_of_assoc(callee).is_none() {
        return Some((callee, callee_args));
    }
    // Arguments with nothing left to instantiate resolve on their own.
    let typing_env = if callee_args.has_non_region_param() {
        body.typing_env(tcx)
    } else {
        ty::TypingEnv::fully_monomorphized()
    };
    let callee_args = tcx
        .try_normalize_erasing_regions(typing_env, ty::Unnormalized::new_wip(callee_args))
        .ok()?;
    let instance = Instance::try_resolve(tcx, typing_env, callee, callee_args).ok()??;
    match instance.def {
        InstanceKind::Item(def) => Some((def, instance.args)),
        // `f(app, w)` for a fn item or a closure `f`, through the Fn traits:
        // the shim runs the callable its first argument is.
        InstanceKind::Shim(ShimKind::FnPtr(..) | ShimKind::ClosureOnce { .. }) => {
            match *instance.args.types().next()?.kind() {
                ty::FnDef(def, args) => Some((def, args.skip_binder())),
                ty::Closure(def, args) => Some((def, args)),
                _ => None,
            }
        }
        _ => None,
    }
}

/// The body a call runs ([`run_instance_by_call`]), without its arguments.
fn run_by_call<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
    callee: DefId,
    callee_args: GenericArgs<'tcx>,
) -> Option<DefId> {
    run_instance_by_call(tcx, body, callee, callee_args).map(|(def, _)| def)
}

/// Whether the fn `def` declares its parameter number `index` with a type
/// that still has a type parameter (`slot: &mut T`, `&mut self` in a generic
/// impl or a trait's provided method): what its body writes through it has
/// the parameter's type, which matches no type of the program. A lifetime
/// parameter is not one (`&mut Config<'a>`).
fn generic_parameter(tcx: TyCtxt<'_>, def: DefId, index: usize) -> bool {
    matches!(tcx.def_kind(def), DefKind::Fn | DefKind::AssocFn)
        && tcx
            .fn_sig(def)
            .instantiate_identity()
            .skip_norm_wip()
            .skip_binder()
            .inputs()
            .get(index)
            .is_some_and(|ty| ty.has_non_region_param())
}

/// How a body was given the pointer a lend is followed through: as its
/// argument (the pointer itself, or a value built around it), or, for a
/// closure, as one of its captures.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Given {
    Arg(usize),
    Capture(usize),
}

/// Whether a body writes through what it was given, per body, instance and
/// way it was given it ([`writes_through`]).
type Lends<'tcx> = FxHashMap<(DefId, GenericArgs<'tcx>, Given), bool>;

/// Whether the fn `def` can write a whole value through the pointer it takes
/// as argument number `param`: its body assigns the pointee (`*slot = v`), or
/// hands the pointer (itself, or a `&mut` reborrow of it: a `&` cannot write)
/// on to sysroot code or to a fn that does. Read off the body the census has
/// for `def`: a local one (a trait's provided method included), or another
/// crate's generic or inlinable one. A fn with no body here answers no: a
/// required trait method whose impl is not known where it is called (a known
/// one is judged as itself, [`run_by_call`]) and another crate's plain fn.
fn writes_through<'tcx>(
    tcx: TyCtxt<'tcx>,
    hooks: &dyn CensusHooks<'tcx>,
    runnable: &FxHashSet<LocalDefId>,
    memo: &mut Lends<'tcx>,
    def: DefId,
    instance: GenericArgs<'tcx>,
    given: Given,
) -> bool {
    let mut active = FxHashSet::default();
    writes_through_from(tcx, hooks, runnable, memo, &mut active, def, instance, given).0
}

/// [`writes_through`], with the fns being read further up (`active`). The
/// second answer is whether a `no` rests on one of those: such a `no` holds
/// only for this walk and is not remembered (in `a -> b -> a`, `b` is `no`
/// only until `a` has been read).
///
/// The body is read at `instance`, the arguments it is called with: a call
/// it makes on its own type parameter (`slot.wipe()`, `f(slot)`) runs the
/// body that instance names. A local one is not judged here: the census
/// reads it on its own, where its writes are sites. A pointer the body wraps
/// is followed in what takes the wrapper: `Some(slot)` into the fn given it
/// (std's may write: `Some(slot).map(mem::take)`), a closure that captures
/// it into the closure's own body, whatever that closure is handed to (a run
/// loop given its handler calls it, and writes nothing itself).
fn writes_through_from<'tcx>(
    tcx: TyCtxt<'tcx>,
    hooks: &dyn CensusHooks<'tcx>,
    runnable: &FxHashSet<LocalDefId>,
    memo: &mut Lends<'tcx>,
    active: &mut FxHashSet<(DefId, GenericArgs<'tcx>, Given)>,
    def: DefId,
    instance: GenericArgs<'tcx>,
    given: Given,
) -> (bool, bool) {
    let key = (def, instance, given);
    if let Some(&known) = memo.get(&key) {
        return (known, false);
    }
    if !active.insert(key) {
        return (false, true);
    }
    let at = (!instance.is_empty() && !instance.has_non_region_param()).then_some(instance);
    let mut direct = false;
    let mut passed: Vec<(DefId, GenericArgs<'tcx>, Given)> = Vec::new();
    let mut read = |body: &mir::Body<'tcx>| {
        // The whole pointee, or a part of it whose type generic code has
        // still to instantiate (`slot.inner = v` in `Slot<T>::set`): a write
        // there may be a whole value of the type the caller passed.
        let whole = |place: &mir::Place<'tcx>| match place.projection.as_slice() {
            [mir::ProjectionElem::Deref] => true,
            [mir::ProjectionElem::Deref, ..] => place.ty(body, tcx).ty.has_non_region_param(),
            _ => false,
        };
        // A value built around a pointer, by its type; anything else that
        // is given is the pointer (a `T` the caller made a `&mut C`).
        let wraps = |ty: Ty<'tcx>| {
            matches!(ty.kind(), ty::Adt(..) | ty::Array(..) | ty::Closure(..)) && !ty.is_box()
        };
        let pointer = |ty: Ty<'tcx>| matches!(ty.kind(), ty::Ref(..) | ty::RawPtr(..));
        // The pointer, through moves, casts and `&mut` reborrows; and the
        // values built around it (`Some(slot)`, a tuple of arguments).
        let mut aliases: FxHashSet<mir::Local> = FxHashSet::default();
        let mut carriers: FxHashSet<mir::Local> = FxHashSet::default();
        // What a closure captured, read out of its environment.
        let env = mir::Local::from_usize(1);
        let captured = |place: &mir::Place<'tcx>| match (given, place.projection.as_slice()) {
            (
                Given::Capture(index),
                [mir::ProjectionElem::Deref, mir::ProjectionElem::Field(field, _)]
                | [mir::ProjectionElem::Field(field, _)],
            ) => place.local == env && field.as_usize() == index,
            _ => false,
        };
        if let Given::Arg(index) = given {
            if index >= body.arg_count {
                return;
            }
            let local = mir::Local::from_usize(index + 1);
            if wraps(body.local_decls[local].ty) {
                carriers.insert(local);
            } else {
                aliases.insert(local);
            }
        }
        // Closures built here around the pointer, with the capture it is.
        let mut closures: Vec<(DefId, GenericArgs<'tcx>, usize)> = Vec::new();
        loop {
            let mut grew = false;
            for data in body.basic_blocks.iter() {
                for statement in &data.statements {
                    let mir::StatementKind::Assign(assign) = &statement.kind else { continue };
                    let (target, rvalue) = &**assign;
                    if !target.projection.is_empty() {
                        continue;
                    }
                    let bare = |operand: &mir::Operand<'tcx>| {
                        operand
                            .place()
                            .filter(|place| place.projection.is_empty())
                            .map(|place| place.local)
                    };
                    let loaded = match rvalue {
                        mir::Rvalue::CopyForDeref(place)
                        | mir::Rvalue::Use(
                            mir::Operand::Copy(place) | mir::Operand::Move(place),
                            _,
                        ) => Some(place),
                        _ => None,
                    };
                    if let Some(place) = loaded {
                        // Out of the closure's environment; through a
                        // pointer to the pointer (a capture by reference);
                        // or out of a value built around it.
                        let unwrapped = !place.projection.is_empty()
                            && carriers.contains(&place.local)
                            && place.projection.iter().all(|elem| {
                                matches!(
                                    elem,
                                    mir::ProjectionElem::Field(..)
                                        | mir::ProjectionElem::Downcast(..)
                                )
                            });
                        let through =
                            matches!(place.projection.as_slice(), [mir::ProjectionElem::Deref])
                                && aliases.contains(&place.local)
                                && pointer(place.ty(body, tcx).ty);
                        if captured(place) || unwrapped || through {
                            grew |= if wraps(body.local_decls[target.local].ty) {
                                carriers.insert(target.local)
                            } else {
                                aliases.insert(target.local)
                            };
                            continue;
                        }
                    }
                    match rvalue {
                        mir::Rvalue::Use(operand, _) | mir::Rvalue::Cast(_, operand, _) => {
                            if let Some(from) = bare(operand) {
                                if aliases.contains(&from) {
                                    grew |= aliases.insert(target.local);
                                }
                                if carriers.contains(&from) {
                                    grew |= carriers.insert(target.local);
                                }
                            }
                        }
                        // A reborrow of the pointee, or a pointer to the
                        // local that holds the pointer.
                        mir::Rvalue::Ref(_, mir::BorrowKind::Mut { .. }, place)
                        | mir::Rvalue::RawPtr(_, place)
                            if (whole(place) || place.projection.is_empty())
                                && aliases.contains(&place.local) =>
                        {
                            grew |= aliases.insert(target.local);
                        }
                        mir::Rvalue::Aggregate(kind, operands) => {
                            let held = |operand: &mir::Operand<'tcx>| {
                                bare(operand).is_some_and(|local| {
                                    aliases.contains(&local) || carriers.contains(&local)
                                })
                            };
                            if !operands.iter().any(held) {
                                continue;
                            }
                            match **kind {
                                // The argument tuple of a call through the
                                // Fn traits passes the pointer as it is.
                                mir::AggregateKind::Tuple => {
                                    grew |= aliases.insert(target.local);
                                }
                                // A closure is followed into its own body,
                                // whatever it is handed to.
                                mir::AggregateKind::Closure(closure, closure_args) => {
                                    for (index, operand) in operands.iter().enumerate() {
                                        let entry = (closure, closure_args, index);
                                        if held(operand) && !closures.contains(&entry) {
                                            closures.push(entry);
                                        }
                                    }
                                }
                                _ => grew |= carriers.insert(target.local),
                            }
                        }
                        _ => {}
                    }
                }
            }
            if !grew {
                break;
            }
        }
        for (closure, closure_args, index) in closures {
            passed.push((closure, at_instance(tcx, at, closure_args), Given::Capture(index)));
        }
        for data in body.basic_blocks.iter() {
            for statement in &data.statements {
                if let mir::StatementKind::Assign(assign) = &statement.kind {
                    let (target, _) = &**assign;
                    direct |= whole(target) && aliases.contains(&target.local);
                }
            }
            let Some(mir::Terminator {
                kind: TerminatorKind::Call { func, args, destination, .. },
                ..
            }) = &data.terminator
            else {
                continue;
            };
            direct |= whole(destination) && aliases.contains(&destination.local);
            // The pointer, or a value built around it, as an argument: a
            // local, or the capture read where it is passed.
            let handed = |arg: &rustc_span::Spanned<mir::Operand<'tcx>>| {
                arg.node.place().is_some_and(|place| {
                    captured(&place)
                        || (place.projection.is_empty()
                            && (aliases.contains(&place.local) || carriers.contains(&place.local)))
                })
            };
            let Some((callee, callee_args)) = func.const_fn_def() else {
                // What a fn pointer or a `dyn` runs is not known here: a
                // wrapped pointer handed to it may be written through.
                direct |= args.iter().any(|arg| {
                    arg.node.place().is_some_and(|place| {
                        place.projection.is_empty() && carriers.contains(&place.local)
                    })
                });
                continue;
            };
            let callee_args = at_instance(tcx, at, callee_args);
            let (run, run_args) = run_instance_by_call(tcx, body, callee, callee_args)
                .unwrap_or((callee, callee_args));
            for (index, arg) in args.iter().enumerate() {
                if handed(arg) {
                    passed.push((run, run_args, Given::Arg(index)));
                }
            }
        }
    };
    match def.as_local() {
        Some(local) if runnable.contains(&local) => hooks.with_local_body(local, &mut read),
        None if tcx.is_mir_available(def) => read(tcx.optimized_mir(def)),
        _ => {}
    }
    let mut result = direct;
    let mut tainted = false;
    for (callee, callee_args, position) in passed {
        if result {
            break;
        }
        // A body of the crate is read on its own, at this instance.
        if callee.as_local().is_some_and(|callee| runnable.contains(&callee)) {
            continue;
        }
        let followed = match position {
            Given::Arg(_) => matches!(tcx.def_kind(callee), DefKind::Fn | DefKind::AssocFn),
            // Another crate's closure, where its body came with the crate.
            Given::Capture(_) => tcx.is_mir_available(callee),
        };
        if crate::def_is_in_sysroot_resident_crate(tcx, callee) {
            // As in the crate's own code: not through a parameter declared
            // `&T`, nor into a std fn that only reads (`ptr::eq(p, q)`).
            // (A `*const T` only where the fn hands no pointer back:
            // `cast_mut` returns one the dependency can write through,
            // which this walk does not follow.)
            let reads = match position {
                Given::Arg(index) => {
                    declared_shared(tcx, callee, index)
                        || read_only_params(tcx, callee).contains(&index)
                }
                Given::Capture(_) => false,
            };
            result |= !reads;
        } else if followed {
            let (writes, rests) = writes_through_from(
                tcx,
                hooks,
                runnable,
                memo,
                active,
                callee,
                callee_args,
                position,
            );
            result |= writes;
            tainted |= rests;
        } else {
            // Another crate's closure, called or with no body here: not read.
            result = true;
        }
    }
    active.remove(&key);
    if result || !tainted {
        memo.insert(key, result);
    }
    (result, tainted && !result)
}

/// Whether a value of type `ty` can hold a `message` for whoever is given
/// it: the type is the message, has it in a field (the fields of any crate's
/// types are read, at their instantiation), behind a pointer, in a tuple or
/// an array, among the type arguments of a sysroot collection (which keeps
/// its elements behind pointers that do not name them), or in what a closure
/// captures or returns. A channel's `Sender` and `SyncSender` name the
/// message and hold none. `budget` bounds the walk; a walk that runs out
/// answers yes.
fn holds_message<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>,
    message: Ty<'tcx>,
    known: &mut FxHashMap<Ty<'tcx>, bool>,
    budget: &mut usize,
) -> bool {
    let ty = tcx.erase_and_anonymize_regions(ty);
    if ty == message {
        return true;
    }
    if let Some(&found) = known.get(&ty) {
        return found;
    }
    if *budget == 0 {
        return true;
    }
    *budget -= 1;
    // A type that holds itself answers no here.
    known.insert(ty, false);
    let mut inside = |ty: Ty<'tcx>| holds_message(tcx, ty, message, known, budget);
    let found = match *ty.kind() {
        ty::Adt(adt, args) => {
            let sysroot = crate::def_is_in_sysroot_resident_crate(tcx, adt.did());
            let sender = sysroot
                && matches!(tcx.item_name(adt.did()).as_str(), "Sender" | "SyncSender")
                && (in_std_module(tcx, adt.did(), "mpsc") || in_std_module(tcx, adt.did(), "mpmc"));
            !sender
                && (adt.all_fields().any(|field| inside(field.ty(tcx, args).skip_norm_wip()))
                    || (sysroot && args.types().any(&mut inside)))
        }
        ty::Ref(_, pointee, _) | ty::RawPtr(pointee, _) => inside(pointee),
        ty::Tuple(fields) => fields.iter().any(inside),
        ty::Array(element, _) | ty::Slice(element) | ty::Pat(element, _) => inside(element),
        ty::Closure(_, args) => {
            let closure = args.as_closure();
            closure.upvar_tys().iter().any(&mut inside)
                || inside(closure.sig().skip_binder().output())
        }
        ty::FnDef(def, args) => inside(
            tcx.fn_sig(def)
                .instantiate(tcx, args.skip_binder())
                .skip_norm_wip()
                .skip_binder()
                .output(),
        ),
        ty::FnPtr(sig, _) => inside(sig.skip_binder().output()),
        // Not known here: a type parameter, an `impl Trait`, a `dyn`.
        ty::Param(_) | ty::Alias(..) | ty::Dynamic(..) | ty::Coroutine(..) => true,
        _ => false,
    };
    known.insert(ty, found);
    found
}

/// The variants of the message a thread sends at `send`, and whether the
/// trace is COMPLETE: every route by which the thread hands a value to that
/// send was followed back to a variant being constructed.
///
/// Tracing starts at each RUN edge in the thread's exact reach (`callers`, its
/// edges by callee) from a local body into code that is not local, is generic
/// over the message type, and reaches `send` through code outside the crate
/// alone (`EventLoopProxy::send_event`, `Sender::send`). A foreign call that
/// reaches the send only by calling back into the crate (`Option::map_or` with
/// a closure that posts) hands nothing on itself: the closure's own call is
/// where its value starts.
///
/// At a start the census takes every argument of the message type and follows
/// it back through moves to each variant constructed (an aggregate, or a
/// discriminant set), through a parameter to every local caller's argument at
/// each call there (a closure's or a fn item's Fn-trait call passes its
/// parameters as one tuple), and through every call of that callee that shares
/// the span (a macro's repetitions). The variants are a union over the body,
/// not a flow analysis: one overwritten before the send is still listed.
///
/// The trace is INCOMPLETE, and says so, wherever a value comes from anything
/// else: a field or another projection, a constant, a call's result, a local
/// whose address is taken mutably, a parameter with no local caller or of a
/// body outside code calls (`open`: a library's exported fns), a call the
/// census cannot find again. And wherever the outside code can get a message
/// some other way than as that argument: it is not generic over the message
/// (it makes one itself, `t.into()`), another argument's type names the
/// message (a `Vec` of them, a closure that returns one), or it calls a local
/// body that returns one (`T::default()`).
#[allow(clippy::too_many_arguments)]
fn sent_variants<'tcx>(
    render: &Render<'_, 'tcx>,
    sites: &[(Option<LocalDefId>, Span)],
    hooks: &dyn CensusHooks<'tcx>,
    callers: &FxHashMap<ReachNode, Vec<ReachEdge>>,
    run_out: &FxHashMap<ReachNode, Vec<ReachEdge>>,
    read_out: &FxHashMap<ReachNode, Vec<ReachNode>>,
    open: &FxHashSet<ReachNode>,
    send: ReachNode,
    message: Ty<'tcx>,
) -> (Vec<String>, bool) {
    let tcx = render.tcx;
    let ty::Adt(adt, _) = *message.kind() else { return (Vec::new(), true) };
    if !adt.is_enum() {
        return (Vec::new(), true);
    }
    let local_body = |node: ReachNode| match render.key(node) {
        Some(Key::Body { def, .. }) => def.as_local(),
        _ => None,
    };
    let message = tcx.erase_and_anonymize_regions(message);
    let mentions =
        |ty: Ty<'tcx>| tcx.erase_and_anonymize_regions(ty).walk().any(|arg| arg == message.into());
    let generic_over_message = |node: ReachNode| {
        let args = match render.key(node) {
            Some(Key::Body { args, .. }) => args,
            Some(Key::Shim { instance, .. }) => instance.args,
            _ => return false,
        };
        let hit = args.types().any(|ty| mentions(ty));
        hit
    };
    // What a body takes and returns, at its instance (a closure's from its
    // own signature; `None` where neither is known here).
    let signature = |node: ReachNode| match render.key(node) {
        Some(Key::Body { def, args, .. }) => match tcx.def_kind(def) {
            DefKind::Fn | DefKind::AssocFn => {
                let sig = erased_sig(tcx, def, Some(args));
                Some((sig.inputs().to_vec(), sig.output()))
            }
            _ => match *tcx.type_of(def).instantiate_identity().skip_norm_wip().kind() {
                ty::Closure(_, closure) => {
                    let sig = closure.as_closure().sig().skip_binder();
                    Some((sig.inputs().to_vec(), sig.output()))
                }
                _ => None,
            },
        },
        _ => None,
    };
    // Whether a type names the message, or is one whose contents are not
    // known here (a type parameter, an `impl Trait`).
    let may_name = |ty: Ty<'tcx>| {
        mentions(ty)
            || ty.walk().any(|arg| match arg.kind() {
                GenericArgKind::Type(part) => match part.kind() {
                    ty::Param(_) => true,
                    ty::Alias(_, alias) => {
                        matches!(alias.kind, ty::AliasTyKind::Opaque { .. })
                    }
                    _ => false,
                },
                _ => false,
            })
    };
    // Whether code outside the crate that runs `target` can get a message
    // from it: a local body that returns one (`T::default()`, a closure, a
    // method returning `impl Iterator<Item = Msg>`) or writes one through a
    // pointer it is given (`fn advance(&mut self)`), and a body outside the
    // crate that makes one from nothing (a foreign `Default`).
    let gives_message = |target: ReachNode| {
        let Some(Key::Body { def, .. }) = render.key(target) else { return false };
        let Some((inputs, output)) = signature(target) else { return def.is_local() };
        if def.is_local() {
            // Through what it returns, a pointer it can write through, or a
            // shared one to a place with interior mutability
            // (`&Cell<Option<T>>`).
            let writable = |pointee: Ty<'tcx>| {
                pointee.has_non_region_param()
                    || pointee.has_escaping_bound_vars()
                    || !pointee.is_freeze(tcx, ty::TypingEnv::fully_monomorphized())
            };
            may_name(output)
                || inputs.iter().any(|input| match *input.kind() {
                    ty::Ref(_, pointee, ty::Mutability::Mut)
                    | ty::RawPtr(pointee, ty::Mutability::Mut) => may_name(pointee),
                    ty::Ref(_, pointee, ty::Mutability::Not)
                    | ty::RawPtr(pointee, ty::Mutability::Not) => {
                        may_name(pointee) && writable(pointee)
                    }
                    _ => false,
                })
        } else {
            mentions(output)
                && !inputs.iter().any(|input| mentions(*input))
                && !in_std_module(tcx, def, "mpsc")
                && !in_std_module(tcx, def, "mpmc")
        }
    };
    // The nodes that reach `send` through code outside the crate alone.
    let mut toward: FxHashSet<ReachNode> = FxHashSet::default();
    let mut queue = VecDeque::from([send]);
    toward.insert(send);
    while let Some(node) = queue.pop_front() {
        for edge in callers.get(&node).map_or(&[][..], Vec::as_slice) {
            if local_body(edge.from).is_none() && toward.insert(edge.from) {
                queue.push_back(edge.from);
            }
        }
    }
    // A position is the callee's parameter, by number (a closure's
    // environment not counted). `None`: every argument of the message type.
    type Position = Option<usize>;
    let mut variants: BTreeSet<String> = BTreeSet::new();
    let mut complete = true;
    // Calls from local code into the send's machinery: where tracing starts.
    let mut work: Vec<(ReachEdge, Position)> = Vec::new();
    for &node in &toward {
        let hands_on = generic_over_message(node);
        let into = callers.get(&node).map_or(&[][..], Vec::as_slice);
        // Code outside the crate that nothing in the thread's reach calls is
        // where the thread starts (a dependency's own closure): what it
        // sends came with the spawn, or is made there.
        if node != send && into.is_empty() {
            complete = false;
        }
        for edge in into {
            if local_body(edge.from).is_none() {
                continue;
            }
            if hands_on {
                work.push((*edge, None));
            } else {
                // It is given no message: it makes the one it sends.
                complete = false;
            }
        }
        if node == send {
            continue;
        }
        // A message the outside code gets some other way than as that
        // argument: from a body it calls (directly, or through a closure's
        // shim), or from a constant of the crate's it reads.
        // Asked of every body the outside code runs on the way, a few
        // calls deep: `mem::take` is no maker, the `Default` it calls is.
        let mut asked: FxHashSet<ReachNode> = FxHashSet::default();
        let mut frontier: Vec<(ReachNode, usize)> = vec![(node, 0)];
        while let Some((at, depth)) = frontier.pop() {
            for edge in run_out.get(&at).map_or(&[][..], Vec::as_slice) {
                let target = edge.to;
                if toward.contains(&target) || !asked.insert(target) {
                    continue;
                }
                if gives_message(target) {
                    complete = false;
                }
                // Through a shim, and on through code outside the crate.
                let outside_code = local_body(target).is_none();
                if outside_code && depth < 3 && asked.len() < 4096 {
                    frontier.push((target, depth + 1));
                }
            }
        }
        for &value in read_out.get(&node).map_or(&[][..], Vec::as_slice) {
            if let Some(Key::Value { def, .. }) = render.key(value) {
                if def.is_local()
                    && may_name(tcx.type_of(def).instantiate_identity().skip_norm_wip())
                {
                    complete = false;
                }
            }
        }
    }
    // Each (caller, callee, span) once per argument position: every call of
    // the callee at the span is read in one pass, so a macro that repeats a
    // send a thousand times at one span is one pass, not a thousand.
    let mut done: FxHashSet<(ReachNode, ReachNode, Span, Position)> = FxHashSet::default();
    // A closure or fn item called through the Fn traits is reached from a
    // shim, or from a forwarding impl in core (`impl FnMut for &mut F`), that
    // passes `(self, args)` on unchanged: the tracer steps through to its
    // callers.
    let forwards = |node: ReachNode| match render.key(node) {
        Some(Key::Shim { .. }) => true,
        Some(Key::Body { def, .. }) => {
            !def.is_local()
                && tcx
                    .trait_of_assoc(def)
                    .or_else(|| {
                        tcx.impl_of_assoc(def).and_then(|owner| tcx.impl_opt_trait_id(owner))
                    })
                    .is_some_and(|trait_def| tcx.fn_trait_kind_from_def_id(trait_def).is_some())
        }
        _ => false,
    };
    // Whether a value of an argument's type can hold a message for the
    // outside code to send: by its fields, to any depth, except that a
    // channel's sender names the message and holds none. A `Receiver`, a
    // `Vec`, a closure that returns one and a receiver object that buffers
    // them all do.
    let holding: std::cell::RefCell<FxHashMap<Ty<'tcx>, bool>> = Default::default();
    let holds = |ty: Ty<'tcx>| {
        let mut budget = 2_000;
        holds_message(tcx, ty, message, &mut holding.borrow_mut(), &mut budget)
    };
    while let Some((edge, position)) = work.pop() {
        let (Some(def), ReachSite::Mir(site)) = (local_body(edge.from), edge.site) else {
            complete = false;
            continue;
        };
        let Some(&(_, span)) = sites.get(site as usize) else {
            complete = false;
            continue;
        };
        if !done.insert((edge.from, edge.to, span, position)) {
            continue;
        }
        let (generic, generic_env) = match render.key(edge.from) {
            Some(Key::Body { args, env, .. }) => (Some(args), env),
            _ => (None, None),
        };
        let target = render.key(edge.to);
        let closure = tcx.is_closure_like(def.to_def_id());
        // The parameters (as locals) the value came in through.
        let mut through: BTreeSet<usize> = BTreeSet::new();
        hooks.with_local_body(def, &mut |body| {
            // A generic frame's MIR names its parameters: instantiate.
            let instantiated = |ty: Ty<'tcx>| {
                let ty = match generic {
                    Some(generic) if !generic.is_empty() => {
                        ty::EarlyBinder::bind(tcx, ty).instantiate(tcx, generic).skip_norm_wip()
                    }
                    _ => ty,
                };
                tcx.erase_and_anonymize_regions(ty)
            };
            // Whether a call at the span is the edge's own. Another call of
            // the same expression (the receiver's `Deref::deref`, a macro
            // that repeats the expression over another callee) is not.
            let is_edge_call = |callee: DefId, callee_args: GenericArgs<'tcx>| {
                let method = tcx.trait_of_assoc(callee).is_some();
                let resolved = method
                    .then(|| {
                        let callee_args = match generic {
                            Some(generic) if !generic.is_empty() => {
                                ty::EarlyBinder::bind(tcx, callee_args)
                                    .instantiate(tcx, generic)
                                    .skip_norm_wip()
                            }
                            _ => callee_args,
                        };
                        // The walked frame's environment: instantiated, the
                        // arguments name the key's parameters, which its env
                        // holds and this body's need not.
                        let typing_env = match generic_env {
                            Some(env) => ty::TypingEnv::post_analysis(tcx, env),
                            None if generic.is_some_and(|generic| !generic.is_empty()) => {
                                ty::TypingEnv::fully_monomorphized()
                            }
                            None => body.typing_env(tcx),
                        };
                        let callee_args = tcx
                            .try_normalize_erasing_regions(
                                typing_env,
                                ty::Unnormalized::new_wip(callee_args),
                            )
                            .ok()?;
                        Instance::try_resolve(tcx, typing_env, callee, callee_args).ok().flatten()
                    })
                    .flatten()
                    .map(|instance| instance.def);
                match (target, resolved) {
                    (Some(Key::Body { def: to, .. }), Some(InstanceKind::Item(item))) => item == to,
                    (Some(Key::Body { def: to, .. }), None) if !method => callee == to,
                    (_, Some(InstanceKind::Item(_))) => false,
                    _ => true,
                }
            };
            // What defines each local, read once.
            let mut assigned: FxHashMap<mir::Local, Vec<&mir::Rvalue<'tcx>>> = FxHashMap::default();
            let mut set: FxHashMap<mir::Local, Vec<String>> = FxHashMap::default();
            let mut returned: FxHashSet<mir::Local> = FxHashSet::default();
            let mut borrowed_mut: FxHashSet<mir::Local> = FxHashSet::default();
            let mut tuples: FxHashMap<mir::Local, Vec<mir::Operand<'tcx>>> = FxHashMap::default();
            for block in body.basic_blocks.iter() {
                for statement in &block.statements {
                    match &statement.kind {
                        mir::StatementKind::Assign(assign) => {
                            let (target, rvalue) = &**assign;
                            // A `&mut` of the value: what is written through
                            // it is not seen.
                            if let mir::Rvalue::Ref(_, mir::BorrowKind::Mut { .. }, borrowed)
                            | mir::Rvalue::RawPtr(mir::RawPtrKind::Mut, borrowed) = rvalue
                            {
                                borrowed_mut.insert(borrowed.local);
                            }
                            if !target.projection.is_empty() {
                                continue;
                            }
                            assigned.entry(target.local).or_default().push(rvalue);
                            if let mir::Rvalue::Aggregate(kind, operands) = rvalue {
                                if matches!(**kind, mir::AggregateKind::Tuple) {
                                    tuples
                                        .entry(target.local)
                                        .or_insert_with(|| operands.iter().cloned().collect());
                                }
                            }
                        }
                        mir::StatementKind::SetDiscriminant { place, variant_index }
                            if place.projection.is_empty() =>
                        {
                            set.entry(place.local)
                                .or_default()
                                .push(adt.variant(*variant_index).name.to_string());
                        }
                        _ => {}
                    }
                }
                // A call's result: what the callee returns is not traced.
                if let Some(mir::Terminator {
                    kind: TerminatorKind::Call { destination, .. },
                    ..
                }) = &block.terminator
                {
                    returned.insert(destination.local);
                }
            }
            // Every call of the callee at the site: a macro's repetitions
            // share one span.
            let mut found = false;
            let mut starts: Vec<mir::Local> = Vec::new();
            for block in body.basic_blocks.iter() {
                let Some(terminator) = block.terminator.as_ref() else { continue };
                let TerminatorKind::Call { func, args, .. } = &terminator.kind else { continue };
                if terminator.source_info.span != span {
                    continue;
                }
                let callee = func.const_fn_def();
                if let Some((callee, callee_args)) = callee {
                    if !is_edge_call(callee, callee_args) {
                        continue;
                    }
                }
                found = true;
                // A call through the Fn traits (`f(x)` for a closure, a fn
                // item or a type parameter) passes the callee's parameters
                // as one tuple after the callee itself.
                let tupled = callee.is_some_and(|(callee, _)| {
                    tcx.trait_of_assoc(callee)
                        .is_some_and(|trait_def| tcx.fn_trait_kind_from_def_id(trait_def).is_some())
                });
                let operands: Vec<mir::Operand<'tcx>> = match position {
                    None => {
                        // The outside code is handed the message here. What
                        // else it is handed may hold more of them.
                        for arg in args.iter() {
                            let ty = instantiated(arg.node.ty(body, tcx));
                            if ty != message && holds(ty) {
                                complete = false;
                            }
                        }
                        args.iter()
                            .map(|arg| arg.node.clone())
                            .filter(|arg| instantiated(arg.ty(body, tcx)) == message)
                            .collect()
                    }
                    Some(parameter) if !tupled => {
                        args.get(parameter).map(|arg| arg.node.clone()).into_iter().collect()
                    }
                    Some(parameter) => args
                        .get(1)
                        .and_then(|arg| arg.node.place())
                        .filter(|tuple| tuple.projection.is_empty())
                        .and_then(|tuple| tuples.get(&tuple.local))
                        .and_then(|operands| operands.get(parameter).cloned())
                        .into_iter()
                        .collect(),
                };
                if operands.is_empty() {
                    complete = false;
                }
                for operand in operands {
                    match operand.place() {
                        Some(place) if place.projection.is_empty() => starts.push(place.local),
                        _ => complete = false,
                    }
                }
            }
            if !found {
                complete = false;
                return;
            }
            let mut pending = starts;
            let mut seen: FxHashSet<mir::Local> = FxHashSet::default();
            while let Some(local) = pending.pop() {
                if !seen.insert(local) {
                    continue;
                }
                if borrowed_mut.contains(&local) {
                    complete = false;
                }
                let mut defined = false;
                for rvalue in assigned.get(&local).map_or(&[][..], Vec::as_slice) {
                    defined = true;
                    match rvalue {
                        mir::Rvalue::Aggregate(kind, _) => match **kind {
                            mir::AggregateKind::Adt(def, variant, ..) if def == adt.did() => {
                                variants.insert(adt.variant(variant).name.to_string());
                            }
                            _ => complete = false,
                        },
                        mir::Rvalue::Use(operand, _) => match operand.place() {
                            Some(source) if source.projection.is_empty() => {
                                pending.push(source.local);
                            }
                            _ => complete = false,
                        },
                        _ => complete = false,
                    }
                }
                for name in set.get(&local).map_or(&[][..], Vec::as_slice) {
                    defined = true;
                    variants.insert(name.clone());
                }
                if returned.contains(&local) {
                    defined = true;
                    complete = false;
                }
                let index = local.as_usize();
                if (1..=body.arg_count).contains(&index) {
                    // The caller's value, whatever the body may also assign.
                    through.insert(index);
                } else if !defined {
                    complete = false;
                }
            }
        });
        for index in through {
            // A closure's locals are its environment, then its parameters.
            let first = if closure { 2 } else { 1 };
            if index < first {
                complete = false;
                continue;
            }
            // Outside code calls this body too, with a value of its own.
            if open.contains(&edge.from) {
                complete = false;
            }
            let parameter: Position = Some(index - first);
            let mut any = false;
            let mut frontier = vec![edge.from];
            let mut stepped: FxHashSet<ReachNode> = FxHashSet::default();
            while let Some(node) = frontier.pop() {
                if !stepped.insert(node) {
                    continue;
                }
                for caller in callers.get(&node).map_or(&[][..], Vec::as_slice) {
                    if local_body(caller.from).is_some() {
                        any = true;
                        work.push((*caller, parameter));
                    } else if forwards(caller.from) {
                        frontier.push(caller.from);
                    } else {
                        // Called by code outside the crate, with a value the
                        // census does not see.
                        complete = false;
                    }
                }
            }
            if !any {
                complete = false;
            }
        }
    }
    (variants.into_iter().collect(), complete)
}

/// Names for rows and witnesses.
struct Render<'r, 'tcx> {
    tcx: TyCtxt<'tcx>,
    keys: &'r [Key<'tcx>],
    census: &'r ReachCensus,
}

impl<'tcx> Render<'_, 'tcx> {
    fn key(&self, node: ReachNode) -> Option<Key<'tcx>> {
        match self.census.expanded().node(node)? {
            ReachNodeKind::Program(ReachNodeSpec { origin: NodeOrigin::Mir(index), .. }) => {
                self.keys.get(*index as usize).copied()
            }
            ReachNodeKind::Program(_) | ReachNodeKind::Sink(_) | ReachNodeKind::Hub => None,
        }
    }

    fn is_local_body(&self, node: ReachNode) -> bool {
        match self.key(node) {
            Some(Key::Body { def, .. }) => def.is_local(),
            Some(Key::Shim { instance, .. }) => instance.def_id().is_local(),
            _ => false,
        }
    }

    /// The row kind of an edge of `strength` (design §5.5).
    fn kind(&self, edge: &ReachEdge, strength: Verdict) -> SpawnRowKind {
        match strength {
            Verdict::Spawns => {
                if matches!(self.key(edge.to), Some(Key::Seed(_))) {
                    SpawnRowKind::DirectSpawn
                } else if edge.via_drop {
                    let local_drop = self.is_local_body(edge.to)
                        || self.census.witness(edge.to).is_some_and(|witness| {
                            witness
                                .path
                                .iter()
                                .any(|step| step.via_drop && self.is_local_body(step.to))
                        });
                    SpawnRowKind::DropSpawns { local_drop }
                } else {
                    SpawnRowKind::CallSpawns { local: self.is_local_body(edge.to) }
                }
            }
            Verdict::Escapes => match edge.class {
                EdgeClass::Create if edge.via_drop => SpawnRowKind::HandsDropGlue,
                EdgeClass::Create if self.census.verdict(edge.to) == Verdict::Spawns => {
                    SpawnRowKind::CreatesSpawning
                }
                EdgeClass::Create => SpawnRowKind::CreatesEscaping,
                EdgeClass::Read => SpawnRowKind::ReadsSpawning,
                EdgeClass::Run | EdgeClass::Approx | EdgeClass::Param => {
                    SpawnRowKind::CalleeEscapes
                }
            },
            Verdict::Indirect => match edge.class {
                EdgeClass::Approx => SpawnRowKind::IndirectCallMaySpawn,
                EdgeClass::Run | EdgeClass::Create | EdgeClass::Read | EdgeClass::Param => {
                    SpawnRowKind::ReachesIndirect
                }
            },
            Verdict::Unknown | Verdict::Quiet => SpawnRowKind::NotEnumerated,
        }
    }

    /// Rendered without trimmed paths: the census runs whether or not a
    /// diagnostic is emitted, and trimmed paths may only be computed for one.
    ///
    /// A long name is [`cut`].
    fn name(&self, node: ReachNode) -> String {
        cut(rustc_middle::ty::print::with_no_trimmed_paths!(self.name_untrimmed(node)))
    }

    fn name_untrimmed(&self, node: ReachNode) -> String {
        let tcx = self.tcx;
        match self.census.expanded().node(node) {
            Some(ReachNodeKind::Sink(reason)) => return sink_text(reason),
            // A witness looks through hubs; none is ever named.
            Some(ReachNodeKind::Hub) | None => return "?".into(),
            Some(ReachNodeKind::Program(_)) => {}
        }
        match self.key(node) {
            Some(Key::Body { def, args, .. }) => {
                if args.types().next().is_some() && !args.has_param() {
                    tcx.def_path_str_with_args(def, args)
                } else {
                    tcx.def_path_str(def)
                }
            }
            Some(Key::Shim { instance, .. }) => format!("{instance}"),
            Some(Key::Value { def, .. }) => tcx.def_path_str(def),
            Some(Key::Promoted { def, promoted, .. }) => {
                format!("{}::promoted[{}]", tcx.def_path_str(def), promoted.as_usize())
            }
            Some(Key::Drop { ty, .. }) => format!("drop glue of `{ty}`"),
            Some(Key::Clone { ty, .. }) => format!("clone of `{ty}`"),
            Some(Key::Seed(def)) => tcx.def_path_str(def),
            Some(Key::Opaque(def)) => format!("foreign `{}`", tcx.def_path_str(def)),
            Some(Key::Outside(world)) => world_name(world).into(),
            Some(Key::Param) => "a type parameter".into(),
            None => "?".into(),
        }
    }

    /// Trust (SC-8 (c)): does `node`'s UNKNOWN verdict rest on the crate-wide
    /// unclosed flag — does its witness end at an `UnclosedPool` or `OpenPrincipal`
    /// sink, rather than at a sink of its own (a MIR-less callee, inline assembly)?
    fn decided_by_unclosed_pools(&self, node: ReachNode) -> bool {
        let base = self
            .census
            .witness(node)
            .and_then(|witness| witness.path.last().map(|edge| edge.to))
            .unwrap_or(node);
        matches!(
            self.census.expanded().node(base),
            Some(ReachNodeKind::Sink(
                DependencyRefusalKind::UnclosedPool | DependencyRefusalKind::OpenPrincipal
            ))
        )
    }

    /// The shortest admitted path from `node` to the base of its verdict.
    fn witness(&self, node: ReachNode) -> String {
        let Some(witness) = self.census.witness(node) else { return String::new() };
        let mut names = vec![self.name(node)];
        names.extend(witness.path.iter().map(|edge| self.name(edge.to)));
        const KEEP: usize = 5;
        if names.len() > KEEP {
            let tail = names.split_off(names.len() - 2);
            names.truncate(KEEP - 2);
            names.push("…".into());
            names.extend(tail);
        }
        names.join(" → ")
    }

    /// The whole witness with each edge's class and every name uncut, for
    /// `TRUST_SPAWN_CENSUS_DEBUG` (a cut name can hide whether a callee is a
    /// fn item or a fn pointer).
    fn full_witness(&self, node: ReachNode) -> String {
        let name =
            |node| rustc_middle::ty::print::with_no_trimmed_paths!(self.name_untrimmed(node));
        let Some(witness) = self.census.witness(node) else { return String::new() };
        let mut out = name(node);
        for edge in &witness.path {
            out.push_str(&format!(
                " -{:?}{}-> {}",
                edge.class,
                if edge.via_drop { "/drop" } else { "" },
                name(edge.to)
            ));
        }
        out
    }
}

/// Each temporary's only assignment, for the two single-assignment readings
/// ([`reified_operand`], [`erases_local_reference`]): a temporary assigned
/// exactly once, as a whole, and never borrowed (`&`, `&mut`, `&raw`),
/// written through a projection, named as a place by any other statement, a
/// call's destination or a yield's resume argument. A body with inline
/// assembly has none (an output operand writes a place). One pass per walked
/// body: asking per coercion rescanned the body each time (quadratic in a
/// body with thousands of `&local as &dyn Debug`).
pub(crate) struct SingleAssignments {
    /// Per local: its only assignment, or `None`.
    only: Vec<Option<Location>>,
}

impl SingleAssignments {
    pub(crate) fn of(body: &mir::Body<'_>) -> Self {
        #[derive(Clone, Copy)]
        enum Seen {
            Unassigned,
            Once(Location),
            Disqualified,
        }
        let locals = body.local_decls.len();
        if body
            .basic_blocks
            .iter()
            .any(|block| matches!(block.terminator().kind, TerminatorKind::InlineAsm { .. }))
        {
            return SingleAssignments { only: vec![None; locals] };
        }
        let mut seen = vec![Seen::Unassigned; locals];
        let disqualify = |seen: &mut Vec<Seen>, local: mir::Local| {
            seen[local.as_usize()] = Seen::Disqualified;
        };
        for (block, data) in body.basic_blocks.iter_enumerated() {
            for (statement_index, statement) in data.statements.iter().enumerate() {
                match &statement.kind {
                    mir::StatementKind::Assign((place, rvalue)) => {
                        if let mir::Rvalue::Ref(_, _, borrowed) | mir::Rvalue::RawPtr(_, borrowed) =
                            rvalue
                        {
                            disqualify(&mut seen, borrowed.local);
                        }
                        let slot = &mut seen[place.local.as_usize()];
                        *slot = match (*slot, place.projection.is_empty()) {
                            (Seen::Unassigned, true) => {
                                Seen::Once(Location { block, statement_index })
                            }
                            _ => Seen::Disqualified,
                        };
                    }
                    other => {
                        for local in places_named(other) {
                            disqualify(&mut seen, local);
                        }
                    }
                }
            }
            match &data.terminator().kind {
                TerminatorKind::Call { destination, .. } => {
                    disqualify(&mut seen, destination.local)
                }
                TerminatorKind::Yield { resume_arg, .. } => disqualify(&mut seen, resume_arg.local),
                _ => {}
            }
        }
        let only = seen
            .into_iter()
            .map(|seen| match seen {
                Seen::Once(location) => Some(location),
                Seen::Unassigned | Seen::Disqualified => None,
            })
            .collect();
        SingleAssignments { only }
    }

    /// The rvalue of `local`'s only assignment, when it is a temporary that
    /// has one.
    fn rvalue<'b, 'tcx>(
        &self,
        body: &'b mir::Body<'tcx>,
        local: mir::Local,
    ) -> Option<&'b mir::Rvalue<'tcx>> {
        if body.local_kind(local) != mir::LocalKind::Temp {
            return None;
        }
        let location = (*self.only.get(local.as_usize())?)?;
        match &body.stmt_at(location).left()?.kind {
            mir::StatementKind::Assign((_, rvalue)) => Some(rvalue),
            _ => None,
        }
    }
}

/// The fn item a fn-pointer operand certainly holds: a temporary whose only
/// assignment ([`SingleAssignments`]) reifies a constant fn item.
fn reified_operand<'tcx>(
    body: &mir::Body<'tcx>,
    assignments: &SingleAssignments,
    operand: &mir::Operand<'tcx>,
) -> Option<Ty<'tcx>> {
    let local = operand.place()?.as_local()?;
    match assignments.rvalue(body, local)? {
        mir::Rvalue::Cast(
            mir::CastKind::PointerCoercion(PointerCoercion::ReifyFnPointer(_), _),
            mir::Operand::Constant(constant),
            _,
        ) if matches!(constant.ty().kind(), ty::FnDef(..)) => Some(constant.ty()),
        _ => None,
    }
}

/// Whether the statement at `location` reifies a fn item into a temporary
/// ([`SingleAssignments`]) whose every use is as the `try_fn` or `catch_fn`
/// operand (the first or third) of a `catch_unwind` intrinsic call: that
/// fn pointer is only ever called by the intrinsic (SC-7h).
fn reified_for_catch_unwind_only<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
    assignments: &SingleAssignments,
    location: Location,
) -> bool {
    let Some(statement) = body.stmt_at(location).left() else { return false };
    let mir::StatementKind::Assign((
        place,
        mir::Rvalue::Cast(
            mir::CastKind::PointerCoercion(PointerCoercion::ReifyFnPointer(_), _),
            mir::Operand::Constant(_),
            _,
        ),
    )) = &statement.kind
    else {
        return false;
    };
    let Some(temp) = place.as_local() else { return false };
    if assignments.rvalue(body, temp).is_none() {
        return false;
    }
    struct Uses<'b, 'tcx> {
        tcx: TyCtxt<'tcx>,
        body: &'b mir::Body<'tcx>,
        temp: mir::Local,
        definition: Location,
        intrinsic: bool,
        other: bool,
    }
    impl<'tcx> mir::visit::Visitor<'tcx> for Uses<'_, 'tcx> {
        fn visit_local(
            &mut self,
            local: mir::Local,
            context: mir::visit::PlaceContext,
            location: Location,
        ) {
            if local != self.temp
                || location == self.definition
                || matches!(context, mir::visit::PlaceContext::NonUse(_))
            {
                return;
            }
            let as_operand = self.body.stmt_at(location).right().is_some_and(|terminator| {
                let TerminatorKind::Call { func, args, destination, .. } = &terminator.kind else {
                    return false;
                };
                let catch_unwind = matches!(
                    *func.ty(self.body, self.tcx).kind(),
                    ty::FnDef(def, _) if self.tcx.intrinsic(def).is_some_and(|intrinsic| intrinsic.name == sym::catch_unwind)
                );
                let named = |operand: &mir::Operand<'tcx>| {
                    operand.place().is_some_and(|place| {
                        place.local == self.temp
                            || place.projection.iter().any(
                                |elem| matches!(elem, mir::ProjectionElem::Index(index) if index == self.temp),
                            )
                    })
                };
                catch_unwind
                    && !named(func)
                    && destination.local != self.temp
                    && args.iter().enumerate().all(|(index, arg)| {
                        !named(&arg.node)
                            || ((index == 0 || index == 2)
                                && arg.node.place().and_then(|place| place.as_local())
                                    == Some(self.temp))
                    })
            });
            if as_operand {
                self.intrinsic = true;
            } else {
                self.other = true;
            }
        }
    }
    let mut uses = Uses { tcx, body, temp, definition: location, intrinsic: false, other: false };
    mir::visit::Visitor::visit_body(&mut uses, body);
    uses.intrinsic && !uses.other
}

/// Whether the unsizing coercion at `location` erases a reference to a local
/// of `body` (design §5.4, confinement): its operand is a temporary whose
/// only assignment ([`SingleAssignments`]) is `&place` or `&mut place` with no
/// dereference in `place`. Borrowck then bounds every copy of the erased
/// reference by that local's storage.
fn erases_local_reference<'tcx>(
    body: &mir::Body<'tcx>,
    assignments: &SingleAssignments,
    location: Location,
) -> bool {
    let Some(statement) = body.stmt_at(location).left() else { return false };
    let mir::StatementKind::Assign((
        _,
        mir::Rvalue::Cast(mir::CastKind::PointerCoercion(PointerCoercion::Unsize, _), operand, _),
    )) = &statement.kind
    else {
        return false;
    };
    let Some(local) = operand.place().and_then(|place| place.as_local()) else { return false };
    matches!(
        assignments.rvalue(body, local),
        Some(mir::Rvalue::Ref(_, _, borrowed)) if !borrowed.is_indirect()
    )
}

/// The locals a non-assignment statement names as a place it may write
/// (`SetDiscriminant`, an intrinsic's operands) or otherwise mentions.
fn places_named(kind: &mir::StatementKind<'_>) -> Vec<mir::Local> {
    match kind {
        mir::StatementKind::SetDiscriminant { place, .. }
        | mir::StatementKind::PlaceMention(place) => vec![place.local],
        mir::StatementKind::AscribeUserType((place, _), _) => vec![place.local],
        mir::StatementKind::Intrinsic(intrinsic) => match intrinsic {
            mir::NonDivergingIntrinsic::Assume(operand) => {
                operand.place().map(|place| place.local).into_iter().collect()
            }
            mir::NonDivergingIntrinsic::CopyNonOverlapping(copy) => {
                [&copy.src, &copy.dst, &copy.count]
                    .into_iter()
                    .filter_map(|operand| operand.place().map(|place| place.local))
                    .collect()
            }
        },
        mir::StatementKind::Assign(..)
        | mir::StatementKind::FakeRead(..)
        | mir::StatementKind::StorageLive(_)
        | mir::StatementKind::StorageDead(_)
        | mir::StatementKind::Coverage(..)
        | mir::StatementKind::ConstEvalCounter
        | mir::StatementKind::Nop
        | mir::StatementKind::BackwardIncompatibleDropHint { .. } => Vec::new(),
    }
}

/// Whether an `asm!` runs no instruction and writes no place but through an
/// `inout` register: it is no `naked_asm!`, no operand is a `sym` (a symbol
/// its template could name), a `label` (a block it could jump to) or an `out`
/// or `lateout` place (which receives whatever its register held: a `lateout`
/// may share an input's register, an `out` holds an unknown value), and its
/// template, each placeholder standing for its operand's text, is only ASCII
/// whitespace and C block comments. An operand's text is a register name or an
/// immediate, which never holds `*/` or a line break, so a placeholder inside a
/// comment stays inside it. zmij's value barrier, `asm!("/*{0}*/", inout(reg)
/// x)` (serde_json's number formatter), is one: it assembles to nothing, so it
/// calls nothing and mints nothing (P2m cost 5). Its `inout` registers still
/// pass an input's bits to an output place, which the walker reads as a
/// transmute (`inout(reg) f => n` is a LAUNDER). Every other inline assembly
/// is an UNKNOWN sink.
pub(crate) fn asm_executes_nothing(
    asm_macro: mir::InlineAsmMacro,
    template: &[impl std::fmt::Display],
    operands: &[mir::InlineAsmOperand<'_>],
) -> bool {
    if asm_macro != mir::InlineAsmMacro::Asm
        || operands.iter().any(|operand| {
            matches!(
                operand,
                mir::InlineAsmOperand::SymFn { .. }
                    | mir::InlineAsmOperand::SymStatic { .. }
                    | mir::InlineAsmOperand::Label { .. }
                    | mir::InlineAsmOperand::Out { place: Some(_), .. }
            )
        })
    {
        return false;
    }
    // A piece renders as the `asm!` source does: a literal `{` or `}` doubled,
    // a placeholder as `{N}` or `{N:m}`.
    let rendered: String = template.iter().map(|piece| piece.to_string()).collect();
    let mut text = String::with_capacity(rendered.len());
    let mut chars = rendered.chars().peekable();
    while let Some(c) = chars.next() {
        match c {
            '{' if chars.peek() == Some(&'{') => {
                chars.next();
                text.push('{');
            }
            '}' if chars.peek() == Some(&'}') => {
                chars.next();
                text.push('}');
            }
            '{' => {
                // A placeholder: an operand index, then an optional modifier.
                let mut digits = 0;
                while chars.peek().is_some_and(|c| c.is_ascii_digit()) {
                    chars.next();
                    digits += 1;
                }
                if chars.peek() == Some(&':') {
                    chars.next();
                    if chars.next().is_none_or(|modifier| !modifier.is_ascii_alphanumeric()) {
                        return false;
                    }
                }
                if digits == 0 || chars.next() != Some('}') {
                    return false;
                }
                text.push('x');
            }
            '}' => return false,
            other => text.push(other),
        }
    }
    let mut rest = text.as_str();
    loop {
        rest = rest.trim_start_matches(|c: char| c.is_ascii_whitespace());
        if rest.is_empty() {
            return true;
        }
        let Some(comment) = rest.strip_prefix("/*") else { return false };
        let Some(end) = comment.find("*/") else { return false };
        rest = &comment[end + 2..];
    }
}

/// Whether `krate` is one this compiler's sysroot supplies: the real sysroot
/// crates, and every crate loaded from the sysroot's own target library
/// directory (`compiler_builtins`, the panic runtimes, libtest's runner).
/// The census's trust-ir lane reads the same rule for its foreign world
/// (`trust_thir_lower::spawn_census`).
pub fn in_sysroot(tcx: TyCtxt<'_>, krate: rustc_span::def_id::CrateNum) -> bool {
    crate::convert::is_real_sysroot_crate(tcx, krate)
        || crate::convert::crate_is_sysroot_resident(tcx, krate)
}

/// The functions and statics of the dependency `krate` that may be linked
/// under a name of their own or as a runtime symbol: what its encoded export
/// list names. A crate compiled without codegen encodes an EMPTY list
/// (`rustc_codegen_ssa::back::symbol_export`, `should_codegen`), and
/// `targo trust check` compiles every library dependency check-only, so an
/// empty list is read past: every non-generic function and static of the
/// crate is a candidate, and each caller keeps the ones whose own attributes
/// link them by name, as it does the list's. A crate linked for its macros
/// only is skipped (it runs in nothing this crate builds).
pub fn linked_candidates(tcx: TyCtxt<'_>, krate: rustc_span::def_id::CrateNum) -> Vec<DefId> {
    let listed: Vec<DefId> = tcx
        .exported_non_generic_symbols(krate)
        .iter()
        .filter_map(|(symbol, _)| match *symbol {
            ExportedSymbol::NonGeneric(def) => Some(def),
            _ => None,
        })
        .collect();
    if !listed.is_empty() || tcx.crate_dep_kind(krate).macros_only() {
        return listed;
    }
    (0..tcx.num_extern_def_ids(krate))
        .map(|position| DefId { krate, index: rustc_span::def_id::DefIndex::from_usize(position) })
        .filter(|&def| {
            matches!(
                tcx.def_kind(def),
                DefKind::Fn | DefKind::AssocFn | DefKind::Static { nested: false, .. }
            ) && !tcx.generics_of(def).requires_monomorphization(tcx)
        })
        .collect()
}

/// Whether foreign code can reach the static `def` without being handed its
/// address: it is linked under a name of its own (`#[no_mangle]`,
/// `#[export_name]`, an external linkage) or placed in a named section
/// (`#[link_section]`), which foreign code and the loader enumerate. A
/// sysroot static is the platform runtime's, as the sysroot's exported
/// functions are ([`SymbolTables`]). `#[used]` alone keeps a static in the
/// object but gives foreign code no name for it. An `extern` static is
/// foreign memory by declaration, charged where a walked node names it. Both
/// census lanes read this one rule (`trust_thir_lower::spawn_census`).
pub fn static_named_by_foreign_code(tcx: TyCtxt<'_>, def: DefId) -> bool {
    if !matches!(tcx.def_kind(def), DefKind::Static { nested: false, .. })
        || tcx.is_foreign_item(def)
        || in_sysroot(tcx, def.krate)
    {
        return false;
    }
    let attrs = tcx.codegen_fn_attrs(def);
    attrs.contains_extern_indicator() || attrs.link_section.is_some()
}

/// The type whose drop glue a call of `def` runs, when `def` is the `DropGlue`
/// lang item (`core::ptr::drop_glue`, what `ptr::drop_in_place` calls).
fn drop_glue_call<'tcx>(
    tcx: TyCtxt<'tcx>,
    def: DefId,
    args: GenericArgs<'tcx>,
) -> Option<Ty<'tcx>> {
    if tcx.is_lang_item(def, LangItem::DropGlue) { args.types().next() } else { None }
}

/// Whether an indirect call of `called` may reach a pool member filed under
/// `member`: function pointers of matching shapes (a LAUNDER changes no
/// shape: a call at a shape its callee's does not match is UB, R4, see
/// `ClosedPools::pool`), or `dyn` slots of the same method (or both drop
/// slots), whatever the principal, since upcasts carry members between
/// principals.
fn keys_meet(member: &PoolKey, called: &PoolKey) -> bool {
    match (member, called) {
        (PoolKey::Fn(member), PoolKey::Fn(called)) => member.matches(called),
        (PoolKey::DynMethod { method: member, .. }, PoolKey::DynMethod { method: called, .. }) => {
            member == called
        }
        (PoolKey::DynDrop(_), PoolKey::DynDrop(_)) => true,
        _ => false,
    }
}

/// The pool each world's node calls its members through: a principal no
/// `dyn` type has (a fixed key outside the principal hashes' range is not
/// guaranteed; a collision only merges two pools, which is coarser).
fn world_principal(world: World) -> PrincipalKey {
    let mut hasher = FxHasher::default();
    "trust spawn census: the world of code it cannot walk".hash(&mut hasher);
    world.index().hash(&mut hasher);
    PrincipalKey(hasher.finish())
}

/// How a world's node is named in a witness.
fn world_name(world: World) -> &'static str {
    match world {
        World::Foreign => {
            "what foreign code may call (a callable handed to it or stored where it reads, an \
             exported symbol)"
        }
        World::Rust => {
            "what MIR-less Rust may call (the allocator, the panic handler, what foreign code may)"
        }
    }
}

/// Trust (SC-8 (c), 2026-10-11; docs/DECISION_QUEUE.md "SC-8"): why every pool is
/// unclosed, or `None` when the engine closed them. Each open principal (the `dyn`
/// type, the node whose fact first named it, and whether its values enter from out of
/// sight — a local body's argument, a mutable static, what MIR-less or foreign code
/// returns), then each UNKNOWN sink the adapter added (its reason and the first node
/// that met it): exactly what sets the engine's crate-wide flag
/// (`unenumerated || !open.is_empty()`, SC-5 (b)). Everything here was already
/// recorded for `TRUST_SPAWN_CENSUS_DEBUG`; the disclosure adds no analysis and no
/// premise.
fn unclosed_root_cause<'tcx>(
    render: &Render<'_, 'tcx>,
    principals: &FxHashMap<u64, &'tcx ty::List<ty::PolyExistentialPredicate<'tcx>>>,
    named_at: &FxHashMap<PrincipalKey, ReachNode>,
    entering: &BTreeSet<PrincipalKey>,
    sinks: &BTreeMap<String, (usize, String)>,
    sink_texts: &BTreeMap<String, String>,
) -> Option<Vec<String>> {
    let expanded = render.census.expanded();
    let pools = expanded.pools();
    if !pools.unclosed() {
        return None;
    }
    let tcx = render.tcx;
    let mut causes = Vec::new();
    for key in pools.open_principals() {
        let name = principals.get(&key.0).map_or_else(
            || format!("{:x}", key.0),
            |predicates| {
                rustc_middle::ty::print::with_no_trimmed_paths!(format!(
                    "{}",
                    Ty::new_dynamic(tcx, predicates, tcx.lifetimes.re_erased)
                ))
            },
        );
        let at = named_at.get(key).map_or_else(|| "?".to_string(), |node| render.name(*node));
        let enters =
            if entering.contains(key) { ", its values entering from out of sight" } else { "" };
        causes.push(format!("open principal `{}` @ {at}{enters}", cut(name)));
    }
    for (reason, (_, at)) in sinks {
        let text = sink_texts.get(reason).map_or(reason.as_str(), String::as_str);
        causes.push(format!("UNKNOWN sink {text} @ {}", cut(at.clone())));
    }
    if causes.is_empty() {
        // The engine's flag with neither recorded: say so rather than name nothing.
        causes.push("no open principal or adapter sink recorded".to_string());
    }
    Some(causes)
}

/// The SC-8 back-reference a NotEnumerated row the unclosed flag decides carries, spelled
/// by trust-types' `sc8_row_disclosure` (T3 L4, C06a): the causes come in the order of
/// their principals' type hashes, which follow the crates' `StableCrateId`s, so the
/// elision audit reads the disclosure by its constants (L4-AUDIT-7).
fn unclosed_row_suffix(causes: &[String]) -> String {
    trust_types::sc8_row_disclosure(causes)
}

/// The one crate-level SC-8 root-cause note. The user-side remedy (R1/SC-3) is
/// named only when an open principal is among the causes.
fn unclosed_crate_note(causes: &[String], rows: usize) -> String {
    let remedy = if causes.iter().any(|cause| cause.starts_with("open principal")) {
        " Remedy for an open principal entering through a parameter: take the callable \
         generically (`impl Fn..` or `T: Trait`) instead of as `&dyn` (R1/SC-3)."
    } else {
        ""
    };
    format!(
        "spawn census root cause (SC-8): pools unclosed because: {}. Every indirect call's \
         pool stays open while any of these holds (SC-5 (b)), so {rows} UNKNOWN row(s) that \
         reach an indirect call stay UNKNOWN; nothing is credited.{remedy}",
        causes.join(" / ")
    )
}

fn sink_text(reason: &DependencyRefusalKind) -> String {
    match reason {
        DependencyRefusalKind::InlineAsm => "inline assembly".into(),
        DependencyRefusalKind::AsyncDropShim => "an async drop".into(),
        DependencyRefusalKind::CoroutineClone => "a coroutine clone".into(),
        DependencyRefusalKind::ResolutionError => {
            "a callee rustc's resolver did not resolve".into()
        }
        DependencyRefusalKind::Widened => {
            "an instance nested deeper than the recursion limit".into()
        }
        DependencyRefusalKind::UnresolvedExtern => {
            "Rust code with no MIR here (a MIR-less sysroot item, or a MIR-less function that \
             may hand back a callable it minted)"
                .into()
        }
        DependencyRefusalKind::GlobalAssembly => {
            "module-level assembly (`global_asm!`), which foreign calls may reach".into()
        }
        DependencyRefusalKind::UncoveredMention => "a mentioned item no fact covers".into(),
        DependencyRefusalKind::OpenPrincipal => {
            "a `dyn` principal open to values from out of sight".into()
        }
        DependencyRefusalKind::UnclosedPool => "an indirect call whose pool is not closed".into(),
        other => format!("{other:?}"),
    }
}

/// The callables `from` holds in its own bytes that a view at `to` may read
/// as something else (design §10, "typed LAUNDER"): every one, unless `to`
/// holds nothing but fn pointers and one of a matching shape keeps it. The
/// census reads no layout, so a view with any data position may receive a
/// fn pointer's bytes there.
fn reinterpret(from: &OwnBytes<'_>, to: &OwnBytes<'_>) -> Vec<CarriedKey> {
    from.callables.iter().filter(|key| !kept(to, key)).cloned().collect()
}

/// Whether a view at `to` can read the callable `key` only as itself.
fn kept(to: &OwnBytes<'_>, key: &CarriedKey) -> bool {
    let CarriedKey::Key(PoolKey::Fn(shape)) = key else { return false };
    !to.other
        && !to.untyped_view()
        && to.objects.is_empty()
        && to
            .callables
            .iter()
            .any(|held| matches!(held, CarriedKey::Key(PoolKey::Fn(other)) if other.matches(shape)))
}

/// The typing environment a memo of typed-LAUNDER facts about `tys` is keyed
/// by: the frame's, when normalizing one of them may depend on it (a type
/// parameter or an alias), and otherwise one shared by every frame.
fn memo_env<'tcx>(tys: &[Ty<'tcx>], typing_env: ty::TypingEnv<'tcx>) -> ty::TypingEnv<'tcx> {
    if tys.iter().any(|ty| ty.has_param() || ty.has_aliases()) {
        typing_env
    } else {
        ty::TypingEnv::fully_monomorphized()
    }
}

/// The unions whose field a body's places project, or which its aggregates
/// build, each with its first location (route U).
fn union_projections<'tcx>(tcx: TyCtxt<'tcx>, body: &mir::Body<'tcx>) -> Vec<(Ty<'tcx>, Location)> {
    struct Unions<'b, 'tcx> {
        tcx: TyCtxt<'tcx>,
        body: &'b mir::Body<'tcx>,
        found: Vec<(Ty<'tcx>, Location)>,
    }
    impl<'tcx> Unions<'_, 'tcx> {
        fn note(&mut self, ty: Ty<'tcx>, location: Location) {
            if ty.is_union() && !self.found.iter().any(|(seen, _)| *seen == ty) {
                self.found.push((ty, location));
            }
        }
    }
    impl<'tcx> mir::visit::Visitor<'tcx> for Unions<'_, 'tcx> {
        fn visit_place(
            &mut self,
            place: &mir::Place<'tcx>,
            context: mir::visit::PlaceContext,
            location: Location,
        ) {
            for (base, elem) in place.iter_projections() {
                if let mir::ProjectionElem::Field(..) = elem {
                    let ty = base.ty(self.body, self.tcx).ty;
                    self.note(ty, location);
                }
            }
            self.super_place(place, context, location);
        }

        fn visit_rvalue(&mut self, rvalue: &mir::Rvalue<'tcx>, location: Location) {
            if let mir::Rvalue::Aggregate(mir::AggregateKind::Adt(_, _, _, _, Some(_)), _) = rvalue
            {
                let ty = rvalue.ty(self.body, self.tcx);
                self.note(ty, location);
            }
            self.super_rvalue(rvalue, location);
        }
    }
    let mut unions = Unions { tcx, body, found: Vec::new() };
    mir::visit::Visitor::visit_body(&mut unions, body);
    unions.found
}

/// A laundered key, for `TRUST_SPAWN_CENSUS_DEBUG`.
fn key_text(key: &CarriedKey) -> String {
    match key {
        CarriedKey::Key(PoolKey::Fn(shape)) => match &shape.params {
            Some(params) => format!("fn{params:?} (abi {:?})", shape.abi),
            None => format!("fn(..) (abi {:?})", shape.abi),
        },
        other => format!("{other:?}"),
    }
}

fn normalize<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    ty: Ty<'tcx>,
) -> Result<Ty<'tcx>, ()> {
    tcx.try_normalize_erasing_regions(typing_env, ty::Unnormalized::new_wip(ty)).map_err(|_| ())
}
