//! Trust (step 2 increment 4b, 2026-10-01): THE PRODUCER EMITS DROPS.
//!
//! Design: `docs/design/2026-09-29-step2-inc4-drops.md` §3; D18 and D28
//! (`docs/DECISION_QUEUE.md`). Until this module the direct producer modelled no drop at all
//! (`lib.rs`, "uniformly Drop-agnostic"): a by-value parameter or binding whose type needs
//! dropping left the body with its destructor never run, and the effect-conservation gate
//! (`effect_conservation.rs`, D28) tagged every such body `abstracted(drop)` and withdrew it.
//!
//! # What this module computes
//!
//! A port, onto THIR, of the part of rustc's drop scheduling and drop elaboration that the
//! producer can place faithfully today:
//!
//! * **Scheduling** (`rustc_mir_build::builder::scope`): every by-value parameter whose type
//!   needs drop is scheduled in the ARGUMENT scope (`args_and_body`), every simple by-value
//!   `let` binding in its binding scope (`schedule_drop_for_binding` → `var_scope`). Drops run in
//!   reverse schedule order; a scope is exited by falling off its end, or by `return` / `break` /
//!   `continue` crossing it. The drop's span is rustc's: the END POINT of the scheduling scope's
//!   span (`schedule_drop`'s `scope_end`), or the assignment's left-hand side for a
//!   drop-and-replace (`build_drop_and_replace`).
//! * **Move paths and init state** (`rustc_mir_dataflow`): for each tracked ROOT (a whole local)
//!   a three-valued state — definitely initialized, definitely moved out, or maybe — computed by
//!   a structured abstract interpretation over THIR in MIR building's evaluation order, with a
//!   fixpoint at every loop head. A by-value read of the whole root (a place in operand position
//!   whose type is not `Copy`) moves it; a drop-and-replace re-initializes it.
//! * **Elaboration** (`rustc_mir_transform::elaborate_drops`): at each exit EDGE each scheduled
//!   drop is `Dead` (moved out on every path: nothing is emitted), `Static` (initialized on every
//!   path: an `Inst::Drop` is emitted) or `Conditional` (maybe). The producer places drops per
//!   EDGE, so a drop rustc must guard with a flag because two edges share one drop-tree node
//!   (`return` from two points, one after a move) is placed statically on each edge; a
//!   `Conditional` on ONE edge would need a runtime flag, and this cut refuses it.
//!
//! # The 4b residuals (2026-10-08): temporaries, pattern bindings, stores through a pointer
//!
//! The same port, extended to three more of rustc's drop sources:
//!
//! * **Live temporaries** (`as_temp`): a needs-drop rvalue in place position (borrowed, a field
//!   or element read out of it, scrutinized, an autoref receiver), a statement's discarded value
//!   (`stmt_expr`'s fallback temporary) and a `let`'s extended temporary are roots scheduled in
//!   the scope rustc's `temporary_scope` names: a THIR `Scope` expression's `Node` scope, a
//!   statement's scope, a block's own scope, a match arm's scope, or a `let`'s remainder scope.
//!   Each such scope is a frame of the walk, popped (`ScopeEnd`, `StmtEnd`, `BlockEnd`,
//!   `EnclosingEnd`) where the lowering's hooks fire. An `if`'s value condition pops its scopes
//!   on BOTH edges out of the test (`then_else_break`): its temporaries are dropped at the start
//!   of each branch (`CondThen` / `CondElse`). A temporary the program borrows whole is dropped
//!   through the memory its object lives in when the drop runs, PROVED to be the only way the
//!   program reaches it ([`borrowed_temp_home`]: the borrow's slot, or the slot a lowering lane
//!   moved the whole value into — the shared-borrow snapshot lane hands `f(&g())`'s callee such a
//!   copy); unproved, only a shared borrow of a `Freeze` value whose glue only releases memory is
//!   placed (any copy is the same drop), any other is refused. Any other temporary is dropped
//!   through a fresh slot holding its value, only when nothing else observes its address, and a
//!   write into part of a temporary refuses the body.
//! * **By-value pattern bindings** (`bind_matched_candidate_for_arm_body`): a binding of a
//!   needs-drop value is a root in its var scope (the arm's, the `if`'s then-scope, the `let`'s
//!   remainder), and the part of the scrutinee it moves out is a MOVE PATH below the scrutinee's
//!   root (`MoveData`'s field / downcast paths), with its own state. A discriminant test's edges
//!   make the other variants' paths inactive (`MaybeInitializedPlaces`' and
//!   `MaybeUninitializedPlaces`' switch-edge effects). A root with a moved path has an OPEN drop:
//!   its claim is the drop oracle's style for it (`Open`, or dead when every needs-drop field is
//!   gone), and it is placed only on an edge where the open drop's elaboration drops NOTHING
//!   (every needs-drop part moved out or in an inactive variant). An open drop that would drop
//!   a part refuses the body; it is never approximated by a whole drop or by nothing.
//! * **Drop-and-replace through a pointer** (`build_drop_and_replace` of `*p` for a `&mut` or a
//!   raw pointer): one static drop of the old pointee THROUGH the pointer the store uses.
//!
//! # What this cut does not model, and what happens then
//!
//! Drop-and-replace of a sub-place (`x.f = v`, `(*p).f = v`); moves through or-patterns, slice
//! and array patterns, deref patterns, a box's contents; an open drop that drops part of the
//! value (`drop(self.a)` leaving `self.b`) and any other per-edge `Conditional` (a drop flag); a
//! temporary in a condition's scope that `&&` / `||` / a guard tests, in an edition-2024 `if let`
//! scrutinee (`IfThenRescope`), in a match guard's scope, in a let-else initializer or in a
//! labelled block's own scope; a mutably or raw-borrowed tracked value, a shared-borrowed one
//! requiring address identity without an actual promoted home; closures'
//! by-value environments, coroutines, generic or opaque-typed roots. For such a body the planner
//! returns a REASON and the producer emits NO drop at all, so the body is exactly what it was
//! before this module (the effect-conservation gate still tags it `abstracted(drop)` and
//! withdraws it). That is the fail-closed floor: a body either carries every drop rustc's
//! elaboration performs, or none.
//!
//! # How a planned body is checked
//!
//! Three independent walls, each failing closed:
//!
//! 1. **The planner's claim** ([`DropClaim`]): per (root, exit class) — the fallthrough of the
//!    scheduling scope, the function's return tree, a loop's break or continue tree, one
//!    drop-and-replace site — the style JOINED over every edge of that class, which is exactly
//!    the style rustc's elaboration gives the one MIR `Drop` terminator its drop tree builds for
//!    that class. The effect-conservation gate compares the claim against rustc's OWN dataflow
//!    run on the built MIR (`drop_oracle.rs`, the MIR test oracle): a drop the program performs
//!    that the claim lacks reads `abstracted(drop)`; a drop the claim makes that the program
//!    does not perform reads `not-conserved(drop)`. Either refuses the body for codegen and
//!    strict.
//! 2. **The placement tripwire** ([`LowerCx::finish_drops`]): every exit the planner found
//!    reachable with a drop to emit must have been lowered through a hook that emitted it, and
//!    every drop must have been placeable. A lowering lane that seals an exit without the hook
//!    (a summary lane, a lane that peels a block) leaves an exit unfired; then — and on any
//!    placement failure — every node this module placed is removed again and the body keeps its
//!    drops elided (all or nothing), which the gate refuses as `abstracted(drop)`.
//! 3. **The module carries the claim**: the gate counts the `Inst::Drop` nodes of the per-body
//!    function and requires the count of drops the producer recorded emitting.
//! 4. **Three placement guards** (the 4b residuals, in `finish_drops`): an exit whose hook placed
//!    drops twice on ONE path (a lane that lowered the same scope again after the first time —
//!    a double drop the per-class comparison above cannot see), a placement that makes the
//!    per-body module validate worse than without its drops (an operand that does not reach its
//!    drop), and a borrowed temporary's home no longer proved on the finished function (the gate
//!    never reads an `Inst::Drop`'s pointer, so this proof is the wall that the drop runs on the
//!    object the program used) each remove every drop of the body, as the tripwire does.
//!
//! Any body that carries an `Inst::Drop` is forced NOT interpretation-eligible
//! (`Lowered::contains_call`), because the reference interpreter refuses `Inst::Drop` with a
//! `TypeError` that the interpretation differential would report as a THIR defect (design §1.6).
//!
//! # Unwinding
//!
//! Only normal-path drops are modelled. Under `panic=abort` (trust-cg's only mode) that is the
//! program. Under `panic=unwind` the cleanup drops are outside the model and DISCLOSED here, not
//! refused: trust-ir v47 gives `Call` no unwind edge, so the module describes the program under
//! abort-on-panic. A body that reaches `catch_unwind` observes post-panic state; the planner
//! refuses a body with a direct call to `std::panic::catch_unwind` / the `catch_unwind`
//! intrinsic (design §8). Executable semantics and an unwinding drop form are trust-ir amendment
//! D (D20), not this increment.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com> | Copyright 2026 | License: MIT OR Apache-2.0

use std::collections::BTreeMap;

use rustc_middle::middle::region;
use rustc_middle::thir::{
    BlockId as ThirBlockId, BodyTy, ExprId, ExprKind, LocalVarId, Pat, PatKind, StmtKind, Thir,
};
use rustc_middle::ty::{self, Ty as RustcTy, TyCtxt, TypeVisitableExt};
use rustc_span::Span;
use rustc_span::def_id::LocalDefId;
use trust_ir::{Inst, InstrNode, Ty, ValueId};

// New producer hooks stay visible to the canonical producer-source census.
mod owned_shared;

// =============================================================================================
// The mutation knob (tests only).
// =============================================================================================

/// `TRUST_IR_LOWER_MUTATE_DROPS`: a TEST-ONLY mutation of this module, so a fixture can show that
/// the effect-conservation gate refuses a producer whose drops are wrong (design §7.2: "a
/// missing or extra drop still refuses"). Unset in every real build.
///
/// * `ignore-moves` — the planner treats every move as a copy, so a moved value is dropped again
///   (a double drop): the claim has drops the program does not perform (`not-conserved(drop)`).
/// * `skip-emission` — the hooks fire and are counted but emit nothing: the module lacks the
///   drops the producer recorded (`not-conserved(drop)`, the ledger leg).
///
/// Step 2 increment 4b residuals, one per new shape:
///
/// * `temp-outer-scope` — every temporary is scheduled one scope OUT (the next enclosing scope
///   that holds temporaries) and dropped at that scope's end: a temporary dropped at the wrong
///   scope end (`abstracted(drop)` for the drop rustc performs, `not-conserved(drop)` for the
///   one it does not).
/// * `open-as-static` — an open drop of a partially moved value (a pattern binding moved part of
///   it out) is placed as a WHOLE drop: the moved part is dropped twice (`not-conserved(drop)`:
///   the claim says `Static` where rustc's elaboration says `Open`, or a drop it does not
///   perform).
/// * `pointee-twice` — a drop-and-replace through a pointer drops the old pointee twice: the
///   module carries a drop the producer never recorded (`not-conserved(drop)`, the ledger leg).
///
/// The 4b residuals review (2026-10-08):
///
/// * `temp-borrow-slot` — drop a DISTINCT slot initialized from the temporary's original
///   SSA value. This restores the first cut's stale-object defect even when a reborrow now
///   forwards the original borrow slot directly to the callee. Drop-key/count comparison
///   alone cannot detect the wrong address: the run-make pointer pin catches it, or the
///   owned-temporary home guard refuses the body before publication.
fn mutation() -> Option<&'static str> {
    static M: std::sync::OnceLock<Option<&'static str>> = std::sync::OnceLock::new();
    *M.get_or_init(|| match std::env::var("TRUST_IR_LOWER_MUTATE_DROPS").ok().as_deref() {
        Some("ignore-moves") => Some("ignore-moves"),
        Some("skip-emission") => Some("skip-emission"),
        Some("temp-outer-scope") => Some("temp-outer-scope"),
        Some("open-as-static") => Some("open-as-static"),
        Some("pointee-twice") => Some("pointee-twice"),
        Some("temp-borrow-slot") => Some("temp-borrow-slot"),
        _ => None,
    })
}

// =============================================================================================
// The pure kernel: states, styles, exits, the plan. TyCtxt-free, unit-tested below.
// =============================================================================================

pub mod kernel {
    use std::collections::{BTreeMap, BTreeSet};

    /// The initialization state of one tracked root at a program point (rustc's
    /// `MaybeInitializedPlaces` x `MaybeUninitializedPlaces` for a single move path).
    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    pub enum Init {
        /// Moved out (or never initialized) on every path: maybe-uninit only.
        Uninit,
        /// Initialized on every path: maybe-init only.
        Init,
        /// Both.
        Maybe,
    }

    impl Init {
        pub fn join(self, other: Init) -> Init {
            if self == other { self } else { Init::Maybe }
        }
    }

    /// The elaborated style of one drop on one edge (`rustc_mir_transform::elaborate_drop::
    /// DropStyle`). `Open` is split by what the open drop's elaboration does on THIS edge
    /// (step 2 increment 4b residuals: a value partially moved out of, by a pattern binding or
    /// a field move): nothing at all (every needs-drop part already moved or in an inactive
    /// variant), or part of the value — which the producer does not place.
    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
    pub enum Style {
        Dead,
        Static,
        Conditional,
        /// An open drop whose elaboration drops nothing on this edge: nothing is emitted.
        Open,
        /// An open drop whose elaboration drops part of the value on this edge: not placeable.
        OpenLive,
    }

    impl Style {
        pub fn of(init: Init) -> Style {
            match init {
                Init::Uninit => Style::Dead,
                Init::Init => Style::Static,
                Init::Maybe => Style::Conditional,
            }
        }

        /// The style of one MIR drop-tree node reached by edges of these two styles.
        pub fn join(self, other: Style) -> Style {
            if self == other { self } else { Style::Conditional }
        }
    }

    /// The state of every tracked root at a program point, or `reachable == false` for a point
    /// no execution reaches (after `return`, `break`, `continue`, a diverging call).
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct State {
        pub reachable: bool,
        pub init: Vec<Init>,
    }

    impl State {
        /// Function entry with `n` roots: all uninitialized (parameters are initialized by the
        /// caller of [`State::set`]).
        pub fn entry(n: usize) -> State {
            State { reachable: true, init: vec![Init::Uninit; n] }
        }

        pub fn unreachable(n: usize) -> State {
            State { reachable: false, init: vec![Init::Uninit; n] }
        }

        /// The state where two paths meet. An unreachable side contributes nothing. A root one
        /// side has not declared yet (its vector is shorter: the root was declared on the other
        /// path only) is `Uninit` on that side, so the join is `Maybe` where the other side has
        /// it initialized — never silently dropped from the state.
        pub fn join(&self, other: &State) -> State {
            match (self.reachable, other.reachable) {
                (false, _) => other.clone(),
                (_, false) => self.clone(),
                _ => {
                    let n = self.init.len().max(other.init.len());
                    State {
                        reachable: true,
                        init: (0..n).map(|i| self.get(i).join(other.get(i))).collect(),
                    }
                }
            }
        }

        pub fn set(&mut self, root: usize, init: Init) {
            if let Some(slot) = self.init.get_mut(root) {
                *slot = init;
            }
        }

        pub fn get(&self, root: usize) -> Init {
            self.init.get(root).copied().unwrap_or(Init::Uninit)
        }

        /// Make room for root `root` (roots are numbered as they are declared).
        pub fn grow(&mut self, n: usize) {
            if self.init.len() < n {
                self.init.resize(n, Init::Uninit);
            }
        }
    }

    /// Which lowering hook an exit edge is placed by. The `u32`s are THIR ids (`ExprId`,
    /// `BlockId`) of the node the hook lowers.
    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
    pub enum ExitKey {
        /// Falling off the end of THIR block `b`: its `let` bindings leave scope.
        BlockEnd(u32),
        /// Falling off the end of the body: the parameters leave scope.
        BodyEnd,
        /// The `return` expression `e`.
        Return(u32),
        /// The `break` expression `e`.
        Break(u32),
        /// The `continue` expression `e`.
        Continue(u32),
        /// The assignment `e` to a whole tracked root (drop-and-replace), or through a pointer
        /// (`*p = v`: the old pointee is dropped through the pointer the store goes through).
        Replace(u32),
        /// Trust (step 2 increment 4b residuals): falling off the end of the THIR `Scope`
        /// expression `e` — its region scope (`ScopeData::Node`) pops, and the temporaries
        /// rustc scheduled in it are dropped.
        ScopeEnd(u32),
        /// Falling off the end of statement `s`: its statement scope pops (the temporaries of an
        /// expression statement, of a `let` initializer, and a statement's discarded value).
        StmtEnd(u32),
        /// Falling off the end of the THIR `Scope` expression `e` that a scope ENCLOSES and
        /// ends with: a match arm's scope around its body (the arm's bindings and temporaries),
        /// an `if`'s then-scope around its then-branch (an `if let`'s bindings). That scope pops
        /// right after `e`'s own.
        EnclosingEnd(u32),
        /// The start of the then branch of the `if` whose condition is expression `e`: the
        /// condition's scopes pop on its true edge (`then_else_break`).
        CondThen(u32),
        /// The start of the else branch (or the empty else) of that `if`: the condition's scopes
        /// pop on its false edge too.
        CondElse(u32),
    }

    /// Which MIR `Drop` terminator an edge's drops belong to. rustc builds ONE drop chain per
    /// scope fallthrough, one exit tree for every `return` of the function, one break tree and
    /// one continue tree per breakable scope (`Scopes::breakable_scopes`), and one terminator
    /// per drop-and-replace; a drop crossed by several edges of one class is one node of that
    /// class's tree, elaborated with the join of the edges' states.
    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
    pub enum ExitClass {
        /// The fallthrough of THIR block `b` (its remainder scopes).
        BlockFallthrough(u32),
        /// The fallthrough of the argument scope.
        ArgsFallthrough,
        ReturnTree,
        /// Break / continue tree of the breakable scope whose `region::Scope` has this
        /// `ItemLocalId` (and data discriminant, see [`crate::drops::label_key`]).
        BreakTree(u64),
        ContinueTree(u64),
        Replace(u32),
        /// The fallthrough of the THIR `Scope` expression `e`.
        ScopeFallthrough(u32),
        /// The fallthrough of statement `s`'s scope.
        StmtFallthrough(u32),
        /// The fallthrough of the scope that encloses and ends with expression `e`.
        EnclosingFallthrough(u32),
        /// The true edge out of the condition `e`.
        CondTrueEdge(u32),
        /// The false edge out of the condition `e`.
        CondFalseEdge(u32),
    }

    /// One exit edge: where it is placed, which drop tree it belongs to, and the drops it
    /// crosses in EMISSION order (innermost scope first, reverse schedule order in a scope).
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct Edge {
        pub key: ExitKey,
        pub class: ExitClass,
        pub drops: Vec<(usize, Style)>,
    }

    /// Why a plan cannot be placed statically.
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub enum Infeasible {
        /// A drop on one edge is maybe-initialized: placing it needs a runtime drop flag.
        ConditionalOnEdge,
        /// A drop on one edge is an open drop that drops part of a partially moved value
        /// (field drops, a variant switch): not placed.
        OpenOnEdge,
        /// The same exit was recorded with two different drop lists (a walker defect).
        KeyConflict,
    }

    /// Every reachable exit edge of a body.
    #[derive(Clone, Debug, Default, PartialEq, Eq)]
    pub struct Plan {
        pub edges: Vec<Edge>,
    }

    impl Plan {
        /// Feasible iff no single edge needs a flag and no exit is recorded twice differently.
        pub fn feasible(&self) -> Result<(), Infeasible> {
            let mut seen: BTreeMap<ExitKey, &Vec<(usize, Style)>> = BTreeMap::new();
            for e in &self.edges {
                if e.drops.iter().any(|(_, s)| *s == Style::Conditional) {
                    return Err(Infeasible::ConditionalOnEdge);
                }
                if e.drops.iter().any(|(_, s)| *s == Style::OpenLive) {
                    return Err(Infeasible::OpenOnEdge);
                }
                if let Some(prev) = seen.insert(e.key, &e.drops) {
                    if *prev != e.drops {
                        return Err(Infeasible::KeyConflict);
                    }
                }
            }
            Ok(())
        }

        /// The roots to drop when the hook for `key` fires, in emission order: the edge's
        /// `Static` drops. Empty for an exit with nothing to emit or not reachable.
        pub fn emission(&self, key: ExitKey) -> Vec<usize> {
            self.edges
                .iter()
                .find(|e| e.key == key)
                .map(|e| {
                    e.drops.iter().filter(|(_, s)| *s == Style::Static).map(|(r, _)| *r).collect()
                })
                .unwrap_or_default()
        }

        /// The exits whose hook MUST fire: those with at least one drop to emit.
        pub fn required(&self) -> BTreeSet<ExitKey> {
            self.edges
                .iter()
                .filter(|e| e.drops.iter().any(|(_, s)| *s == Style::Static))
                .map(|e| e.key)
                .collect()
        }

        /// Per (root, class): the join of the styles of every edge of that class that crosses
        /// the root. This is the style rustc's elaboration gives the class's one `Drop` node.
        pub fn joined(&self) -> BTreeMap<(usize, ExitClass), Style> {
            let mut out: BTreeMap<(usize, ExitClass), Style> = BTreeMap::new();
            for e in &self.edges {
                for (r, s) in &e.drops {
                    out.entry((*r, e.class)).and_modify(|have| *have = have.join(*s)).or_insert(*s);
                }
            }
            out
        }
    }
}

use kernel::{Edge, ExitClass, ExitKey, Init, Plan, State, Style};

/// A stable key for a breakable scope's `region::Scope` (its `ItemLocalId` and data kind).
pub(crate) fn label_key(scope: region::Scope) -> u64 {
    let data = match scope.data {
        region::ScopeData::Node => 0u64,
        region::ScopeData::CallSite => 1,
        region::ScopeData::Arguments => 2,
        region::ScopeData::Destruction => 3,
        region::ScopeData::IfThen => 4,
        region::ScopeData::IfThenRescope => 5,
        region::ScopeData::MatchGuard => 6,
        region::ScopeData::Remainder(first) => 16 + u64::from(first.as_u32()),
    };
    (u64::from(scope.local_id.as_u32()) << 32) | data
}

// =============================================================================================
// The claim the gate checks.
// =============================================================================================

/// Which local a drop is of, in terms both the producer and the MIR oracle can name: a
/// parameter by position, a `let` binding by the `ItemLocalId` of its `LocalVarId` (MIR keeps it
/// as `VarBindingForm::binding_hir_local_id`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum DropIdentity {
    Param(u32),
    Var(u32),
    /// A MIR local the producer has no name for (a temporary, a guard copy).
    Other,
}

/// The elaborated style the gate compares (no `Dead`: a dead drop is not a drop).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum LiveStyle {
    Static,
    Conditional,
    /// Drop elaboration expands it into per-field drops (a partially moved place). The producer
    /// never claims one in this cut.
    Open,
}

/// One live drop, as either side names it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct DropKey {
    pub identity: DropIdentity,
    /// `tcx.type_id_hash` of the dropped type.
    pub ty: u128,
    pub span: Span,
    pub style: LiveStyle,
}

// Upstream 1.101: `Span` no longer implements `Ord`; order spans by their
// byte positions (the previous derived order compared the same fields).
impl PartialOrd for DropKey {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for DropKey {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.identity
            .cmp(&other.identity)
            .then_with(|| self.ty.cmp(&other.ty))
            .then_with(|| self.span.lo().cmp(&other.span.lo()))
            .then_with(|| self.span.hi().cmp(&other.span.hi()))
            .then_with(|| self.style.cmp(&other.style))
    }
}

/// Trust (step 2 increment 4c): WHICH TYPE one emitted `Inst::Drop` drops, in terms the codegen
/// seam can read back. The node carries only its trust-ir type and pointer; the glue a drop
/// resolves to is a function of the RUSTC type. Every drop of one root goes through that root's
/// own slot (an entry-block `Alloca`, or a promoted binding's slot), so the pointer names the
/// root, and the root names its rustc type by `tcx.type_id_hash` (regions erased). The drop-glue
/// lane (`rustc_codegen_trust_cg`, `drop_glue_lane.rs`) recovers the type from the body's own
/// typeck results by that hash and refuses a drop whose pointer or hash it cannot match.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct DropSite {
    /// The `ValueId` the `Inst::Drop` names as its pointer.
    pub ptr: u32,
    /// `tcx.type_id_hash` of the dropped root's type.
    pub ty: u128,
    pub identity: DropIdentity,
}

/// What the producer claims about a body's drops, read by the effect-conservation gate.
#[derive(Clone, Debug, Default)]
pub struct DropClaim {
    /// Every live drop rustc's elaboration performs, one per (root, exit class).
    pub live: Vec<DropKey>,
    /// How many `Inst::Drop` nodes the producer emitted.
    pub emitted: usize,
    /// Whether each live drop's glue may run a destructor (parallel to `live`).
    pub destructor: Vec<bool>,
    /// Trust (step 2 increment 4c): one row per emitted `Inst::Drop`, in emission order.
    pub sites: Vec<DropSite>,
}

// =============================================================================================
// The planner: a structured abstract interpretation of THIR.
// =============================================================================================

/// How the program reaches a temporary's own bytes, which decides how its drop may be placed
/// (step 2 increment 4b residuals). Ordered: a stronger observation subsumes a weaker one.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum Observed {
    /// Only read in place (a field or element copied out, a discriminant tested) or not used at
    /// all: nothing outside the drop ever sees the temporary's address, so a drop through a
    /// fresh slot holding the same bytes is the drop rustc performs.
    No,
    /// Shared-borrowed (directly, or a place inside it not behind a deref): the drop must go
    /// through the object's proved home (`borrowed_temp_home`), unless the type is `Freeze` and
    /// its glue only releases memory (the root rule of 4b).
    Shared,
    /// Mutably (or raw-) borrowed: the program may have changed it through the borrow, so the
    /// drop must go through the object's proved home.
    Mut,
}

/// A temporary rustc's MIR building materializes (`as_temp`) and schedules a value drop for in
/// its temporary scope (`ScopeTree::temporary_scope`, or the statement scope for a statement's
/// discarded value).
#[derive(Clone, Debug)]
pub(crate) struct TempRoot {
    /// The THIR expressions whose lowered value IS the temporary's value: the operand as its
    /// consumer names it, and the same expression with each `Scope` wrapper peeled.
    pub(crate) exprs: Vec<ExprId>,
    pub(crate) observed: Observed,
    /// The `Borrow` expression that borrows the WHOLE temporary (`&f()`, an autoref
    /// receiver), when one does: its lowered value is the slot the temporary is materialized
    /// in, from which the placement proves where the object lives at the drop
    /// ([`borrowed_temp_home`]).
    pub(crate) borrow: Option<ExprId>,
}

/// One step of a move path below a root, as rustc's `MoveData` records it (`MoveSubPath`): the
/// steps a pattern binding or a field move takes (step 2 increment 4b residuals).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) enum Elem {
    Field(u32),
    Downcast(u32),
}

/// What kind of value a tracked root is.
#[derive(Clone, Debug)]
pub(crate) enum RootKind {
    /// A by-value parameter, a `let` binding, or (step 2 increment 4b residuals) a by-value
    /// pattern binding.
    Local,
    /// A temporary (step 2 increment 4b residuals).
    Temp(TempRoot),
    /// The old pointee of a drop-and-replace through a pointer (`*p = v` where `p` is a `&mut`
    /// or a raw pointer): one `Static` drop at the assignment, through the pointer the store
    /// goes through (rustc's `build_drop_and_replace`; the drop oracle's `LookupResult::Parent`
    /// arm keeps it unconditional).
    Pointee,
    /// Not a drop: the state slot of a move path below a root (a part of it some pattern
    /// binding or field move moves out; the planner's `children` names which). Its state is
    /// rustc's `MaybeInitializedPlaces` x `MaybeUninitializedPlaces` for that path; the root's
    /// drop reads it (open drops).
    Path,
}

/// A root's identity across fixpoint rounds (roots are re-declared every round).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum RootKey {
    Param(u32),
    Var(u32),
    /// A temporary, by the outermost expression it is materialized from.
    Temp(u32),
}

/// A tracked root.
#[derive(Clone, Debug)]
pub(crate) struct Root<'tcx> {
    pub(crate) identity: DropIdentity,
    pub(crate) var: Option<LocalVarId>,
    /// `thir.params` index, for a parameter.
    pub(crate) param: Option<usize>,
    pub(crate) ty: RustcTy<'tcx>,
    /// The drop's span: the end point of the scheduling scope's span (the assignment's
    /// left-hand side for a `Pointee`).
    pub(crate) span: Span,
    shared_borrowed: bool,
    pub(crate) kind: RootKind,
}

/// A planned body: its roots and every reachable exit edge.
#[derive(Clone, Debug)]
pub(crate) struct DropPlan<'tcx> {
    pub(crate) roots: Vec<Root<'tcx>>,
    pub(crate) plan: Plan,
    /// Drop-and-replace spans, by `Replace` key (the left-hand side's span).
    replace_spans: BTreeMap<u32, Span>,
    /// Per root: may its glue run a destructor beyond releasing memory.
    destructor: Vec<bool>,
    /// Per root: is its type `Freeze` (no interior mutability reachable without a pointer).
    freeze: Vec<bool>,
    /// Per (root, exit class): the style rustc's elaboration gives the class's one `Drop` node
    /// — computed, as the drop oracle computes it, from the JOIN of the states the class's edges
    /// carry (for a partially moved root the join of the per-edge styles is not that style).
    /// A dead node is absent.
    class_styles: BTreeMap<(usize, ExitClass), LiveStyle>,
}

impl<'tcx> DropPlan<'tcx> {
    /// The span a drop of `root` on the edge `key` carries.
    fn span_of(&self, root: usize, key: ExitKey) -> Span {
        match key {
            ExitKey::Replace(e) => {
                self.replace_spans.get(&e).copied().unwrap_or(self.roots[root].span)
            }
            _ => self.roots[root].span,
        }
    }

    /// The claim, with the emitted count filled in by the caller.
    pub(crate) fn claim(&self, tcx: TyCtxt<'tcx>, emitted: usize) -> DropClaim {
        let mut live = Vec::new();
        let mut destructor = Vec::new();
        // The span of a class: a Replace class carries the assignment's span.
        for (&(root, class), &style) in &self.class_styles {
            let span = match class {
                ExitClass::Replace(e) => self.span_of(root, ExitKey::Replace(e)),
                _ => self.roots[root].span,
            };
            live.push(DropKey {
                identity: self.roots[root].identity,
                ty: tcx.type_id_hash(self.roots[root].ty).as_u128(),
                span,
                style,
            });
            destructor.push(self.destructor[root]);
        }
        DropClaim { live, emitted, destructor, sites: Vec::new() }
    }

    /// Every THIR expression whose lowered value is a temporary root's value, with that root
    /// (the recording hook in `LowerCx::lower_expr` reads it).
    pub(crate) fn temp_exprs(&self) -> BTreeMap<u32, usize> {
        let mut out = BTreeMap::new();
        for (r, root) in self.roots.iter().enumerate() {
            if let RootKind::Temp(t) = &root.kind {
                for e in &t.exprs {
                    out.insert(e.as_u32(), r);
                }
            }
        }
        out
    }

    /// Every `Borrow` expression that borrows a whole temporary, with that temporary's root.
    pub(crate) fn temp_borrows(&self) -> BTreeMap<u32, usize> {
        let mut out = BTreeMap::new();
        for (r, root) in self.roots.iter().enumerate() {
            if let RootKind::Temp(TempRoot { borrow: Some(e), .. }) = &root.kind {
                out.insert(e.as_u32(), r);
            }
        }
        out
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Ctx {
    /// The value is consumed: operand or destination position. A non-`Copy` place here moves.
    Value,
    /// The expression is used as a place (borrowed, projected, scrutinized, assigned to).
    Place,
    /// A statement expression: its value is ignored.
    Discard,
}

#[derive(Clone, Debug)]
enum Frame {
    Args(Vec<usize>),
    Block {
        roots: Vec<usize>,
    },
    /// A breakable scope (`loop` or labelled block) with its label.
    Breakable {
        label: region::Scope,
        is_loop: bool,
    },
    /// Trust (step 2 increment 4b residuals): a region scope whose drops are temporaries or
    /// pattern bindings — a THIR `Scope` expression's `Node` scope, a statement's scope, a
    /// block's own `Node` scope, a match arm's scope, an `if`'s then-scope.
    Temps {
        scope: region::Scope,
        roots: Vec<usize>,
        /// A scope of a CONDITION (an `if`'s, a guard's, a `&&`/`||` left operand's), lowered by
        /// `then_else_break`: its drops are placed on BOTH branch edges, which no lowering hook
        /// places, so a temporary scheduled here is refused by name.
        cond: bool,
    },
}

/// The base a place expression is projected from.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Base {
    /// A tracked root (a needs-drop parameter or binding).
    Root(usize),
    /// A temporary the place's evaluation materialized (an rvalue in place position).
    Temp(usize),
    /// Anything else: an untracked local, an upvar, a temporary that needs no drop, a static.
    Untracked,
}

#[derive(Clone, Copy, Debug)]
struct PlaceInfo {
    base: Base,
    /// No projection between the base and the place.
    whole: bool,
    /// A `Deref` lies between the base and the place: the place is behind a pointer the base
    /// holds, so a borrow of the place does not observe the base's own address.
    deref: bool,
}

impl PlaceInfo {
    fn untracked() -> PlaceInfo {
        PlaceInfo { base: Base::Untracked, whole: true, deref: false }
    }
}

/// One binding of a pattern, with the move path below the scrutinee it binds.
struct PatBinding<'tcx> {
    var: LocalVarId,
    mode: rustc_ast::ByRef,
    ty: RustcTy<'tcx>,
    proj: Vec<Elem>,
    /// A construct between the scrutinee and the binding whose moves this cut does not model.
    through: Option<&'static str>,
}

/// The bindings of `pat` in pattern order (rustc binds and schedules them in that order), each
/// with its projection below the scrutinee.
fn pattern_bindings<'tcx>(
    pat: &Pat<'tcx>,
    proj: &[Elem],
    through: Option<&'static str>,
    out: &mut Vec<PatBinding<'tcx>>,
) {
    match &pat.kind {
        PatKind::Binding { var, mode, ty, subpattern, .. } => {
            let sub = subpattern.as_ref().map(|_| "a by-value binding with a subpattern");
            out.push(PatBinding {
                var: *var,
                mode: mode.0,
                ty: *ty,
                proj: proj.to_vec(),
                through: through.or(sub),
            });
            if let Some(sp) = subpattern {
                pattern_bindings(sp, proj, through.or(sub), out);
            }
        }
        PatKind::Variant { variant_index, subpatterns, .. } => {
            for fp in subpatterns {
                let mut p = proj.to_vec();
                p.push(Elem::Downcast(variant_index.as_u32()));
                p.push(Elem::Field(fp.field.as_u32()));
                pattern_bindings(&fp.pattern, &p, through, out);
            }
        }
        PatKind::Leaf { subpatterns } => {
            let enum_leaf = matches!(pat.ty.kind(), ty::Adt(adt, _) if adt.is_enum());
            for fp in subpatterns {
                let mut p = proj.to_vec();
                p.push(Elem::Field(fp.field.as_u32()));
                let t = if enum_leaf {
                    through.or(Some("a single-variant enum pattern"))
                } else {
                    through
                };
                pattern_bindings(&fp.pattern, &p, t, out);
            }
        }
        PatKind::Deref { subpattern, .. } | PatKind::DerefPattern { subpattern, .. } => {
            pattern_bindings(subpattern, proj, through.or(Some("a deref pattern")), out);
        }
        PatKind::Guard { subpattern, .. } => {
            pattern_bindings(subpattern, proj, through.or(Some("a guard pattern")), out);
        }
        PatKind::Slice { prefix, slice, suffix } | PatKind::Array { prefix, slice, suffix } => {
            for p in prefix.iter().chain(slice.iter().map(|b| &**b)).chain(suffix.iter()) {
                pattern_bindings(p, proj, through.or(Some("a slice or array pattern")), out);
            }
        }
        PatKind::Or { pats } => {
            for p in pats.iter() {
                pattern_bindings(p, proj, through.or(Some("an or-pattern")), out);
            }
        }
        PatKind::Missing
        | PatKind::Wild
        | PatKind::Constant { .. }
        | PatKind::Range(_)
        | PatKind::Never
        | PatKind::Error(_) => {}
    }
}

/// The variant a pattern tests at its top (an enum `Variant` pattern of a multi-variant enum).
fn top_variant(pat: &Pat<'_>) -> Option<u32> {
    match &pat.kind {
        PatKind::Variant { adt_def, variant_index, .. } if adt_def.variants().len() > 1 => {
            Some(variant_index.as_u32())
        }
        _ => None,
    }
}

/// A pattern that matches every value without a test (`_`, `x`, a struct/tuple of those).
fn irrefutable(pat: &Pat<'_>) -> bool {
    match &pat.kind {
        PatKind::Missing | PatKind::Wild => true,
        PatKind::Binding { subpattern, .. } => subpattern.as_ref().is_none_or(|p| irrefutable(p)),
        PatKind::Leaf { subpatterns } => subpatterns.iter().all(|fp| irrefutable(&fp.pattern)),
        PatKind::Variant { adt_def, subpatterns, .. } => {
            adt_def.variants().len() == 1 && subpatterns.iter().all(|fp| irrefutable(&fp.pattern))
        }
        _ => false,
    }
}

/// A variant pattern whose fields test nothing more (`Some(x)`, `E::A(_, y)`): the arm is
/// entered exactly from the discriminant switch's edge for that variant.
fn variant_test_only(pat: &Pat<'_>) -> bool {
    match &pat.kind {
        PatKind::Variant { subpatterns, .. } => {
            top_variant(pat).is_some() && subpatterns.iter().all(|fp| irrefutable(&fp.pattern))
        }
        _ => false,
    }
}

/// Trust (4b residuals review, 2026-10-08): the variants the arms before arm `arm` test at the
/// top (`tops[i]` is arm `i`'s [`top_variant`]) — the ones inactive on the discriminant switch's
/// otherwise edge into a catch-all arm `arm`. Only the arms BEFORE it: an arm after a catch-all
/// is unreachable, and counting its variant would kill a payload that still reaches the
/// catch-all (`match o { None => 0, _ => 1, Some(g) => .. }`: on `_`, `o` may be `Some(g)` and
/// rustc drops it). PURE.
pub(crate) fn variants_tested_before(
    tops: &[Option<u32>],
    arm: usize,
) -> std::collections::BTreeSet<u32> {
    tops[..arm.min(tops.len())].iter().flatten().copied().collect()
}

/// The fixpoint bound: each root can only move towards `Maybe`, so a loop head stabilises in a
/// couple of rounds per root; this bound is generous and refuses rather than loop forever.
const FIXPOINT_ROUNDS: usize = 64;

/// One exit edge as the walk records it: its drops' roots in emission order and the state it
/// carries. Styles are computed once every move path of the body is known (a path a later
/// statement moves out of exists, in rustc's `MoveData`, at every point of the body).
struct PendingEdge {
    key: ExitKey,
    class: ExitClass,
    roots: Vec<usize>,
    state: State,
}

struct Planner<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    thir: &'a Thir<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    scope_tree: &'tcx region::ScopeTree,
    parent_module: rustc_span::def_id::LocalModId,
    roots: Vec<Root<'tcx>>,
    var_root: std::collections::HashMap<LocalVarId, usize>,
    frames: Vec<Frame>,
    state: State,
    pending: Vec<PendingEdge>,
    replace_spans: BTreeMap<u32, Span>,
    /// Per loop (its label key): the back-edge state of the previous round, and of this one.
    back_prev: BTreeMap<u64, State>,
    back_cur: BTreeMap<u64, State>,
    /// Per breakable scope: the join of the states its `break`s carry, this round.
    breaks: BTreeMap<u64, State>,
    /// The `let` statements whose initializer is being evaluated, innermost last: each one's
    /// remainder scope (where a temporary its initializer EXTENDS is scheduled) and the frame of
    /// the block it belongs to.
    remainders: Vec<(region::Scope, usize)>,
    /// Every move path below a root that some move of the body creates (rustc's `MoveData`
    /// creates them for the whole body), kept across rounds; a round that discovers a new one
    /// is redone with it declared from the root's declaration on.
    known_paths: BTreeMap<RootKey, std::collections::BTreeSet<Vec<Elem>>>,
    new_paths: bool,
    /// This round: each root's path slots.
    children: BTreeMap<usize, Vec<(Vec<Elem>, usize)>>,
}

type PResult<T = ()> = Result<T, &'static str>;

impl<'a, 'tcx> Planner<'a, 'tcx> {
    /// The THIR, with its own lifetime: a reference into it does not borrow `self`.
    fn thir(&self) -> &'a Thir<'tcx> {
        self.thir
    }

    fn may_need_drop(&self, ty: RustcTy<'tcx>) -> bool {
        crate::cycle_safe_needs_drop(self.tcx, self.typing_env, ty)
    }

    /// Through the producer's reveal funnel (`lib.rs`): inside `mir_built` no type query may
    /// reveal an opaque.
    fn is_copy(&self, ty: RustcTy<'tcx>) -> bool {
        crate::cycle_safe_is_copy(self.tcx, self.typing_env, ty)
    }

    fn n(&self) -> usize {
        self.roots.len()
    }

    fn unreachable(&mut self) {
        self.state = State::unreachable(self.n());
    }

    /// A type the planner may track: concrete, opaque-free, layout-queryable.
    fn trackable(&self, ty: RustcTy<'tcx>) -> PResult {
        if ty.has_non_region_param() || ty.has_opaque_types() || ty.has_aliases() {
            return Err("generic, opaque or alias-typed value needing drop");
        }
        if !crate::layout_query_is_reentrant_safe(ty) {
            return Err("value needing drop of an unqueryable type");
        }
        if ty.has_coroutines() {
            return Err("coroutine value needing drop");
        }
        Ok(())
    }

    fn scope_end(&self, scope: region::Scope) -> Span {
        let span = scope.span(self.tcx, self.scope_tree);
        self.tcx.sess.source_map().end_point(span)
    }

    fn add_root(&mut self, root: Root<'tcx>) -> usize {
        let i = self.roots.len();
        if let Some(var) = root.var {
            self.var_root.insert(var, i);
        }
        self.roots.push(root);
        self.state.grow(self.roots.len());
        for s in self.back_prev.values_mut().chain(self.back_cur.values_mut()) {
            s.grow(i + 1);
        }
        for s in self.breaks.values_mut() {
            s.grow(i + 1);
        }
        i
    }

    fn root_key(&self, r: usize) -> Option<RootKey> {
        match (&self.roots[r].kind, self.roots[r].identity) {
            (RootKind::Local, DropIdentity::Param(i)) => Some(RootKey::Param(i)),
            (RootKind::Local, DropIdentity::Var(v)) => Some(RootKey::Var(v)),
            (RootKind::Temp(t), _) => t.exprs.first().map(|e| RootKey::Temp(e.as_u32())),
            _ => None,
        }
    }

    /// A root that can be moved out of: declared with a slot for every move path below it the
    /// body creates (from earlier rounds), right after it.
    fn new_root(&mut self, root: Root<'tcx>) -> usize {
        let r = self.add_root(root);
        if let Some(key) = self.root_key(r) {
            let paths: Vec<Vec<Elem>> =
                self.known_paths.get(&key).map(|s| s.iter().cloned().collect()).unwrap_or_default();
            for proj in paths {
                let (ty, span) = (self.roots[r].ty, self.roots[r].span);
                let slot = self.add_root(Root {
                    identity: DropIdentity::Other,
                    var: None,
                    param: None,
                    ty,
                    span,
                    shared_borrowed: false,
                    kind: RootKind::Path,
                });
                self.children.entry(r).or_default().push((proj, slot));
            }
        }
        r
    }

    /// The state slot of the path `proj` below root `r` (`r` itself for `[]`).
    fn slot(&self, r: usize, proj: &[Elem]) -> Option<usize> {
        if proj.is_empty() {
            return Some(r);
        }
        self.children.get(&r)?.iter().find(|(p, _)| p.as_slice() == proj).map(|(_, s)| *s)
    }

    /// The slots of the path `proj` below `r` and of every path below it.
    fn subtree(&self, r: usize, proj: &[Elem]) -> Vec<usize> {
        let mut out = Vec::new();
        if proj.is_empty() {
            out.push(r);
        }
        if let Some(cs) = self.children.get(&r) {
            out.extend(cs.iter().filter(|(p, _)| p.starts_with(proj)).map(|(_, s)| *s));
        }
        out
    }

    /// A whole-root event (an initialization, a whole move, a drop-and-replace): the root and
    /// every path below it (rustc's `on_all_children_bits`).
    fn set_root(&mut self, r: usize, init: Init) {
        for s in self.subtree(r, &[]) {
            self.state.set(s, init);
        }
    }

    /// A move out of the path `proj` below root `r` (`move_path_for` creates every prefix):
    /// the path and everything below it are uninitialized. A path the body has not declared yet
    /// redoes the round.
    fn move_out(&mut self, r: usize, proj: &[Elem]) -> PResult {
        if mutation() == Some("ignore-moves") {
            return Ok(());
        }
        if proj.is_empty() {
            self.set_root(r, Init::Uninit);
            return Ok(());
        }
        let Some(key) = self.root_key(r) else {
            return Err("partial move out of a value the planner does not track");
        };
        let known = self.known_paths.entry(key).or_default();
        for i in 1..=proj.len() {
            if known.insert(proj[..i].to_vec()) {
                self.new_paths = true;
            }
        }
        for s in self.subtree(r, proj) {
            self.state.set(s, Init::Uninit);
        }
        Ok(())
    }

    /// A switch edge into variant-tested code: the paths below `base` (of root `r`) under every
    /// variant `keep` rejects are inactive — uninitialized (`MaybeInitializedPlaces`' and
    /// `MaybeUninitializedPlaces`' switch-edge effects, as the drop oracle configures them).
    fn kill_variants(&mut self, r: usize, base: &[Elem], keep: &dyn Fn(u32) -> bool) {
        let n = base.len();
        let slots: Vec<usize> = self
            .children
            .get(&r)
            .map(|cs| {
                cs.iter()
                    .filter(|(p, _)| {
                        p.len() > n
                            && p.starts_with(base)
                            && matches!(p[n], Elem::Downcast(w) if !keep(w))
                    })
                    .map(|(_, s)| *s)
                    .collect()
            })
            .unwrap_or_default();
        for s in slots {
            self.state.set(s, Init::Uninit);
        }
    }

    // ---- styles: the drop oracle's rules, on the planner's states ----

    /// `(maybe_init, maybe_uninit, more than one path)` over the path `proj` of `r` and all
    /// paths below it (`drop_style`'s `Deep` mode).
    fn deep(&self, r: usize, proj: &[Elem], st: &State) -> (bool, bool, bool) {
        let slots = self.subtree(r, proj);
        let init = slots.iter().any(|s| st.get(*s) != Init::Uninit);
        let uninit = slots.iter().any(|s| st.get(*s) != Init::Init);
        (init, uninit, slots.len() > 1)
    }

    fn maybe_init(&self, r: usize, proj: &[Elem], st: &State) -> bool {
        self.slot(r, proj).is_some_and(|s| st.get(s) != Init::Uninit)
    }

    /// The fields of a struct (no destructor, not a box), tuple or closure, or `None`.
    fn open_fields(&self, ty: RustcTy<'tcx>) -> Option<Vec<RustcTy<'tcx>>> {
        match ty.kind() {
            ty::Adt(adt, args)
                if adt.is_struct() && !adt.is_box() && adt.destructor(self.tcx).is_none() =>
            {
                Some(
                    adt.non_enum_variant()
                        .fields
                        .iter()
                        .map(|f| f.ty(self.tcx, *args).skip_normalization())
                        .collect(),
                )
            }
            ty::Tuple(tys) => Some(tys.iter().collect()),
            ty::Closure(_, args) => Some(args.as_closure().upvar_tys().iter().collect()),
            _ => None,
        }
    }

    /// The drop oracle's `open_drop_is_live` on the planner's state: does an open drop of the
    /// path `proj` of `r` (of type `ty`) drop anything — a struct, tuple or closure expanded
    /// per field; anything else (an enum, a box, an array) conservatively live.
    fn oracle_open_live(
        &self,
        r: usize,
        proj: &[Elem],
        ty: RustcTy<'tcx>,
        st: &State,
        d: usize,
    ) -> bool {
        if d > 16 {
            return true;
        }
        let Some(fields) = self.open_fields(ty) else { return true };
        let parent_init = self.maybe_init(r, proj, st);
        for (i, fty) in fields.into_iter().enumerate() {
            let mut cp = proj.to_vec();
            cp.push(Elem::Field(i as u32));
            if self.slot(r, &cp).is_some() {
                match self.deep(r, &cp, st) {
                    (false, _, _) => {}
                    (true, true, true) => {
                        if self.oracle_open_live(r, &cp, fty, st, d + 1) {
                            return true;
                        }
                    }
                    _ => return true,
                }
            } else if parent_init && self.may_need_drop(fty) {
                return true;
            }
        }
        false
    }

    /// The style the drop oracle gives the one `Drop` node of `r` reached in state `st` (the
    /// join of a class's edges), or `None` for a dead node.
    fn class_style(&self, r: usize, st: &State) -> Option<LiveStyle> {
        match self.deep(r, &[], st) {
            (false, _, _) => None,
            (true, false, _) => Some(LiveStyle::Static),
            (true, true, false) => Some(LiveStyle::Conditional),
            (true, true, true) => {
                self.oracle_open_live(r, &[], self.roots[r].ty, st, 0).then_some(LiveStyle::Open)
            }
        }
    }

    /// What rustc's elaboration of an open drop (`open_drop_for_adt` /
    /// `open_drop_for_multivariant` / `drop_ladder`) of the path `proj` of `r` drops on an edge
    /// carrying `st`: `true` when nothing — every needs-drop field moved out (its path dead),
    /// every variant not moved out of free of needs-drop fields. A box, an array, a type with a
    /// destructor, or anything left to drop answers `false`.
    fn open_drops_nothing(
        &self,
        r: usize,
        proj: &[Elem],
        ty: RustcTy<'tcx>,
        st: &State,
        d: usize,
    ) -> bool {
        if d > 16 {
            return false;
        }
        // One field, under the parent path `parent` (its own state decides a field with no path).
        let field_dead = |this: &Self, parent: &[Elem], fi: usize, fty: RustcTy<'tcx>| -> bool {
            let mut cp = parent.to_vec();
            cp.push(Elem::Field(fi as u32));
            if this.slot(r, &cp).is_some() {
                match this.deep(r, &cp, st) {
                    (false, _, _) => true,
                    (true, true, true) => this.open_drops_nothing(r, &cp, fty, st, d + 1),
                    _ => false,
                }
            } else {
                !this.may_need_drop(fty) || !this.maybe_init(r, parent, st)
            }
        };
        match ty.kind() {
            ty::Adt(adt, args) if adt.is_enum() && adt.destructor(self.tcx).is_none() => {
                for (vi, variant) in adt.variants().iter_enumerated() {
                    let mut dp = proj.to_vec();
                    dp.push(Elem::Downcast(vi.as_u32()));
                    let ftys: Vec<RustcTy<'tcx>> = variant
                        .fields
                        .iter()
                        .map(|f| f.ty(self.tcx, *args).skip_normalization())
                        .collect();
                    if self.slot(r, &dp).is_some() {
                        for (fi, fty) in ftys.into_iter().enumerate() {
                            if !field_dead(self, &dp, fi, fty) {
                                return false;
                            }
                        }
                    } else if ftys.iter().any(|t| self.may_need_drop(*t)) {
                        // rustc drops the whole value in this variant's arm (`drop_block`).
                        return false;
                    }
                }
                true
            }
            _ => match self.open_fields(ty) {
                Some(fields) => {
                    fields.into_iter().enumerate().all(|(fi, fty)| field_dead(self, proj, fi, fty))
                }
                None => false,
            },
        }
    }

    /// The style of `r`'s drop on one edge carrying `st`.
    fn edge_style(&self, r: usize, st: &State) -> Style {
        match self.deep(r, &[], st) {
            (false, _, _) => Style::Dead,
            (true, false, _) => Style::Static,
            (true, true, false) => Style::Conditional,
            (true, true, true) => {
                if self.open_drops_nothing(r, &[], self.roots[r].ty, st, 0) {
                    Style::Open
                } else {
                    Style::OpenLive
                }
            }
        }
    }

    // ---- places ----

    /// Peel the value-transparent wrappers rustc's MIR building looks through.
    fn peel(&self, mut e: ExprId) -> ExprId {
        loop {
            match &self.thir().exprs[e].kind {
                ExprKind::Scope { value, .. } => e = *value,
                _ => return e,
            }
        }
    }

    /// `e` and each expression under its `Scope` wrappers, outermost first.
    fn scope_chain(&self, e: ExprId) -> Vec<ExprId> {
        let mut chain = vec![e];
        let mut cur = e;
        while let ExprKind::Scope { value, .. } = &self.thir().exprs[cur].kind {
            cur = *value;
            chain.push(cur);
        }
        chain
    }

    /// The expressions whose lowered value is `e`'s value: `e` and each expression under its
    /// `Scope` and `Use` wrappers (a lowering lane may peel either before it lowers).
    fn value_chain(&self, e: ExprId) -> Vec<ExprId> {
        let mut chain = vec![e];
        let mut cur = e;
        loop {
            match &self.thir().exprs[cur].kind {
                ExprKind::Scope { value, .. } => cur = *value,
                ExprKind::ValueExpr { source } => cur = *source,
                _ => return chain,
            }
            chain.push(cur);
        }
    }

    fn is_place_expr(&self, e: ExprId) -> bool {
        matches!(
            self.thir().exprs[self.peel(e)].kind,
            ExprKind::Field { .. }
                | ExprKind::Deref { .. }
                | ExprKind::Index { .. }
                | ExprKind::UpvarRef { .. }
                | ExprKind::VarRef { .. }
                | ExprKind::PlaceTypeAscription { .. }
                | ExprKind::ValueTypeAscription { .. }
                | ExprKind::PlaceUnwrapUnsafeBinder { .. }
                | ExprKind::ValueUnwrapUnsafeBinder { .. }
        )
    }

    /// The tracked root a place expression is based at, and whether it is the WHOLE root (no
    /// projection), read syntactically (no evaluation, no temporary). Looks through field,
    /// deref and index projections and ascriptions.
    fn place_base(&self, e: ExprId) -> Option<(usize, bool)> {
        let mut cur = self.peel(e);
        let mut whole = true;
        loop {
            match &self.thir().exprs[cur].kind {
                ExprKind::VarRef { id } => return self.var_root.get(id).map(|r| (*r, whole)),
                ExprKind::Field { lhs, .. } => {
                    whole = false;
                    cur = self.peel(*lhs);
                }
                ExprKind::Deref { arg } => {
                    whole = false;
                    cur = self.peel(*arg);
                }
                ExprKind::Index { lhs, .. } => {
                    whole = false;
                    cur = self.peel(*lhs);
                }
                ExprKind::PlaceTypeAscription { source, .. }
                | ExprKind::ValueTypeAscription { source, .. } => cur = self.peel(*source),
                _ => return None,
            }
        }
    }

    /// The field projections from the base of a place expression to the place — a chain of
    /// `Field`s only (a deref, an index or an ascription between answers `None`) — as move
    /// path steps (a field of an enum-typed base is a downcast then the field).
    fn field_proj(&self, e: ExprId) -> Option<Vec<Elem>> {
        let mut cur = self.peel(e);
        let mut rev = Vec::new();
        loop {
            match &self.thir().exprs[cur].kind {
                ExprKind::Field { lhs, variant_index, name } => {
                    rev.push(Elem::Field(name.as_u32()));
                    if matches!(self.thir().exprs[*lhs].ty.kind(), ty::Adt(adt, _) if adt.is_enum())
                    {
                        rev.push(Elem::Downcast(variant_index.as_u32()));
                    }
                    cur = self.peel(*lhs);
                }
                ExprKind::Deref { .. }
                | ExprKind::Index { .. }
                | ExprKind::PlaceTypeAscription { .. }
                | ExprKind::ValueTypeAscription { .. }
                | ExprKind::PlaceUnwrapUnsafeBinder { .. }
                | ExprKind::ValueUnwrapUnsafeBinder { .. } => return None,
                _ => {
                    rev.reverse();
                    return Some(rev);
                }
            }
        }
    }

    /// The scrutinee as a move path base: a tracked root or a temporary with the field
    /// projections down to the scrutinee place. `None` for anything a by-value binding cannot
    /// move out of here.
    fn scrut_path(&self, scrut: ExprId, info: PlaceInfo) -> Option<(usize, Vec<Elem>)> {
        let r = match info.base {
            Base::Root(r) | Base::Temp(r) => r,
            Base::Untracked => return None,
        };
        if info.deref {
            return None;
        }
        if !self.is_place_expr(scrut) {
            return Some((r, Vec::new()));
        }
        self.field_proj(scrut).map(|p| (r, p))
    }

    /// Trust (4b residuals review, 2026-10-08): an assignment's left-hand side. A write into a
    /// needs-drop temporary's own bytes (`f().0 = v`, `f().0 += 1`; not behind a deref) changes
    /// the value its drop must see, while a temporary nothing borrows is dropped through a fresh
    /// slot holding the value from BEFORE the write. Refused by name; a lowering lane that one
    /// day admits such an assignment keeps the body's drops elided rather than drop stale bytes.
    fn write_into(info: PlaceInfo) -> PResult {
        match info.base {
            Base::Temp(_) if !info.deref => Err("a write into part of a temporary"),
            _ => Ok(()),
        }
    }

    /// Record that the program reaches temporary `r`'s own bytes as `o`.
    fn observe(&mut self, r: usize, o: Observed) {
        if let RootKind::Temp(t) = &mut self.roots[r].kind {
            t.observed = t.observed.max(o);
        }
    }

    /// The frame a temporary whose drop rustc schedules in `scope` is scheduled in: an open
    /// `Temps` frame of that scope, or — a temporary EXTENDED to a `let`'s remainder scope
    /// (`let x = &f();`) — the block frame of the `let` whose initializer is being evaluated.
    /// Any other scope is not modelled, and the body is refused naming it.
    fn temp_frame(&self, scope: region::Scope) -> PResult<usize> {
        match scope.data {
            // An edition-2024 `if let`'s temporaries are dropped on the edge into the else
            // branch as well, which no lowering hook places.
            region::ScopeData::IfThenRescope => {
                return Err("temporary in an if-let scrutinee's rescoped scope (edition 2024)");
            }
            region::ScopeData::MatchGuard => return Err("temporary in a match guard's scope"),
            _ => {}
        }
        for (i, f) in self.frames.iter().enumerate().rev() {
            if let Frame::Temps { scope: s, cond, .. } = f {
                if *s == scope {
                    if *cond {
                        return Err(
                            "temporary in a condition's scope (dropped on both branch edges)",
                        );
                    }
                    return Ok(i);
                }
            }
        }
        match scope.data {
            region::ScopeData::Remainder(_) => self
                .remainders
                .iter()
                .rev()
                .find(|(s, _)| *s == scope)
                .map(|(_, frame)| *frame)
                .ok_or("temporary extended to a scope the planner does not model"),
            _ => Err("temporary scope the planner does not model"),
        }
    }

    fn push_root_to(&mut self, frame: usize, r: usize) {
        match &mut self.frames[frame] {
            Frame::Temps { roots, .. } | Frame::Block { roots } => roots.push(r),
            Frame::Args(roots) => roots.push(r),
            Frame::Breakable { .. } => {}
        }
    }

    /// Schedule a temporary of type `ty` in frame `frame` (rustc's `schedule_drop_value` in
    /// `scope`, right after the temporary is written), initialized.
    fn add_temp(
        &mut self,
        frame: usize,
        scope: region::Scope,
        exprs: Vec<ExprId>,
        ty: RustcTy<'tcx>,
        observed: Observed,
    ) -> usize {
        let (mut frame, mut scope) = (frame, scope);
        if mutation() == Some("temp-outer-scope") {
            // TEST-ONLY: the next enclosing scope that holds temporaries.
            if let Some((i, s)) =
                self.frames[..frame].iter().enumerate().rev().find_map(|(i, f)| {
                    if let Frame::Temps { scope: s, cond: false, .. } = f {
                        Some((i, *s))
                    } else {
                        None
                    }
                })
            {
                frame = i;
                scope = s;
            }
        }
        let span = self.scope_end(scope);
        let r = self.new_root(Root {
            identity: DropIdentity::Other,
            var: None,
            param: None,
            ty,
            span,
            shared_borrowed: false,
            kind: RootKind::Temp(TempRoot { exprs, observed, borrow: None }),
        });
        self.set_root(r, Init::Init);
        self.push_root_to(frame, r);
        r
    }

    /// An rvalue in place position (`as_place` of a non-place, `lower_scrutinee`): rustc
    /// evaluates it into a temporary (`as_temp`) and schedules the temporary's drop in its
    /// temporary scope (`temporary_scope(expr.temp_scope_id)`, the `Scope`-peeled expression's —
    /// `expr_as_place` recurses through `Scope` first). `None` when its type needs no drop.
    fn temp_of(&mut self, e: ExprId, observed: Observed) -> PResult<Option<usize>> {
        let chain = self.scope_chain(e);
        let inner = *chain.last().unwrap_or(&e);
        let ty = self.thir().exprs[inner].ty;
        self.expr(e, Ctx::Value)?;
        if !self.may_need_drop(ty) {
            return Ok(None);
        }
        self.trackable(ty)?;
        let lifetime = self.scope_tree.temporary_scope(self.thir().exprs[inner].temp_scope_id);
        let Some(scope) = lifetime.temp_lifetime else {
            return Err("temporary with no drop scope");
        };
        let frame = self.temp_frame(scope)?;
        let exprs = self.value_chain(e);
        Ok(Some(self.add_temp(frame, scope, exprs, ty, observed)))
    }

    /// [`Self::temp_of`] as a place.
    fn rvalue_place(&mut self, e: ExprId) -> PResult<PlaceInfo> {
        let t = self.temp_of(e, Observed::No)?;
        Ok(PlaceInfo { base: t.map_or(Base::Untracked, Base::Temp), whole: true, deref: false })
    }

    fn place_or_temp(&mut self, e: ExprId) -> PResult<PlaceInfo> {
        if self.is_place_expr(e) { self.place_info(e) } else { self.rvalue_place(e) }
    }

    /// Evaluate a place expression's sub-expressions in MIR building's order (`expr_as_place`):
    /// index operands, and every rvalue base, which becomes a temporary. Returns the base.
    fn place_info(&mut self, e: ExprId) -> PResult<PlaceInfo> {
        let p = self.peel(e);
        match &self.thir().exprs[p].kind {
            ExprKind::VarRef { id } => Ok(PlaceInfo {
                base: self.var_root.get(id).map_or(Base::Untracked, |r| Base::Root(*r)),
                whole: true,
                deref: false,
            }),
            ExprKind::UpvarRef { .. } => {
                if self.may_need_drop(self.thir().exprs[p].ty) {
                    // An upvar of a needs-drop type: a by-value closure environment.
                    return Err("closure environment value needing drop");
                }
                Ok(PlaceInfo::untracked())
            }
            ExprKind::Field { lhs, .. } => {
                let mut i = self.place_or_temp(*lhs)?;
                i.whole = false;
                Ok(i)
            }
            ExprKind::Deref { arg } => {
                let mut i = self.place_or_temp(*arg)?;
                i.whole = false;
                i.deref = true;
                Ok(i)
            }
            ExprKind::Index { lhs, index } => {
                let (l, ix) = (*lhs, *index);
                let mut i = self.place_or_temp(l)?;
                self.expr(ix, Ctx::Value)?;
                i.whole = false;
                Ok(i)
            }
            ExprKind::PlaceTypeAscription { source, .. }
            | ExprKind::ValueTypeAscription { source, .. } => self.place_or_temp(*source),
            ExprKind::PlaceUnwrapUnsafeBinder { .. } | ExprKind::ValueUnwrapUnsafeBinder { .. } => {
                Err("unsafe binder place")
            }
            _ => self.rvalue_place(e),
        }
    }

    /// A place expression evaluated in `ctx`.
    fn place(&mut self, e: ExprId, ctx: Ctx) -> PResult<PlaceInfo> {
        let ty = self.thir().exprs[e].ty;
        let info = self.place_info(e)?;
        match ctx {
            Ctx::Place => Ok(info),
            Ctx::Value | Ctx::Discard => {
                if self.is_copy(ty) {
                    return Ok(info);
                }
                if ctx == Ctx::Discard && self.may_need_drop(ty) {
                    // `x;` outside a statement position moves `x` into a temporary.
                    return Err("discarded place of a needs-drop type");
                }
                match info.base {
                    Base::Root(r) if info.whole => {
                        self.move_out(r, &[])?;
                        Ok(info)
                    }
                    Base::Root(r) | Base::Temp(r) => {
                        // A move out of a field of a value (rustc's `MoveData` records nothing for
                        // a place whose type needs no drop).
                        if !self.may_need_drop(ty) {
                            return Ok(info);
                        }
                        if info.deref {
                            return Err("move out of a box's contents");
                        }
                        let Some(proj) = self.field_proj(e).filter(|p| !p.is_empty()) else {
                            return Err("partial move out of a tracked value");
                        };
                        self.move_out(r, &proj)?;
                        Ok(info)
                    }
                    Base::Untracked => Ok(info),
                }
            }
        }
    }

    /// An rvalue in `ctx`: in place or discard position a needs-drop rvalue is a live
    /// temporary, which every caller routes through [`Self::temp_of`]; one that reaches here
    /// unrouted is refused.
    fn rvalue_temp_check(&self, e: ExprId, ctx: Ctx) -> PResult {
        let ty = self.thir().exprs[e].ty;
        match ctx {
            Ctx::Value => Ok(()),
            Ctx::Place if self.may_need_drop(ty) => Err("live temporary needing drop"),
            Ctx::Discard if self.may_need_drop(ty) => Err("discarded temporary needing drop"),
            _ => Ok(()),
        }
    }

    /// Mark the state unreachable after an expression of an uninhabited type: `!`, or a call
    /// whose result is uninhabited from this module (`LintAndRemoveUninhabited`, the first pass
    /// of the `mir_built` provider, removes that call's return edge).
    fn after(&mut self, e: ExprId) {
        let ex = &self.thir().exprs[e];
        // Inhabitedness is asked only of a type the reveal funnel would lay out (it can reveal
        // an opaque otherwise); any other call result reads as inhabited, so the code after it
        // stays reachable — conservative: a drop there is planned, and the oracle refuses the
        // body if rustc's elaboration removed it.
        let uninhabited = ex.ty.is_never()
            || (matches!(ex.kind, ExprKind::Call { .. })
                && crate::layout_query_is_reentrant_safe_deep(self.tcx, ex.ty)
                && !ex.ty.is_inhabited_from(self.tcx, self.parent_module, self.typing_env));
        if uninhabited {
            self.unreachable();
        }
    }

    /// Bindings of a pattern: (var, binding mode, type).
    fn bindings(pat: &Pat<'tcx>) -> Vec<(LocalVarId, rustc_ast::ByRef, RustcTy<'tcx>)> {
        let mut out = Vec::new();
        pat.walk_always(|p| {
            if let PatKind::Binding { var, mode, ty, .. } = &p.kind {
                out.push((*var, mode.0, *ty));
            }
        });
        out
    }

    /// Does the pattern bind by value a value whose type needs drop (a move rustc records)?
    fn moves_needs_drop(&self, pat: &Pat<'tcx>) -> bool {
        Self::bindings(pat).iter().any(|(_, mode, ty)| {
            matches!(mode, rustc_ast::ByRef::No) && !self.is_copy(*ty) && self.may_need_drop(*ty)
        })
    }

    /// Bind a pattern on its success path (rustc's `bind_matched_candidate_for_arm_body` /
    /// `place_into_pattern`): a `ref` binding borrows the scrutinee; a by-value binding of a
    /// non-`Copy` value MOVES its path below the scrutinee (`scrut`, when the scrutinee is a
    /// tracked root or a temporary, with the field projections down to it), and one whose type
    /// needs drop is a new root scheduled in `scope` (its var scope), in frame `frame`. With
    /// `bind == None` a by-value needs-drop binding is refused (no scope to schedule it in).
    fn bind_pattern(
        &mut self,
        pat: &Pat<'tcx>,
        info: Option<PlaceInfo>,
        scrut: Option<(usize, Vec<Elem>)>,
        bind: Option<(usize, region::Scope)>,
    ) -> PResult {
        let mut bs = Vec::new();
        pattern_bindings(pat, &[], None, &mut bs);
        for b in bs {
            let by_value = matches!(b.mode, rustc_ast::ByRef::No);
            if !by_value {
                match info.map(|i| i.base) {
                    Some(Base::Root(r)) => {
                        self.roots[r].shared_borrowed = true;
                        // A `ref mut` binding is a mutable borrow.
                        if matches!(b.mode, rustc_ast::ByRef::Yes(_, rustc_ast::Mutability::Mut)) {
                            return Err("mutable borrow of a tracked value");
                        }
                    }
                    Some(Base::Temp(t)) if !info.is_some_and(|i| i.deref) => {
                        let o = match b.mode {
                            rustc_ast::ByRef::Yes(_, rustc_ast::Mutability::Mut) => Observed::Mut,
                            _ => Observed::Shared,
                        };
                        self.observe(t, o);
                    }
                    _ => {}
                }
                continue;
            }
            if self.is_copy(b.ty) || !self.may_need_drop(b.ty) {
                // A copy, or a move rustc's `MoveData` does not record (no drop to place).
                continue;
            }
            if let Some(why) = b.through {
                return Err(match why {
                    "an or-pattern" => "pattern move through an or-pattern",
                    "a slice or array pattern" => "pattern move through a slice or array pattern",
                    "a deref pattern" => "pattern move through a deref pattern",
                    "a guard pattern" => "pattern move through a guard pattern",
                    "a single-variant enum pattern" => {
                        "pattern move through a single-variant enum pattern"
                    }
                    _ => "pattern move through a binding with a subpattern",
                });
            }
            let Some((r, base)) = &scrut else {
                return Err("pattern move out of a place the planner does not track");
            };
            let mut full = base.clone();
            full.extend(b.proj.iter().copied());
            self.move_out(*r, &full)?;
            let Some((frame, scope)) = bind else {
                return Err("pattern binding of a needs-drop value");
            };
            self.trackable(b.ty)?;
            if self.scope_tree.var_scope(b.var.0.local_id) != Some(scope) {
                return Err("pattern binding scope the planner does not model");
            }
            let span = self.scope_end(scope);
            let nr = self.new_root(Root {
                identity: DropIdentity::Var(b.var.0.local_id.as_u32()),
                var: Some(b.var),
                param: None,
                ty: b.ty,
                span,
                shared_borrowed: false,
                kind: RootKind::Local,
            });
            self.set_root(nr, Init::Init);
            self.push_root_to(frame, nr);
        }
        Ok(())
    }

    /// A guarded arm's bindings during its guard: each one a reference into the scrutinee
    /// (`RefWithinGuard`), whatever its mode — a shared borrow of a tracked root (the 4b root
    /// rule) or of a temporary, a mutable one for `ref mut`.
    fn observe_guard_bindings(&mut self, pat: &Pat<'tcx>, info: PlaceInfo) -> PResult {
        if info.deref {
            return Ok(());
        }
        for (_, mode, _) in Self::bindings(pat) {
            let mutable = matches!(mode, rustc_ast::ByRef::Yes(_, rustc_ast::Mutability::Mut));
            match info.base {
                Base::Root(r) => {
                    if mutable {
                        return Err("mutable borrow of a tracked value");
                    }
                    self.roots[r].shared_borrowed = true;
                }
                Base::Temp(t) => {
                    self.observe(t, if mutable { Observed::Mut } else { Observed::Shared })
                }
                Base::Untracked => {}
            }
        }
        Ok(())
    }

    fn exit(&mut self, key: ExitKey, class: ExitClass, frames_from: usize) {
        if !self.state.reachable {
            return;
        }
        let mut roots = Vec::new();
        for f in self.frames[frames_from..].iter().rev() {
            let rs: &[usize] = match f {
                Frame::Args(r) => r,
                Frame::Block { roots, .. } => roots,
                Frame::Temps { roots, .. } => roots,
                Frame::Breakable { .. } => &[],
            };
            roots.extend(rs.iter().rev().copied());
        }
        // An exit that crosses no scheduled drop places nothing and constrains nothing.
        if roots.is_empty() {
            return;
        }
        self.pending.push(PendingEdge { key, class, roots, state: self.state.clone() });
    }

    /// The frame index just above the breakable scope `label` (the frames a `break` / `continue`
    /// to it exits).
    fn frames_above(&self, label: region::Scope) -> PResult<(usize, bool)> {
        for (i, f) in self.frames.iter().enumerate().rev() {
            if let Frame::Breakable { label: l, is_loop } = f {
                if *l == label {
                    return Ok((i + 1, *is_loop));
                }
            }
        }
        Err("break or continue to a scope the planner does not know")
    }

    fn frame_roots(&self, i: usize) -> &[usize] {
        match &self.frames[i] {
            Frame::Args(r) => r,
            Frame::Block { roots } | Frame::Temps { roots, .. } => roots,
            Frame::Breakable { .. } => &[],
        }
    }

    fn block(&mut self, b: ThirBlockId, ctx: Ctx) -> PResult {
        let blk = &self.thir().blocks[b];
        let labelled = blk.targeted_by_break;
        let label = blk.region_scope;
        let stmts: Vec<_> = blk.stmts.iter().copied().collect();
        let tail = blk.expr;
        // `ast_block`: the block's own region scope (it holds the temporaries of a
        // terminating block), then its breakable scope, then its statements' remainder scopes.
        let temps_frame = self.frames.len();
        self.frames.push(Frame::Temps { scope: blk.region_scope, roots: Vec::new(), cond: false });
        if labelled {
            self.frames.push(Frame::Breakable { label, is_loop: false });
            self.breaks.remove(&label_key(label));
        }
        let block_frame = self.frames.len();
        self.frames.push(Frame::Block { roots: Vec::new() });
        for s in stmts {
            self.stmt(s, block_frame)?;
        }
        if let Some(t) = tail {
            self.expr(t, ctx)?;
        }
        if labelled {
            self.exit(
                ExitKey::BlockEnd(b.as_u32()),
                ExitClass::BlockFallthrough(b.as_u32()),
                block_frame,
            );
            self.frames.truncate(block_frame);
            self.frames.pop();
            if let Some(broke) = self.breaks.remove(&label_key(label)) {
                self.state = self.state.join(&broke);
            }
            if !self.frame_roots(temps_frame).is_empty() {
                // Its drops run after the `break`s join, past the lowering's block-end hook.
                return Err("temporary in a labelled block's own scope");
            }
        } else {
            // The remainder scopes pop (the `let` bindings, innermost first), then the block's
            // own scope (its temporaries): one fallthrough edge, in that order.
            self.exit(
                ExitKey::BlockEnd(b.as_u32()),
                ExitClass::BlockFallthrough(b.as_u32()),
                temps_frame,
            );
        }
        self.frames.truncate(temps_frame);
        Ok(())
    }

    fn stmt(&mut self, s: rustc_middle::thir::StmtId, block_frame: usize) -> PResult {
        match &self.thir().stmts[s].kind {
            StmtKind::Expr { scope, expr } => {
                let (scope, e) = (*scope, *expr);
                let fi = self.frames.len();
                self.frames.push(Frame::Temps { scope, roots: Vec::new(), cond: false });
                let ty = self.thir().exprs[e].ty;
                if self.may_need_drop(ty) {
                    // `stmt_expr`'s fallback: the statement's value is written to a temporary
                    // whose drop is scheduled in the statement scope (after the value), and
                    // dropped when the statement ends (`x;` moves `x` into it).
                    self.trackable(ty)?;
                    let exprs = self.value_chain(e);
                    self.expr(e, Ctx::Value)?;
                    self.add_temp(fi, scope, exprs, ty, Observed::No);
                } else {
                    self.expr(e, Ctx::Discard)?;
                }
                self.exit(ExitKey::StmtEnd(s.as_u32()), ExitClass::StmtFallthrough(s.as_u32()), fi);
                self.frames.truncate(fi);
                Ok(())
            }
            StmtKind::Let { init_scope, remainder_scope, else_block, .. } => {
                let (init_scope, remainder_scope) = (*init_scope, *remainder_scope);
                let has_else = else_block.is_some();
                let fi = self.frames.len();
                self.frames.push(Frame::Temps {
                    scope: init_scope,
                    roots: Vec::new(),
                    cond: false,
                });
                self.remainders.push((remainder_scope, block_frame));
                let r = self.let_stmt(s, block_frame);
                self.remainders.pop();
                r?;
                if has_else && !self.frame_roots(fi).is_empty() {
                    return Err("temporary in a let-else initializer");
                }
                self.exit(ExitKey::StmtEnd(s.as_u32()), ExitClass::StmtFallthrough(s.as_u32()), fi);
                self.frames.truncate(fi);
                Ok(())
            }
        }
    }

    /// The scrutinee of a `match`, `if let` or destructuring `let`, evaluated as MIR building's
    /// `lower_scrutinee` does (a place in place, an rvalue into a temporary).
    fn scrutinee(&mut self, scrut: ExprId) -> PResult<(PlaceInfo, Option<(usize, Vec<Elem>)>)> {
        let info = if self.is_place_expr(scrut) {
            self.place(scrut, Ctx::Place)?
        } else {
            self.rvalue_place(scrut)?
        };
        let path = self.scrut_path(scrut, info);
        Ok((info, path))
    }

    /// A refutable pattern's two outcomes on its scrutinee path: the state of the failure edge
    /// (the tested variant inactive when the variant is the pattern's only test; otherwise also
    /// the variant-active state a nested test fails from), and the success state's variant kill.
    fn split_on_variant(&mut self, pat: &Pat<'tcx>, scrut: &Option<(usize, Vec<Elem>)>) -> State {
        let pre = self.state.clone();
        let Some((r, base)) = scrut.clone() else { return pre };
        let Some(v) = top_variant(pat) else { return pre };
        self.kill_variants(r, &base, &|w| w != v);
        let killed = std::mem::replace(&mut self.state, pre.clone());
        // The success edge: every other variant inactive.
        self.kill_variants(r, &base, &|w| w == v);
        if variant_test_only(pat) { killed } else { killed.join(&pre) }
    }

    fn let_stmt(&mut self, s: rustc_middle::thir::StmtId, block_frame: usize) -> PResult {
        let StmtKind::Let { pattern, initializer, else_block, remainder_scope, .. } =
            &self.thir().stmts[s].kind
        else {
            return Err("a let statement that is not one");
        };
        let pattern: &Pat<'tcx> = pattern;
        let initializer = *initializer;
        let else_block = *else_block;
        let remainder_scope = *remainder_scope;
        // A simple by-value binding `let x [: T] [= init];`.
        if let PatKind::Binding {
            var,
            mode: rustc_ast::BindingMode(rustc_ast::ByRef::No, _),
            subpattern: None,
            ty,
            ..
        } = &pattern.kind
        {
            if else_block.is_some() {
                return Err("let-else with a simple binding");
            }
            let (var, ty) = (*var, *ty);
            if let Some(init) = initializer {
                self.expr(init, Ctx::Value)?;
            }
            if self.may_need_drop(ty) {
                self.trackable(ty)?;
                // The binding's drop is scheduled in its var scope, which for an ordinary
                // `let` is the statement's remainder scope; anything else (`super let`'s
                // extended scope) is not modelled.
                if self.scope_tree.var_scope(var.0.local_id) != Some(remainder_scope) {
                    return Err("binding scope is not its let's remainder scope");
                }
                let span = self.scope_end(remainder_scope);
                let r = self.new_root(Root {
                    identity: DropIdentity::Var(var.0.local_id.as_u32()),
                    var: Some(var),
                    param: None,
                    ty,
                    span,
                    shared_borrowed: false,
                    kind: RootKind::Local,
                });
                let init_state = if initializer.is_some() { Init::Init } else { Init::Uninit };
                self.set_root(r, init_state);
                self.push_root_to(block_frame, r);
            }
            return Ok(());
        }
        // Every other pattern: the initializer is the scrutinee (a place read in place, an
        // rvalue a temporary in its temporary scope); a by-value binding moves its part out and
        // is scheduled in the remainder scope (`declare_bindings` there).
        let Some(init) = initializer else {
            return self.bind_pattern(pattern, None, None, None);
        };
        let (info, scrut) = self.scrutinee(init)?;
        let bind = Some((block_frame, remainder_scope));
        if let Some(eb) = else_block {
            // let-else: the pattern is tested; the else block runs on its failure edge (and must
            // diverge), the bindings on its success edge.
            if self.moves_needs_drop(pattern) && top_variant(pattern).is_none() {
                return Err("let-else whose pattern moves without a variant test");
            }
            let fail = self.split_on_variant(pattern, &scrut);
            self.bind_pattern(pattern, Some(info), scrut, bind)?;
            let success = std::mem::replace(&mut self.state, fail);
            self.block(eb, Ctx::Discard)?;
            self.state = success;
            return Ok(());
        }
        self.bind_pattern(pattern, Some(info), scrut, bind)
    }

    /// `*p = v` through a `&mut` or a raw pointer — the drop-and-replace rustc builds with the
    /// old pointee dropped through the pointer.
    fn is_deref_of_pointer(&self, lhs: ExprId) -> bool {
        let p = self.peel(lhs);
        let ExprKind::Deref { arg } = &self.thir().exprs[p].kind else { return false };
        matches!(
            self.thir().exprs[*arg].ty.kind(),
            ty::Ref(_, _, rustc_ast::Mutability::Mut) | ty::RawPtr(_, rustc_ast::Mutability::Mut)
        )
    }

    /// An `if` whose condition is an `if let` that moves part of its scrutinee: the two edges
    /// out of the test carry different states (the bindings and moves on the success edge, the
    /// tested variant inactive on the failure edge). Returns the failure edge's state, with the
    /// success edge's in `self.state`; `None` when the condition is not such a `let`.
    fn if_let_split(
        &mut self,
        cond: ExprId,
        then_frame: usize,
        then_scope: region::Scope,
    ) -> PResult<Option<State>> {
        let chain = self.scope_chain(cond);
        let inner = *chain.last().unwrap_or(&cond);
        let ExprKind::Let { expr: scrut, pat } = &self.thir().exprs[inner].kind else {
            return Ok(None);
        };
        let scrut = *scrut;
        let pat: &Pat<'tcx> = pat;
        if !self.moves_needs_drop(pat) {
            return Ok(None);
        }
        if top_variant(pat).is_none() {
            return Err("if-let whose pattern moves without a variant test");
        }
        // The condition's own scopes (it is not a terminating scope): they hold nothing here.
        let base = self.frames.len();
        for w in &chain[..chain.len() - 1] {
            if let ExprKind::Scope { region_scope, .. } = &self.thir().exprs[*w].kind {
                self.frames.push(Frame::Temps {
                    scope: *region_scope,
                    roots: Vec::new(),
                    cond: true,
                });
            }
        }
        let (info, path) = self.scrutinee(scrut)?;
        let fail = self.split_on_variant(pat, &path);
        self.bind_pattern(pat, Some(info), path, Some((then_frame, then_scope)))?;
        if (base..self.frames.len()).any(|i| !self.frame_roots(i).is_empty()) {
            return Err("temporary in an if-let condition's own scope");
        }
        self.frames.truncate(base);
        Ok(Some(fail))
    }

    /// An `if`'s condition that is a VALUE under `Scope` / `Use` / `!` wrappers (no `&&` / `||`,
    /// no `let`): `then_else_break` pops the wrappers' scopes on BOTH edges out of the test, so
    /// their temporaries are dropped at the start of the then branch and at the start of the
    /// else branch (one `Drop` terminator each) — the `CondThen` / `CondElse` exits of the `if`,
    /// placed by the `if` lowering's hooks. `false` when the condition is not of that shape.
    fn branch_cond(&mut self, c: ExprId) -> PResult<bool> {
        let mut scopes = Vec::new();
        let mut cur = c;
        loop {
            let ex = &self.thir().exprs[cur];
            match &ex.kind {
                ExprKind::Scope { region_scope, value, .. } => {
                    scopes.push(*region_scope);
                    cur = *value;
                }
                ExprKind::ValueExpr { source } => cur = *source,
                ExprKind::Unary { op: rustc_middle::mir::UnOp::Not, arg } if ex.ty.is_bool() => {
                    cur = *arg
                }
                ExprKind::LogicalOp { .. } | ExprKind::Let { .. } => return Ok(false),
                _ => break,
            }
        }
        let base = self.frames.len();
        for s in scopes {
            self.frames.push(Frame::Temps { scope: s, roots: Vec::new(), cond: false });
        }
        let r = self.expr(cur, Ctx::Value);
        if r.is_ok() {
            self.exit(ExitKey::CondThen(c.as_u32()), ExitClass::CondTrueEdge(c.as_u32()), base);
            self.exit(ExitKey::CondElse(c.as_u32()), ExitClass::CondFalseEdge(c.as_u32()), base);
        }
        self.frames.truncate(base);
        r?;
        Ok(true)
    }

    /// A condition, as `then_else_break` lowers it (an `if`'s, a guard's, the left operand of a
    /// `&&` / `||`): its `Scope`, `Use`, `!` and `&&`/`||` wrappers branch rather than produce a
    /// value, so the drops of their scopes run on both outgoing edges — scopes marked `cond`,
    /// where a temporary is refused. The leaf is an ordinary value.
    fn cond_expr(&mut self, e: ExprId) -> PResult {
        let ex = &self.thir().exprs[e];
        match &ex.kind {
            ExprKind::Scope { region_scope, value, .. } => {
                let (rs, v) = (*region_scope, *value);
                let fi = self.frames.len();
                self.frames.push(Frame::Temps { scope: rs, roots: Vec::new(), cond: true });
                let r = self.cond_expr(v);
                self.frames.truncate(fi);
                r?;
            }
            ExprKind::ValueExpr { source } => {
                let s = *source;
                self.cond_expr(s)?;
            }
            ExprKind::Unary { op: rustc_middle::mir::UnOp::Not, arg } if ex.ty.is_bool() => {
                let a = *arg;
                self.cond_expr(a)?;
            }
            ExprKind::LogicalOp { lhs, rhs, .. } => {
                let (l, r) = (*lhs, *rhs);
                self.cond_expr(l)?;
                let short = self.state.clone();
                self.cond_expr(r)?;
                self.state = self.state.join(&short);
            }
            _ => return self.expr(e, Ctx::Value),
        }
        self.after(e);
        Ok(())
    }

    fn expr(&mut self, e: ExprId, ctx: Ctx) -> PResult {
        let ex = &self.thir().exprs[e];
        let ty = ex.ty;
        match &ex.kind {
            ExprKind::Scope { region_scope, value, .. } => {
                let (rs, v) = (*region_scope, *value);
                let fi = self.frames.len();
                self.frames.push(Frame::Temps { scope: rs, roots: Vec::new(), cond: false });
                let r = self.expr(v, ctx);
                if r.is_ok() {
                    self.exit(
                        ExitKey::ScopeEnd(e.as_u32()),
                        ExitClass::ScopeFallthrough(e.as_u32()),
                        fi,
                    );
                }
                self.frames.truncate(fi);
                r?;
            }
            ExprKind::Field { .. }
            | ExprKind::Deref { .. }
            | ExprKind::Index { .. }
            | ExprKind::UpvarRef { .. }
            | ExprKind::VarRef { .. }
            | ExprKind::PlaceTypeAscription { .. }
            | ExprKind::ValueTypeAscription { .. } => {
                self.place(e, ctx)?;
            }
            ExprKind::PlaceUnwrapUnsafeBinder { .. }
            | ExprKind::ValueUnwrapUnsafeBinder { .. }
            | ExprKind::WrapUnsafeBinder { .. } => return Err("unsafe binder"),
            ExprKind::ValueExpr { source }
            | ExprKind::Cast { source }
            | ExprKind::PointerCoercion { source, .. }
            | ExprKind::Reborrow { source, .. } => {
                let s = *source;
                self.rvalue_temp_check(e, ctx)?;
                self.expr(s, Ctx::Value)?;
            }
            ExprKind::NeverToAny { source } => {
                let s = *source;
                self.expr(s, Ctx::Value)?;
                self.unreachable();
            }
            ExprKind::Unary { arg, .. } => {
                let a = *arg;
                self.expr(a, Ctx::Value)?;
            }
            ExprKind::Binary { lhs, rhs, .. } => {
                let (l, r) = (*lhs, *rhs);
                self.expr(l, Ctx::Value)?;
                self.expr(r, Ctx::Value)?;
            }
            ExprKind::LogicalOp { lhs, rhs, .. } => {
                // `expr_into_dest`: the left operand is a condition (`then_else_break`), the
                // right one a value.
                let (l, r) = (*lhs, *rhs);
                self.cond_expr(l)?;
                let short = self.state.clone();
                self.expr(r, Ctx::Value)?;
                self.state = self.state.join(&short);
            }
            ExprKind::If { if_then_scope, cond, then, else_opt } => {
                let (its, c, t, el) = (*if_then_scope, *cond, *then, *else_opt);
                self.rvalue_temp_check(e, ctx)?;
                // `in_if_then_scope`: the then-scope encloses the condition and the then
                // branch; an `if let`'s bindings are scheduled in it and dropped when the then
                // branch falls through (on the else edge they were never bound).
                let tf = self.frames.len();
                self.frames.push(Frame::Temps { scope: its, roots: Vec::new(), cond: false });
                let else_state = match self.if_let_split(c, tf, its)? {
                    Some(fail) => fail,
                    None => {
                        if !self.branch_cond(c)? {
                            self.cond_expr(c)?;
                        }
                        self.state.clone()
                    }
                };
                self.expr(t, Ctx::Value)?;
                self.exit(
                    ExitKey::EnclosingEnd(t.as_u32()),
                    ExitClass::EnclosingFallthrough(t.as_u32()),
                    tf,
                );
                self.frames.truncate(tf);
                let after_then = std::mem::replace(&mut self.state, else_state);
                if let Some(el) = el {
                    self.expr(el, Ctx::Value)?;
                }
                self.state = self.state.join(&after_then);
            }
            ExprKind::Let { expr, pat } => {
                // A `let` the `if` above did not split (a let chain, a guard, a `while let`'s
                // desugaring that tests without moving): its bindings may not move a needs-drop
                // part.
                let scrut = *expr;
                let pat: &Pat<'tcx> = pat;
                let (info, path) = self.scrutinee(scrut)?;
                self.bind_pattern(pat, Some(info), path, None)?;
            }
            ExprKind::Match { scrutinee, arms, .. } => {
                let scrut = *scrutinee;
                let arms: Vec<_> = arms.iter().copied().collect();
                self.rvalue_temp_check(e, ctx)?;
                let (info, path) = self.scrutinee(scrut)?;
                // The variant each arm's pattern tests at the top: the discriminant switch's
                // explicit targets. A catch-all arm is entered from the switch's otherwise edge,
                // where the variants the arms BEFORE it test are inactive — when every arm before
                // it tests only its variant (a nested test's failure enters it with the variant
                // active). An arm after the catch-all is unreachable and tests nothing on that
                // edge: a variant only it names still reaches the catch-all with its payload.
                let tops: Vec<Option<u32>> =
                    arms.iter().map(|a| top_variant(&self.thir().arms[*a].pattern)).collect();
                let mut only_variant_tests_so_far = true;
                let mut pending = self.state.clone();
                let mut result = State::unreachable(self.n());
                for (i, a) in arms.into_iter().enumerate() {
                    let arm = &self.thir().arms[a];
                    let pat: &Pat<'tcx> = &arm.pattern;
                    let (guard, body, arm_scope) = (arm.guard, arm.body, arm.scope);
                    self.state = pending.clone();
                    if let Some((r, base)) = path.clone() {
                        if let Some(v) = top_variant(pat) {
                            self.kill_variants(r, &base, &|w| w == v);
                        } else if irrefutable(pat) && only_variant_tests_so_far {
                            let tested = variants_tested_before(&tops, i);
                            if !tested.is_empty() {
                                self.kill_variants(r, &base, &|w| !tested.contains(&w));
                            }
                        }
                    }
                    only_variant_tests_so_far &= variant_test_only(pat) && guard.is_none();
                    // `lower_match_arms`: each arm body runs in the arm's scope, which pops
                    // (dropping the arm's bindings and temporaries) when the body falls through.
                    let af = self.frames.len();
                    self.frames.push(Frame::Temps {
                        scope: arm_scope,
                        roots: Vec::new(),
                        cond: false,
                    });
                    if let Some(g) = guard {
                        // `bind_and_guard_matched_candidate`: the guard runs with every binding
                        // BY REFERENCE into the scrutinee (no move yet); its failure falls to the
                        // next candidate with the scrutinee whole. The by-value bindings move
                        // after it succeeds.
                        self.observe_guard_bindings(pat, info)?;
                        self.cond_expr(g)?;
                        pending = pending.join(&self.state);
                    }
                    self.bind_pattern(pat, Some(info), path.clone(), Some((af, arm_scope)))?;
                    self.expr(body, Ctx::Value)?;
                    self.exit(
                        ExitKey::EnclosingEnd(body.as_u32()),
                        ExitClass::EnclosingFallthrough(body.as_u32()),
                        af,
                    );
                    self.frames.truncate(af);
                    result = result.join(&self.state);
                    result.grow(self.n());
                    pending.grow(self.n());
                }
                self.state = result;
            }
            ExprKind::Loop { body } => {
                let body = *body;
                let label =
                    region::Scope { local_id: ex.temp_scope_id, data: region::ScopeData::Node };
                let key = label_key(label);
                let entry = self.state.clone();
                let mut head = entry.clone();
                if let Some(back) = self.back_prev.get(&key) {
                    head = head.join(back);
                }
                self.state = head;
                self.frames.push(Frame::Breakable { label, is_loop: true });
                self.breaks.remove(&key);
                self.expr(body, Ctx::Discard)?;
                // The body's fallthrough goes round again.
                let fall = self.state.clone();
                self.back_cur.entry(key).and_modify(|s| *s = s.join(&fall)).or_insert(fall);
                self.frames.pop();
                self.state =
                    self.breaks.remove(&key).unwrap_or_else(|| State::unreachable(self.n()));
            }
            ExprKind::LoopMatch { .. } | ExprKind::ConstContinue { .. } => {
                return Err("loop_match");
            }
            ExprKind::Block { block } => {
                let b = *block;
                self.rvalue_temp_check(e, ctx)?;
                self.block(b, if ctx == Ctx::Discard { Ctx::Discard } else { Ctx::Value })?;
            }
            ExprKind::Assign { lhs, rhs } => {
                let (l, r) = (*lhs, *rhs);
                // rustc evaluates the right-hand side first (`stmt_expr`, "evaluate assignments
                // right-to-left").
                self.expr(r, Ctx::Value)?;
                let lhs_ty = self.thir().exprs[l].ty;
                if self.may_need_drop(lhs_ty) {
                    match self.place_base(l) {
                        Some((root, true)) => {
                            self.place_info(l)?;
                            if self.state.reachable {
                                let span = self.thir().exprs[l].span;
                                self.replace_spans.insert(e.as_u32(), span);
                                self.exit_replace(e, root);
                            }
                            self.set_root(root, Init::Init);
                        }
                        None if self.is_deref_of_pointer(l) => {
                            // Trust (step 2 increment 4b residuals): `*p = v` through a `&mut` or
                            // a raw pointer. The pointer is not a tracked value; the old pointee
                            // is dropped unconditionally, through the pointer, before the store.
                            let info = self.place_info(l)?;
                            if info.base != Base::Untracked {
                                return Err(
                                    "drop-and-replace through a pointer held by a tracked value",
                                );
                            }
                            self.trackable(lhs_ty)?;
                            if self.state.reachable {
                                let span = self.thir().exprs[l].span;
                                let root = self.add_root(Root {
                                    identity: DropIdentity::Other,
                                    var: None,
                                    param: None,
                                    ty: lhs_ty,
                                    span,
                                    shared_borrowed: false,
                                    kind: RootKind::Pointee,
                                });
                                self.state.set(root, Init::Init);
                                self.replace_spans.insert(e.as_u32(), span);
                                self.exit_replace(e, root);
                            }
                        }
                        _ => return Err("drop-and-replace of a place that is not a tracked local"),
                    }
                } else {
                    let info = self.place(l, Ctx::Place)?;
                    Self::write_into(info)?;
                }
            }
            ExprKind::AssignOp { lhs, rhs, .. } => {
                let (l, r) = (*lhs, *rhs);
                self.expr(r, Ctx::Value)?;
                let info = self.place(l, Ctx::Place)?;
                Self::write_into(info)?;
            }
            ExprKind::Call { fun, args, .. } => {
                let fun = *fun;
                let args: Vec<_> = args.iter().copied().collect();
                self.rvalue_temp_check(e, ctx)?;
                if let ty::FnDef(def_id, _) = self.thir().exprs[fun].ty.kind() {
                    if is_catch_unwind(self.tcx, *def_id) {
                        // Design §8: post-panic state is observable through `catch_unwind`, and
                        // the module models abort-on-panic only.
                        return Err("call to catch_unwind");
                    }
                }
                self.expr(fun, Ctx::Value)?;
                for a in args {
                    self.expr(a, Ctx::Value)?;
                }
            }
            ExprKind::ByUse { .. } => return Err("ergonomic `.use`"),
            ExprKind::Borrow { borrow_kind, arg } => {
                let (bk, a) = (*borrow_kind, *arg);
                let observed = match bk {
                    rustc_middle::mir::BorrowKind::Shared => Observed::Shared,
                    rustc_middle::mir::BorrowKind::Fake(_) => Observed::No,
                    rustc_middle::mir::BorrowKind::Mut { .. } => Observed::Mut,
                };
                if self.is_place_expr(a) {
                    let info = self.place(a, Ctx::Place)?;
                    match info.base {
                        Base::Root(r) => match bk {
                            rustc_middle::mir::BorrowKind::Shared => {
                                self.roots[r].shared_borrowed = true
                            }
                            rustc_middle::mir::BorrowKind::Fake(_) => {}
                            rustc_middle::mir::BorrowKind::Mut { .. } => {
                                return Err("mutable borrow of a tracked value");
                            }
                        },
                        Base::Temp(t) if !info.deref => self.observe(t, observed),
                        _ => {}
                    }
                } else {
                    // `&f()`: the borrow of a temporary in its temporary scope (extended to the
                    // `let`'s remainder scope for `let x = &f();`).
                    if let Some(t) = self.temp_of(a, observed)? {
                        if observed != Observed::No {
                            if let RootKind::Temp(tr) = &mut self.roots[t].kind {
                                tr.borrow = Some(e);
                            }
                        }
                    }
                }
            }
            ExprKind::RawBorrow { arg, .. } => {
                let a = *arg;
                if self.is_place_expr(a) {
                    let info = self.place(a, Ctx::Place)?;
                    match info.base {
                        Base::Root(_) => return Err("raw borrow of a tracked value"),
                        Base::Temp(t) if !info.deref => self.observe(t, Observed::Mut),
                        _ => {}
                    }
                } else {
                    self.temp_of(a, Observed::Mut)?;
                }
            }
            ExprKind::Break { label, value } => {
                let (label, value) = (*label, *value);
                if let Some(v) = value {
                    self.expr(v, Ctx::Value)?;
                }
                let (from, _is_loop) = self.frames_above(label)?;
                let key = label_key(label);
                self.exit(ExitKey::Break(e.as_u32()), ExitClass::BreakTree(key), from);
                if self.state.reachable {
                    let s = self.state.clone();
                    self.breaks.entry(key).and_modify(|b| *b = b.join(&s)).or_insert(s);
                }
                self.unreachable();
            }
            ExprKind::Continue { label } => {
                let label = *label;
                let (from, is_loop) = self.frames_above(label)?;
                if !is_loop {
                    return Err("continue to a labelled block");
                }
                let key = label_key(label);
                self.exit(ExitKey::Continue(e.as_u32()), ExitClass::ContinueTree(key), from);
                if self.state.reachable {
                    let s = self.state.clone();
                    self.back_cur.entry(key).and_modify(|b| *b = b.join(&s)).or_insert(s);
                }
                self.unreachable();
            }
            ExprKind::Return { value } => {
                if let Some(v) = *value {
                    self.expr(v, Ctx::Value)?;
                }
                self.exit(ExitKey::Return(e.as_u32()), ExitClass::ReturnTree, 0);
                self.unreachable();
            }
            ExprKind::Become { .. } => return Err("tail call"),
            ExprKind::ConstBlock { .. }
            | ExprKind::Literal { .. }
            | ExprKind::NonHirLiteral { .. }
            | ExprKind::ZstLiteral { .. }
            | ExprKind::NamedConst { .. }
            | ExprKind::ConstParam { .. }
            | ExprKind::StaticRef { .. }
            | ExprKind::ThreadLocalRef(_) => {
                self.rvalue_temp_check(e, ctx)?;
            }
            ExprKind::Repeat { value, count } => {
                let (v, count) = (*value, *count);
                self.rvalue_temp_check(e, ctx)?;
                // `[x; 0]` moves `x` into a temporary that is dropped at once
                // (`build_zero_repeat`): a live temporary.
                if matches!(count.try_to_target_usize(self.tcx), None | Some(0))
                    && self.may_need_drop(self.thir().exprs[v].ty)
                {
                    return Err("zero-length or unevaluated repeat of a needs-drop value");
                }
                self.expr(v, Ctx::Value)?;
            }
            ExprKind::Array { fields } | ExprKind::Tuple { fields } => {
                let fields: Vec<_> = fields.iter().copied().collect();
                self.rvalue_temp_check(e, ctx)?;
                for f in fields {
                    self.expr(f, Ctx::Value)?;
                }
            }
            ExprKind::Adt(adt) => {
                let fields: Vec<_> = adt.fields.iter().map(|f| f.expr).collect();
                let base = match &adt.base {
                    rustc_middle::thir::AdtExprBase::Base(fru) => Some(fru.base),
                    _ => None,
                };
                self.rvalue_temp_check(e, ctx)?;
                for f in fields {
                    self.expr(f, Ctx::Value)?;
                }
                if let Some(b) = base {
                    if self.place_base(b).is_some() {
                        return Err("functional record update from a tracked value");
                    }
                    if self.is_place_expr(b) {
                        self.place(b, Ctx::Place)?;
                    } else {
                        if self.may_need_drop(self.thir().exprs[b].ty) {
                            return Err("functional record update from a needs-drop temporary");
                        }
                        self.expr(b, Ctx::Value)?;
                    }
                }
            }
            ExprKind::Closure(closure) => {
                let upvars: Vec<_> = closure.upvars.iter().copied().collect();
                self.rvalue_temp_check(e, ctx)?;
                for u in upvars {
                    self.expr(u, Ctx::Value)?;
                }
            }
            ExprKind::InlineAsm(_) => return Err("inline asm"),
            ExprKind::Yield { .. } => return Err("yield"),
        }
        let _ = ty;
        self.after(e);
        Ok(())
    }

    /// The drop-and-replace edge of assignment `e` to root `root` (one `Drop` terminator).
    fn exit_replace(&mut self, e: ExprId, root: usize) {
        self.pending.push(PendingEdge {
            key: ExitKey::Replace(e.as_u32()),
            class: ExitClass::Replace(e.as_u32()),
            roots: vec![root],
            state: self.state.clone(),
        });
    }
}

/// `std::panic::catch_unwind`, `std::panicking::catch_unwind` or the `catch_unwind` intrinsic.
fn is_catch_unwind(tcx: TyCtxt<'_>, def_id: rustc_span::def_id::DefId) -> bool {
    tcx.opt_item_name(def_id).is_some_and(|n| n.as_str() == "catch_unwind")
        && matches!(tcx.crate_name(def_id.krate).as_str(), "std" | "core" | "alloc")
}

/// Design §8: under `panic=unwind` a body that calls `catch_unwind` OBSERVES post-panic state —
/// the cleanup drops a panic runs and the value `catch_unwind` returns — and the trust-ir (no
/// unwind edge on `Call`, cleanup drops not modelled) describes the program under abort-on-panic
/// only. The first such call, if any. A `catch_unwind` reached through a function pointer or a
/// callee is not seen here.
pub(crate) fn catch_unwind_site(tcx: TyCtxt<'_>, thir: &Thir<'_>) -> Option<Span> {
    thir.exprs.iter().find_map(|ex| match ex.kind {
        ExprKind::Call { fun, .. } => match thir.exprs[fun].ty.kind() {
            ty::FnDef(def_id, _) if is_catch_unwind(tcx, *def_id) => Some(ex.span),
            _ => None,
        },
        _ => None,
    })
}

/// Plan the drops of a fn body. `Ok(None)`: nothing to drop (no tracked root). `Err(reason)`:
/// the body has a needs-drop value this cut cannot place; the producer then emits no drop.
pub(crate) fn plan_body<'tcx>(
    tcx: TyCtxt<'tcx>,
    def: LocalDefId,
    thir: &Thir<'tcx>,
    root: ExprId,
) -> Result<Option<DropPlan<'tcx>>, &'static str> {
    if !matches!(thir.body_type, BodyTy::Fn(_)) {
        return Ok(None);
    }
    if tcx.is_coroutine(def.to_def_id()) {
        return Err("coroutine body");
    }
    let typing_env = ty::TypingEnv::non_body_analysis(tcx, def);
    let scope_tree = tcx.region_scope_tree(def);
    let body_id = tcx.hir_body_owned_by(def).value.hir_id.local_id;
    let arg_scope = region::Scope { local_id: body_id, data: region::ScopeData::Arguments };
    let mut p = Planner {
        tcx,
        thir,
        typing_env,
        scope_tree,
        parent_module: tcx.parent_module_from_def_id(def),
        roots: Vec::new(),
        var_root: std::collections::HashMap::new(),
        frames: Vec::new(),
        state: State::entry(0),
        pending: Vec::new(),
        replace_spans: BTreeMap::new(),
        back_prev: BTreeMap::new(),
        back_cur: BTreeMap::new(),
        breaks: BTreeMap::new(),
        remainders: Vec::new(),
        known_paths: BTreeMap::new(),
        new_paths: false,
        children: BTreeMap::new(),
    };
    // The parameters, scheduled in the argument scope in order.
    let mut params = Vec::new();
    let arg_end = p.scope_end(arg_scope);
    for (i, param) in thir.params.iter().enumerate() {
        if !p.may_need_drop(param.ty) {
            continue;
        }
        p.trackable(param.ty)?;
        let var = match param.pat.as_deref().map(|pat| &pat.kind) {
            Some(PatKind::Binding {
                var,
                mode: rustc_ast::BindingMode(rustc_ast::ByRef::No, _),
                subpattern: None,
                ..
            }) => Some(*var),
            Some(PatKind::Wild) | Some(PatKind::Missing) => None,
            None => {
                return Err("parameter without a pattern needing drop (a by-value closure env)");
            }
            Some(_) => return Err("destructured parameter needing drop"),
        };
        params.push((i, var, param.ty));
    }
    // Every needs-drop by-value binding is a root (or the plan is refused). Cheap pre-scan:
    // no tracked param and no needs-drop expression type anywhere means nothing to drop.
    let any_drop_ty = !params.is_empty()
        || thir.exprs.iter().any(|ex| p.may_need_drop(ex.ty))
        || thir.stmts.iter().any(|s| match &s.kind {
            StmtKind::Let { pattern, .. } => {
                Planner::bindings(pattern).iter().any(|(_, _, t)| p.may_need_drop(*t))
            }
            _ => false,
        });
    if !any_drop_ty {
        return Ok(None);
    }
    let mut rounds = 0;
    loop {
        rounds += 1;
        if rounds > FIXPOINT_ROUNDS {
            return Err("loop fixpoint did not converge");
        }
        // Each round re-declares every root in walk order (deterministic), each with a slot for
        // every move path below it the body creates.
        p.roots.clear();
        p.var_root.clear();
        p.children.clear();
        p.state = State::entry(0);
        p.frames = vec![Frame::Args(Vec::new())];
        p.pending.clear();
        p.replace_spans.clear();
        p.back_cur.clear();
        p.breaks.clear();
        p.remainders.clear();
        p.new_paths = false;
        for (i, var, ty) in &params {
            let r = p.new_root(Root {
                identity: DropIdentity::Param(*i as u32),
                var: *var,
                param: Some(*i),
                ty: *ty,
                span: arg_end,
                shared_borrowed: false,
                kind: RootKind::Local,
            });
            p.set_root(r, Init::Init);
            p.push_root_to(0, r);
        }
        p.expr(root, Ctx::Value)?;
        p.exit(ExitKey::BodyEnd, ExitClass::ArgsFallthrough, 0);
        if p.new_paths {
            // A move path this round discovered must exist from its root's declaration on:
            // redo the walk with it declared (and the loop heads recomputed).
            p.back_prev.clear();
            continue;
        }
        // Back-edge states of this round, grown to the final root count.
        let n = p.roots.len();
        let mut cur = std::mem::take(&mut p.back_cur);
        for s in cur.values_mut() {
            s.grow(n);
        }
        let mut prev = std::mem::take(&mut p.back_prev);
        for s in prev.values_mut() {
            s.grow(n);
        }
        if cur == prev {
            break;
        }
        p.back_prev = cur;
    }
    if !p.roots.iter().any(|r| !matches!(r.kind, RootKind::Path)) {
        return Ok(None);
    }
    // Every move path is known now: each edge's styles, and each class's from the join of its
    // edges' states (the state rustc's one `Drop` node of that class sees).
    let pending = std::mem::take(&mut p.pending);
    let mut edges = Vec::with_capacity(pending.len());
    let mut joined: BTreeMap<(usize, ExitClass), State> = BTreeMap::new();
    let open_as_static = mutation() == Some("open-as-static");
    for pe in &pending {
        let drops = pe
            .roots
            .iter()
            .map(|r| {
                let s = p.edge_style(*r, &pe.state);
                // TEST-ONLY: an open drop placed as a whole drop.
                (*r, if open_as_static && s == Style::Open { Style::Static } else { s })
            })
            .collect();
        edges.push(Edge { key: pe.key, class: pe.class, drops });
        for r in &pe.roots {
            joined
                .entry((*r, pe.class))
                .and_modify(|s| *s = s.join(&pe.state))
                .or_insert_with(|| pe.state.clone());
        }
    }
    let plan = Plan { edges };
    match plan.feasible() {
        Ok(()) => {}
        Err(kernel::Infeasible::ConditionalOnEdge) => {
            return Err("a drop is maybe-initialized on one edge (needs a drop flag)");
        }
        Err(kernel::Infeasible::OpenOnEdge) => {
            return Err("an open drop of a partially moved value drops part of it");
        }
        Err(kernel::Infeasible::KeyConflict) => return Err("an exit was planned twice"),
    }
    let class_styles: BTreeMap<(usize, ExitClass), LiveStyle> = joined
        .iter()
        .filter_map(|(k, st)| {
            let s = p.class_style(k.0, st);
            // TEST-ONLY (`open-as-static`): the claim follows the mutated placement.
            let s = match s {
                Some(LiveStyle::Open) if open_as_static => Some(LiveStyle::Static),
                None if open_as_static && p.deep(k.0, &[], st).0 => Some(LiveStyle::Static),
                s => s,
            };
            s.map(|s| (*k, s))
        })
        .collect();
    // Address identity: spilling a shared-borrowed value is allowed only when its content
    // cannot change through the borrow (`Freeze`) and its glue only releases memory. A named
    // local outside that subset instead requires its actual promoted home at placement. The
    // planner cannot assert that promotion succeeded: emit_one_drop checks the real slot.
    // A temporary's borrow is judged at placement instead (step 2 increment 4b residuals): the
    // drop goes through the home `borrowed_temp_home` proves for a whole borrow, and only
    // otherwise under this same rule (`LowerCx::emit_temp_drop`).
    let mut destructor = Vec::with_capacity(p.roots.len());
    let mut freeze = Vec::with_capacity(p.roots.len());
    for r in &p.roots {
        if matches!(r.kind, RootKind::Path) {
            destructor.push(false);
            freeze.push(true);
            continue;
        }
        let d = crate::effect_conservation::drop_runs_destructor_pub(tcx, typing_env, r.ty);
        let shared_temp = matches!(&r.kind, RootKind::Temp(t) if t.observed == Observed::Shared);
        let f = if r.shared_borrowed || shared_temp {
            crate::is_freeze_without_reveal(tcx, r.ty, typing_env)
        } else {
            true
        };
        let needs_home = r.shared_borrowed && (d || !f);
        if needs_home && !(matches!(r.kind, RootKind::Local) && r.var.is_some()) {
            return Err("shared borrow of a value whose drop could observe its address");
        }
        destructor.push(d);
        freeze.push(f);
    }
    Ok(Some(DropPlan {
        roots: std::mem::take(&mut p.roots),
        plan,
        replace_spans: std::mem::take(&mut p.replace_spans),
        destructor,
        freeze,
        class_styles,
    }))
}

// =============================================================================================
// The producer side: placement hooks on `LowerCx`.
// =============================================================================================

/// The per-body drop state `LowerCx` carries.
#[derive(Default)]
pub(crate) struct DropLowering<'tcx> {
    /// `Some` when the body was planned and its drops are placed; `None` when there is nothing
    /// to drop or the planner refused (then nothing is emitted).
    pub(crate) plan: Option<DropPlan<'tcx>>,
    /// Why no drop was placed — the planner refused the body, or placement failed and was
    /// reverted — for the disclosure.
    pub(crate) refused: Option<String>,
    /// The parameters' trust-ir types, by `thir.params` index.
    pub(crate) param_tys: Vec<Ty>,
    /// Exits whose hook fired, with how many times (a lowering may lower one exit twice, on
    /// two paths).
    fired: BTreeMap<ExitKey, usize>,
    /// Trust (step 2 increment 4b residuals): the block each firing of an exit's hook placed
    /// its drops in, so `finish_drops` can refuse an exit placed twice on ONE path.
    fired_at: BTreeMap<ExitKey, Vec<trust_ir::BlockId>>,
    /// The spill slot of each root (an entry-block `Alloca`), once allocated.
    slots: BTreeMap<usize, (ValueId, Ty)>,
    /// `Inst::Drop` nodes emitted.
    pub(crate) emitted: usize,
    /// `Inst::Drop` nodes the plan says the fired hooks must emit.
    pub(crate) expected: usize,
    /// A placement failure (a root's value or type was unavailable at an exit).
    pub(crate) failed: Option<String>,
    /// Trust (step 2 increment 4c): the [`DropSite`] of every `Inst::Drop` placed, in order.
    sites: Vec<DropSite>,
    /// Trust (step 2 increment 4b residuals): THIR expression (`ExprId::as_u32`) → the
    /// temporary root whose value its lowering produces (from the plan).
    temp_exprs: BTreeMap<u32, usize>,
    /// The value the lowering produced for each temporary root (the last one recorded).
    temp_values: BTreeMap<usize, ValueId>,
    /// `Borrow` expression (`ExprId::as_u32`) → the temporary root it borrows whole.
    temp_borrows: BTreeMap<u32, usize>,
    /// The pointer the lowering produced for each whole-borrowed temporary's borrow.
    temp_ptrs: BTreeMap<usize, ValueId>,
    /// Whole-object homes for temporaries borrowed through an interior field.
    /// The reference points inside this slot; destruction still uses the root.
    partial_homes: BTreeMap<usize, (ValueId, ValueId, Ty)>,
    /// The pointer and the stored type of the drop-and-replace through a pointer whose hook is
    /// firing (`*p = v`): the old pointee is dropped through exactly the pointer the store uses.
    replace_through: Option<(ValueId, Ty)>,
    /// Trust (4b residuals review, 2026-10-08): every whole-borrowed temporary dropped through
    /// the home [`borrowed_temp_home`] proved — `(value, slot, type, home)` — for `finish_drops`
    /// to prove again on the finished function (a use lowered after the drop fails it).
    homes: Vec<(ValueId, ValueId, Ty, ValueId)>,
    /// Owned whole or field-borrowed temporaries materialized at their first shared borrow.
    /// Each needs an exact finished-function home proof and a placed drop.
    /// A failed placement must also refuse the borrow itself.
    owned_shared_temps: Vec<(ValueId, ValueId, Ty)>,
    /// The condition (`ExprId::as_u32`) of the `if` whose branches `lower_if` is about to lower:
    /// `lower_if_value` takes it at its start and fires `CondThen` / `CondElse` with it.
    pub(crate) if_cond: Option<u32>,
}

impl<'a, 'tcx> crate::LowerCx<'a, 'tcx> {
    /// Plan the body's drops. Called once by `lower_fn` after the parameters are mapped and
    /// before the body is lowered. The instance lane is skipped: its frozen gate
    /// (`instance_admission::thir_instance_needs_drop`) refuses every drop-bearing instance.
    pub(crate) fn plan_drops(&mut self, def: LocalDefId, body: ExprId, param_tys: &[Ty]) {
        // Design §8, on every lane: a body that can observe post-panic state is refused on the
        // trust-ir path while the build unwinds (under `panic=abort` a panic never returns to it).
        if self.tcx.sess.panic_strategy().unwinds() {
            if let Some(site) = catch_unwind_site(self.tcx, self.thir) {
                self.unsupported
                    .push((format!("{site:?}"), "Unwind(catch_unwind under panic=unwind)"));
            }
        }
        if self.mono_args.is_some() {
            return;
        }
        self.drops.param_tys = param_tys.to_vec();
        match plan_body(self.tcx, def, self.thir, body) {
            Ok(plan) => {
                self.drops.temp_exprs = plan.as_ref().map(|p| p.temp_exprs()).unwrap_or_default();
                self.drops.temp_borrows =
                    plan.as_ref().map(|p| p.temp_borrows()).unwrap_or_default();
                self.drops.plan = plan;
            }
            Err(reason) => self.drops.refused = Some(reason.to_string()),
        }
    }

    /// Trust (step 2 increment 4b residuals): the recording hook `lower_expr` calls with every
    /// expression's lowered value — a temporary root's value is the value of the expression
    /// rustc materializes into the temporary. The last value recorded wins; a placement whose
    /// value does not reach its drop is refused by `finish_drops`' validation.
    #[inline]
    pub(crate) fn record_drop_value(&mut self, id: ExprId, value: Option<ValueId>) {
        if self.drops.temp_exprs.is_empty() {
            return;
        }
        let Some(v) = value else { return };
        if let Some(&r) = self.drops.temp_exprs.get(&id.as_u32()) {
            self.drops.temp_values.insert(r, v);
        }
        if let Some(&r) = self.drops.temp_borrows.get(&id.as_u32()) {
            self.drops.temp_ptrs.insert(r, v);
        }
    }

    /// Trust (step 2 increment 4b residuals): the recording hook of a lane that materializes the
    /// rvalue `rvalue` in a fresh slot of its own and hands the slot to a borrow
    /// (`try_lower_mut_call_temp_slot`: `&mut f()`, also under THIR's reborrow wrapper, where
    /// the `Borrow` expression itself is never lowered): that slot IS the address the borrow
    /// of the temporary sees.
    pub(crate) fn record_drop_borrow_slot(&mut self, rvalue: ExprId, slot: ValueId) {
        let Some(&r) = self.drops.temp_exprs.get(&rvalue.as_u32()) else { return };
        let borrowed = self.drops.plan.as_ref().is_some_and(|p| {
            matches!(&p.roots[r].kind, RootKind::Temp(TempRoot { borrow: Some(_), .. }))
        });
        if borrowed {
            self.drops.temp_ptrs.insert(r, slot);
        }
    }

    /// The hook every exit's lowering calls right before it seals (or, for `Replace`, right
    /// before the new value is bound): emit the edge's `Static` drops.
    pub(crate) fn emit_planned_drops(&mut self, key: ExitKey) {
        let Some(plan) = self.drops.plan.as_ref() else { return };
        if self.sealed {
            return;
        }
        let roots = plan.plan.emission(key);
        *self.drops.fired.entry(key).or_insert(0) += 1;
        if !roots.is_empty() {
            self.drops.fired_at.entry(key).or_default().push(self.cur_id);
        }
        self.drops.expected += roots.len();
        if mutation() == Some("skip-emission") {
            return;
        }
        for r in roots {
            if let Err(why) = self.emit_one_drop(r, key) {
                self.drops.failed.get_or_insert(why);
            }
        }
    }

    /// Trust (step 2 increment 4b residuals): [`Self::emit_planned_drops`] for a
    /// drop-and-replace through a pointer (`*p = v`): the old pointee is dropped through `ptr`,
    /// the pointer the store of the new value goes through, at the store's type `ty`.
    pub(crate) fn emit_planned_drops_through(&mut self, key: ExitKey, ptr: ValueId, ty: Ty) {
        if self.drops.plan.is_none() {
            return;
        }
        self.drops.replace_through = Some((ptr, ty));
        self.emit_planned_drops(key);
        self.drops.replace_through = None;
    }

    fn emit_one_drop(&mut self, r: usize, key: ExitKey) -> Result<(), String> {
        let plan = self.drops.plan.as_ref().ok_or_else(|| "no plan".to_string())?;
        let root = plan.roots[r].clone();
        let span = plan.span_of(r, key);
        let (destructor, freeze) = (plan.destructor[r], plan.freeze[r]);
        // The planner defers this only for named locals. Actual storage is the
        // placement witness; a promotion request cannot authorize a fresh spill.
        let required_home = root.shared_borrowed && (destructor || !freeze);
        match &root.kind {
            RootKind::Local => {}
            RootKind::Pointee => {
                let (ptr, ty) = self.drops.replace_through.clone().ok_or_else(|| {
                    "a drop-and-replace through a pointer was lowered without its pointer"
                        .to_string()
                })?;
                if let Some(why) = unspellable_drop_type(&ty, &self.pending_tys) {
                    return Err(why);
                }
                self.record_drop_site(ptr, &root);
                if mutation() == Some("pointee-twice") {
                    // TEST-ONLY: the old pointee dropped twice.
                    self.push_drop_node(ty.clone(), ptr, span);
                }
                self.push_drop_node(ty, ptr, span);
                return Ok(());
            }
            RootKind::Temp(t) => {
                return self.emit_temp_drop(r, &root, t, destructor, freeze, span);
            }
            RootKind::Path => return Err("a move path's slot is not a drop".to_string()),
        }
        // The value and its trust-ir type.
        let (value, ty) = match (root.var, root.param) {
            (Some(var), _) if self.is_promoted(var) => {
                let slot = self
                    .promoted_slot(var)
                    .ok_or_else(|| format!("promoted root {var:?} has no slot"))?;
                let ty = self
                    .promoted_ty(var)
                    .ok_or_else(|| format!("promoted root {var:?} has no type"))?;
                // The same v55 rule as the SSA path below: a promoted local's slot can be
                // spelled trivially droppable too (`let t = (fd, Some((g(fd), Vec::new())));
                // &t.0` promotes `t` as `(i32, bool)`, its `Option` collapsed to the
                // discriminant), and a `Drop` of that spelling fails the whole crate module.
                if let Some(why) = unspellable_drop_type(&ty, &self.pending_tys) {
                    return Err(why);
                }
                self.record_drop_site(slot, &root);
                self.push_drop_node(ty, slot, span);
                return Ok(());
            }
            (Some(var), _) => {
                if required_home {
                    return Err("shared-borrowed root has no promoted home".to_string());
                }
                let v = self
                    .local_value(var)
                    .ok_or_else(|| format!("root {var:?} has no value at {key:?}"))?;
                let t = self
                    .local_ty(var)
                    .ok_or_else(|| format!("root {var:?} has no type at {key:?}"))?;
                (v, t)
            }
            (None, Some(i)) => {
                if required_home {
                    return Err("shared-borrowed parameter has no promoted home".to_string());
                }
                let t = self
                    .drops
                    .param_tys
                    .get(i)
                    .cloned()
                    .ok_or_else(|| format!("parameter {i} has no type"))?;
                (ValueId::new(i as u32), t)
            }
            (None, None) => return Err("root with neither a binding nor a parameter".to_string()),
        };
        if self.carrier_spelling(value).is_some() {
            return Err(format!("root value {value:?} is an opaque carrier"));
        }
        if matches!(ty, Ty::Unit) && !self.is_drop_free_zst(root.ty) {
            // `Ty::Unit` is also the fail-closed placeholder: a drop of `()` for a real value
            // would name nothing.
            return Err("root spelled as a `()` placeholder".to_string());
        }
        // Trust (trust-ir v55, amendment D §20 rule 5a; the validator's `NonCanonicalDrop`): a
        // drop of a trivially droppable type does nothing and is spelled by ABSENCE. A root is
        // planned because its Rust type needs a drop, so a root whose trust-ir spelling is
        // trivially droppable (an `Option` collapsed to its discriminant `bool`, a ZST spelled
        // `()`) has lost the destructor its drop runs: no `Inst::Drop` of that spelling can say
        // so, and one that tried would fail the whole crate module's validation. The placement
        // fails, and the body's drops are elided all or nothing (`finish_drops`). The rule is
        // `unspellable_drop_type`, shared with the promoted-slot path above.
        if let Some(why) = unspellable_drop_type(&ty, &self.pending_tys) {
            return Err(why);
        }
        self.spill_and_drop(r, &root, value, ty, span)
    }

    /// A drop of `root` through its fresh entry slot holding `value`: the `Store`, then the
    /// `Inst::Drop` through the slot.
    fn spill_and_drop(
        &mut self,
        r: usize,
        root: &Root<'tcx>,
        value: ValueId,
        ty: Ty,
        span: Span,
    ) -> Result<(), String> {
        let slot = match self.drops.slots.get(&r) {
            Some((s, t)) if *t == ty => *s,
            Some(_) => return Err("root spelled with two trust-ir types".to_string()),
            None => {
                let s = self.alloc_entry_slot(ty.clone());
                self.drops.slots.insert(r, (s, ty.clone()));
                s
            }
        };
        let saved = self.cur_span;
        self.cur_span = self.to_source_span(span).or(saved);
        self.push_node(InstrNode::new(Inst::Store {
            ty: ty.clone(),
            ptr: slot,
            value,
            volatile: false,
            align: None,
        }));
        self.cur_span = saved;
        self.record_drop_site(slot, root);
        self.push_drop_node(ty, slot, span);
        Ok(())
    }

    /// Trust (step 2 increment 4b residuals): the drop of a temporary.
    ///
    /// * A temporary the program borrows WHOLE (`&f()`, an autoref receiver) is dropped through
    ///   its object's HOME: the slot the borrow's lowering produced (an `Alloca`; none recorded,
    ///   or not a slot, refuses the placement), or the slot a lane moved the whole value into,
    ///   PROVED by [`borrowed_temp_home`] to be the only way the program reaches the object (and
    ///   proved again on the finished function by `finish_drops`). Unproved, a shared borrow of
    ///   a `Freeze` value whose glue only releases memory is still dropped through the borrow's
    ///   slot (every copy is the same drop); any other refuses the placement.
    /// * Otherwise its VALUE is the one the lowering produced for the expression rustc
    ///   materializes into the temporary (`record_drop_value`), dropped through a fresh slot
    ///   holding the same bytes — only when nothing else observes the temporary's address (or,
    ///   for a shared borrow of a part of it, when its type is `Freeze` and its glue only
    ///   releases memory: the 4b root rule). A temporary mutably borrowed in part refuses the
    ///   placement.
    fn emit_temp_drop(
        &mut self,
        r: usize,
        root: &Root<'tcx>,
        temp: &TempRoot,
        destructor: bool,
        freeze: bool,
        span: Span,
    ) -> Result<(), String> {
        if let Some((value, slot, ty)) = self.drops.partial_homes.get(&r).cloned() {
            if self.drops.temp_values.get(&r) != Some(&value) {
                return Err("the partially borrowed temporary's value changed".to_string());
            }
            if let Some(why) = unspellable_drop_type(&ty, &self.pending_tys) {
                return Err(why);
            }
            let nodes: Vec<&InstrNode> =
                self.blocks.iter().flat_map(|b| b.body.iter()).chain(self.cur.iter()).collect();
            let home = borrowed_temp_home(&nodes, value, slot, &ty).map_err(|why| {
                format!("a partially borrowed temporary's home is unproved: {why}")
            })?;
            self.drops.homes.push((value, slot, ty.clone(), home));
            self.record_drop_site(home, root);
            self.push_drop_node(ty, home, span);
            return Ok(());
        }
        if temp.borrow.is_some() {
            let ptr = *self.drops.temp_ptrs.get(&r).ok_or_else(|| {
                "a borrowed temporary's borrow was not lowered through `lower_expr`".to_string()
            })?;
            let ty = self
                .slot_ty(ptr)
                .ok_or_else(|| "a borrowed temporary's pointer is not a slot".to_string())?;
            if let Some(why) = unspellable_drop_type(&ty, &self.pending_tys) {
                return Err(why);
            }
            // Trust (4b residuals review, 2026-10-08): the drop goes through the memory the
            // object lives in when the drop runs, PROVED to be the only way the program reaches
            // it (`borrowed_temp_home`): the borrow's slot, or the slot a lowering lane moved the
            // whole value into (the shared-borrow snapshot lane's `f(&g())` copy, which the
            // callee receives). Without the proof the slot's bytes may be a stale copy at another
            // address — admitted only for a shared borrow under the 4b root rule (content cannot
            // change through the borrow, glue only releases memory: every copy is the same drop).
            if mutation() == Some("temp-borrow-slot") {
                // TEST-ONLY: recreate a genuinely distinct, stale object. A
                // reborrow can now forward the original slot to the callee,
                // so dropping `ptr` itself would leave this mutation inert.
                let value = *self.drops.temp_values.get(&r).ok_or_else(|| {
                    "the borrowed temporary's value was not lowered through `lower_expr`"
                        .to_string()
                })?;
                let stale = self.fresh();
                self.push_node(
                    InstrNode::new(Inst::Alloca { ty: ty.clone(), count: None, align: None })
                        .with_result(stale),
                );
                self.push_node(InstrNode::new(Inst::Store {
                    ty: ty.clone(),
                    ptr: stale,
                    value,
                    volatile: false,
                    align: None,
                }));
                self.record_drop_site(stale, root);
                self.push_drop_node(ty, stale, span);
                return Ok(());
            }
            let proved = match self.drops.temp_values.get(&r) {
                Some(&value) => {
                    let nodes: Vec<&InstrNode> = self
                        .blocks
                        .iter()
                        .flat_map(|b| b.body.iter())
                        .chain(self.cur.iter())
                        .collect();
                    borrowed_temp_home(&nodes, value, ptr, &ty).map(|home| (value, home))
                }
                None => Err("the borrowed temporary's value was not lowered through `lower_expr`"),
            };
            let at = match proved {
                Ok((value, home)) => {
                    self.drops.homes.push((value, ptr, ty.clone(), home));
                    home
                }
                Err(_) if temp.observed == Observed::Shared && !destructor && freeze => ptr,
                Err(why) => {
                    return Err(format!("a borrowed temporary's object is unproved: {why}"));
                }
            };
            self.record_drop_site(at, root);
            self.push_drop_node(ty, at, span);
            return Ok(());
        }
        match temp.observed {
            Observed::No => {}
            Observed::Shared if !destructor && freeze => {}
            Observed::Shared => {
                return Err(
                    "a temporary borrowed in part whose glue could observe its address".to_string()
                );
            }
            Observed::Mut => {
                return Err("a temporary mutably borrowed in part".to_string());
            }
        }
        let value = *self.drops.temp_values.get(&r).ok_or_else(|| {
            "a temporary's value was not lowered through `lower_expr`".to_string()
        })?;
        if self.carrier_spelling(value).is_some() {
            return Err(format!("temporary value {value:?} is an opaque carrier"));
        }
        // The temporary's trust-ir type: mapping it emits nothing, and a mapping that would
        // refuse is a probe whose tags are discarded (the placement fails instead).
        let mark = self.attempt_mark();
        let before = self.unsupported.len();
        let ty = self.map_ty(root.ty);
        if self.unsupported.len() != before {
            self.discard_probe(mark, "drops: a temporary's type");
            return Err(format!("the temporary's type `{}` does not map", root.ty));
        }
        if matches!(ty, Ty::Unit) && !self.is_drop_free_zst(root.ty) {
            return Err("temporary spelled as a `()` placeholder".to_string());
        }
        if let Some(why) = unspellable_drop_type(&ty, &self.pending_tys) {
            return Err(why);
        }
        self.spill_and_drop(r, root, value, ty, span)
    }

    /// The type of the slot `ptr`, when `ptr` is the result of an `Alloca` the lowering emitted.
    fn slot_ty(&self, ptr: ValueId) -> Option<Ty> {
        self.blocks.iter().flat_map(|b| b.body.iter()).chain(self.cur.iter()).find_map(|n| match &n
            .inst
        {
            Inst::Alloca { ty, count: None, .. } if n.results.first() == Some(&ptr) => {
                Some(ty.clone())
            }
            _ => None,
        })
    }

    /// Trust (step 2 increment 4c): the [`DropSite`] of a drop of `root` through `slot`.
    fn record_drop_site(&mut self, slot: ValueId, root: &Root<'tcx>) {
        let ty = self.tcx.type_id_hash(root.ty).as_u128();
        self.drops.sites.push(DropSite { ptr: slot.index(), ty, identity: root.identity });
    }

    fn push_drop_node(&mut self, ty: Ty, ptr: ValueId, span: Span) {
        let saved = self.cur_span;
        self.cur_span = self.to_source_span(span).or(saved);
        self.push_node(InstrNode::new(Inst::Drop { ty, ptr }));
        self.cur_span = saved;
        self.drops.emitted += 1;
        self.contains_call = true;
    }

    /// An `Alloca` of `ty` in the ENTRY block (so a drop inside a loop reuses one slot): pushed
    /// into the open block when it is the entry, else inserted before the sealed entry block's
    /// terminator. An `Alloca` has no operand, so it dominates every use from there.
    fn alloc_entry_slot(&mut self, ty: Ty) -> ValueId {
        let slot = self.fresh();
        let entry = trust_ir::BlockId::new(0);
        let mut node =
            InstrNode::new(Inst::Alloca { ty, count: None, align: None }).with_result(slot);
        if self.cur_id == entry && !self.sealed {
            self.push_node(node);
            return slot;
        }
        node.span = None;
        node.scope = Some(0);
        if let Some(i) = self.blocks.iter().position(|b| b.id == entry) {
            let body = &mut self.blocks[i].body;
            let at = body.len().saturating_sub(1);
            body.insert(at, node);
        } else {
            // No entry block yet (impossible after `lower_fn` started it); keep the slot in the
            // current block so the module stays well-formed, and fail the placement.
            self.push_node(node);
            self.drops.failed.get_or_insert_with(|| "entry block missing".to_string());
        }
        slot
    }

    /// The end of the body's lowering: the placement tripwire. Returns the claim for the gate,
    /// or `None` when no drop was placed.
    ///
    /// ALL OR NOTHING. If an exit the plan needs was not lowered through its hook (a lowering
    /// lane that seals an exit itself), an exit's drops were placed twice on one path (a lane
    /// that lowered the same exit twice in sequence), a drop could not be placed (the root's
    /// value is an opaque carrier, spelled as the `()` placeholder, or spelled as a trivially
    /// droppable type that carries no destructor; a temporary's value or slot is unavailable),
    /// or the placed module validates worse than the same module without its drops (a
    /// placed operand that does not reach its drop), every node this module placed — each
    /// `Inst::Drop`, and each spill slot's `Alloca` and `Store` — is removed from `module`, and
    /// the body is left exactly as the producer lowers it without drops: its drops elided, which
    /// the effect-conservation gate refuses as `abstracted(drop)`, naming why. A partially placed
    /// body never leaves this function.
    pub(crate) fn finish_drops(&mut self, module: &mut trust_ir::Module) -> Option<DropClaim> {
        let Some(plan) = self.drops.plan.as_ref() else {
            if !self.drops.owned_shared_temps.is_empty() {
                self.unsupported
                    .push(("body".to_string(), "Borrow(owned temporary home unproved)"));
            }
            return None;
        };
        let required = plan.plan.required();
        let missed: Vec<ExitKey> =
            required.iter().filter(|k| !self.drops.fired.contains_key(k)).copied().collect();
        let slots: std::collections::BTreeSet<ValueId> =
            self.drops.slots.values().map(|(s, _)| *s).collect();
        let mut failure = if !missed.is_empty() {
            Some(format!("an exit was not lowered through the drop hook: {missed:?}"))
        } else {
            self.drops.failed.as_ref().map(|why| format!("placement failed: {why}"))
        };
        if failure.is_none() {
            failure = placed_twice_on_one_path(module, &self.drops.fired_at)
                .map(|k| format!("an exit's drops were placed twice on one path: {k:?}"));
        }
        if failure.is_none() {
            failure = homes_still_proved(module, &self.drops.homes, &self.drops.owned_shared_temps);
        }
        if failure.is_none() && self.drops.emitted > 0 {
            failure = validation_regression(module, &slots);
        }
        if let Some(why) = failure {
            // Drop elision cannot turn an unproved owned object into an admitted snapshot.
            // Keep this refusal even for callers that do not demand placed drops themselves.
            if !self.drops.owned_shared_temps.is_empty() {
                self.unsupported
                    .push(("body".to_string(), "Borrow(owned temporary home unproved)"));
            }
            strip_placed(module, &slots);
            self.drops.plan = None;
            self.drops.refused = Some(why);
            self.drops.sites.clear();
            return None;
        }
        // The claim's count is what the PLAN says the fired hooks place, not what the emitter
        // counted: the gate compares it with the `Inst::Drop`s the module carries, so an emitter
        // that placed more or fewer than planned is refused there (`not-conserved(drop)`).
        let mut claim = plan.claim(self.tcx, self.drops.expected);
        claim.sites = std::mem::take(&mut self.drops.sites);
        Some(claim)
    }
}

/// Trust (4b residuals review, 2026-10-08): where a WHOLE-BORROWED temporary's object lives
/// when its drop runs, and the proof that the program reaches it nowhere else (DROPS-RES-1).
///
/// The borrow's lowering materializes the temporary in `slot` (an `Alloca` of `ty`) with one
/// `Store` of `value`, the temporary's lowered value. A lowering lane may hand the consumer a
/// COPY: the shared-borrow snapshot lane lowers `f(&g())`'s reborrow `&*&g()` as `load` +
/// `alloca` + `store`, so the callee mutates (a `Cell`, a `RefCell`) or observes the address of
/// the copy, and a drop through `slot` would run the destructor on stale bytes at another address
/// — the review's `cell_temp` (a destructor closing a stale descriptor) and `refcell_temp` (a
/// double free and a leak), both accepted by strict on the first cut. So:
///
/// * a whole-value MOVE the lowering made — `slot`'s only uses are its one initializing store and
///   one `load ty`, whose only use is a store into a fresh `Alloca` of `ty` — moves the object to
///   that `Alloca` (nothing observed the old slot, which is dead), and the walk follows it;
/// * the final home may then be used only by stores into it, drops through it, call arguments
///   (the callee receives exactly this address), interior addresses (`GEP`) used the same way,
///   and loads whose result is only READ: never stored, passed on or returned whole, merged into
///   an aggregate, a `select` or a block argument — no second copy of any part of the object
///   exists that the program could change or take the address of;
/// * `value` may be stored only into `slot`, exactly once, and otherwise only read.
///
/// `Err(why)` for any other use. `nodes` is every node of the function. PURE.
pub(crate) fn borrowed_temp_home(
    nodes: &[&InstrNode],
    value: ValueId,
    slot: ValueId,
    ty: &Ty,
) -> Result<ValueId, &'static str> {
    let g = UseGraph::new(nodes);
    // The temporary's value: stored into its slot once, otherwise only read.
    let mut init = 0;
    for &i in g.users(value) {
        match &nodes[i].inst {
            Inst::Store { ptr, value: v, .. } if *ptr == slot && *v == value => init += 1,
            _ => g.read(i, value, true, 0)?,
        }
    }
    if init != 1 {
        return Err("the temporary's value does not initialize its slot exactly once");
    }
    // Follow the whole-value moves.
    let mut home = slot;
    for _ in 0..8 {
        let (mut stores, mut load, mut other) = (0, None, false);
        for &i in g.users(home) {
            match &nodes[i].inst {
                Inst::Store { ptr, value: v, .. } if *ptr == home && *v != home => stores += 1,
                Inst::Load { ptr, ty: t, .. } if *ptr == home && t == ty && load.is_none() => {
                    load = Some(i)
                }
                _ => other = true,
            }
        }
        let (false, 1, Some(li)) = (other, stores, load) else { break };
        let Some(&l) = nodes[li].results.first() else { break };
        let &[si] = g.users(l) else { break };
        let Inst::Store { ptr: next, value: v, .. } = &nodes[si].inst else { break };
        if *v != l || *next == home {
            break;
        }
        match g.def.get(next).map(|&d| &nodes[d].inst) {
            Some(Inst::Alloca { ty: t, count: None, .. }) if t == ty => home = *next,
            _ => break,
        }
    }
    g.addr(home, Some(ty), 0)?;
    Ok(home)
}

/// The use graph [`borrowed_temp_home`] walks: each value's users and definer, by node index.
struct UseGraph<'a, 'n> {
    nodes: &'a [&'n InstrNode],
    uses: std::collections::HashMap<ValueId, Vec<usize>>,
    def: std::collections::HashMap<ValueId, usize>,
}

impl<'a, 'n> UseGraph<'a, 'n> {
    const COPY: &'static str = "a copy of (part of) the borrowed temporary outlives the read";
    const DEPTH: usize = 16;

    fn new(nodes: &'a [&'n InstrNode]) -> Self {
        let mut uses: std::collections::HashMap<ValueId, Vec<usize>> = Default::default();
        let mut def: std::collections::HashMap<ValueId, usize> = Default::default();
        for (i, n) in nodes.iter().enumerate() {
            n.inst.visit_value_operands(|v| {
                let u = uses.entry(v).or_default();
                if u.last() != Some(&i) {
                    u.push(i);
                }
            });
            for r in &n.results {
                def.insert(*r, i);
            }
        }
        UseGraph { nodes, uses, def }
    }

    fn users(&self, v: ValueId) -> &[usize] {
        self.uses.get(&v).map_or(&[][..], |u| u.as_slice())
    }

    /// The use at node `i` of `x` — a value read out of the object, all of it when `whole` —
    /// only READS it: a field or element extracted (and itself only read), a computation, a
    /// branch condition, or (a part, never the whole) a by-value argument or return value.
    fn read(&self, i: usize, x: ValueId, whole: bool, depth: usize) -> Result<(), &'static str> {
        if depth > Self::DEPTH {
            return Err(Self::COPY);
        }
        let n = self.nodes[i];
        let through = || -> Result<(), &'static str> {
            for r in &n.results {
                for &j in self.users(*r) {
                    self.read(j, *r, false, depth + 1)?;
                }
            }
            Ok(())
        };
        match &n.inst {
            Inst::ExtractField { aggregate, .. } if *aggregate == x => through(),
            Inst::ExtractElement { array, index, .. } if *array == x && *index != x => through(),
            Inst::Cast { .. } if !whole => through(),
            Inst::BinOp { .. }
            | Inst::UnOp { .. }
            | Inst::ICmp { .. }
            | Inst::FCmp { .. }
            | Inst::Overflow { .. }
            | Inst::Assert { .. }
            | Inst::Assume { .. }
                if !whole =>
            {
                Ok(())
            }
            Inst::CondBr { cond, then_args, else_args, .. }
                if *cond == x && !then_args.contains(&x) && !else_args.contains(&x) =>
            {
                Ok(())
            }
            Inst::Return { .. } | Inst::Call { .. } | Inst::CallCannotUnwind { .. } if !whole => {
                Ok(())
            }
            _ => Err(Self::COPY),
        }
    }

    /// Every use of the address `p` — the home (`ty` is its type) or an interior address derived
    /// from it — keeps the program on the object itself.
    fn addr(&self, p: ValueId, ty: Option<&Ty>, depth: usize) -> Result<(), &'static str> {
        if depth > Self::DEPTH {
            return Err("the borrowed temporary's address is projected too deep to follow");
        }
        for &i in self.users(p) {
            let n = self.nodes[i];
            match &n.inst {
                Inst::Store { ptr, value, .. } if *ptr == p && *value != p => {}
                Inst::Drop { ptr, .. } if *ptr == p && ty.is_some() => {}
                Inst::Call { .. } | Inst::CallCannotUnwind { .. } => {}
                Inst::CallIndirect { callee, .. } if *callee != p => {}
                Inst::GEP { base, indices, .. } if *base == p && !indices.contains(&p) => {
                    for r in &n.results {
                        self.addr(*r, None, depth + 1)?;
                    }
                }
                Inst::Load { ptr, ty: t, .. } if *ptr == p => {
                    let whole = ty.is_some_and(|ty| ty == t);
                    for r in &n.results {
                        for &j in self.users(*r) {
                            self.read(j, *r, whole, 0)?;
                        }
                    }
                }
                _ => {
                    return Err(
                        "the borrowed temporary's address flows where the placement cannot follow it",
                    );
                }
            }
        }
        Ok(())
    }
}

/// [`borrowed_temp_home`] again for every proved home, on the FINISHED function (the one that
/// drops through it): a use lowered after the drop's hook fired, or a home that moved, fails the
/// placement. `Some(why)` on the first that does not hold.
fn homes_still_proved(
    module: &trust_ir::Module,
    homes: &[(ValueId, ValueId, Ty, ValueId)],
    owned_shared_temps: &[(ValueId, ValueId, Ty)],
) -> Option<String> {
    // Every owned materialization must have its own exact proof. A proof for another
    // value, slot or type cannot authorize a non-Freeze borrow missing from this ledger.
    for (value, slot, ty) in owned_shared_temps {
        if !homes.iter().any(|(v, s, t, _)| v == value && s == slot && t == ty) {
            return Some(
                "an owned shared temporary has no placed drop with a proved home".to_string(),
            );
        }
    }
    for (value, slot, ty, home) in homes {
        let Some(f) = module.functions.iter().find(|f| {
            f.blocks
                .iter()
                .flat_map(|b| b.body.iter())
                .any(|n| matches!(&n.inst, Inst::Drop { ptr, .. } if ptr == home))
        }) else {
            return Some("a borrowed temporary's drop is not in the module".to_string());
        };
        let nodes: Vec<&InstrNode> = f.blocks.iter().flat_map(|b| b.body.iter()).collect();
        match borrowed_temp_home(&nodes, *value, *slot, ty) {
            Ok(h) if h == *home => {}
            Ok(_) => return Some("a borrowed temporary's object moved after its drop".to_string()),
            Err(why) => return Some(format!("a borrowed temporary's object is unproved: {why}")),
        }
    }
    None
}

/// Remove every node the placement put in `module`: each `Inst::Drop`, and each spill slot's
/// `Alloca` and `Store`.
fn strip_placed(module: &mut trust_ir::Module, slots: &std::collections::BTreeSet<ValueId>) {
    for f in &mut module.functions {
        for b in &mut f.blocks {
            b.body.retain(|n| match &n.inst {
                Inst::Drop { .. } => false,
                Inst::Alloca { .. } => !n.results.first().is_some_and(|r| slots.contains(r)),
                Inst::Store { ptr, .. } => !slots.contains(ptr),
                _ => true,
            });
        }
    }
}

/// Trust (step 2 increment 4b residuals): does the placed module validate WORSE than the same
/// module with the placement removed? An operand the placement used that does not reach its
/// drop (a temporary's value lowered on another path), or a spelling the validator refuses,
/// would otherwise fail the whole crate module. `Some(the first new error)` when it does.
fn validation_regression(
    module: &trust_ir::Module,
    slots: &std::collections::BTreeSet<ValueId>,
) -> Option<String> {
    let with = trust_ir_build::validate_module(module);
    if with.is_empty() {
        return None;
    }
    let mut stripped = module.clone();
    strip_placed(&mut stripped, slots);
    let without = trust_ir_build::validate_module(&stripped);
    new_validation_error(&with, &without)
        .map(|first| format!("the placed drops make the module invalid: {first}"))
}

/// Trust (4b residuals review, 2026-10-08): the first error `with` carries more often than
/// `without` (a MULTISET difference of the rendered errors, not a count: one new error next to
/// one the placement happened to remove is still a new error). PURE.
fn new_validation_error<E: std::fmt::Debug>(with: &[E], without: &[E]) -> Option<String> {
    let mut left: BTreeMap<String, usize> = BTreeMap::new();
    for e in without {
        *left.entry(format!("{e:?}")).or_insert(0) += 1;
    }
    with.iter().map(|e| format!("{e:?}")).find(|e| match left.get_mut(e) {
        Some(n) if *n > 0 => {
            *n -= 1;
            false
        }
        _ => true,
    })
}

/// Trust (step 2 increment 4b residuals): the first exit whose hook placed drops in two blocks
/// of which one reaches the other along forward edges (or twice in one block) — one execution
/// would run that exit's drops twice. A lane may lower one exit twice on two DISJOINT paths
/// (an or-pattern arm, a duplicated tail); it may not lower it twice in sequence. Back edges
/// (an edge to a block on the depth-first stack) are excluded, so a loop that runs one placed
/// exit once per iteration is not a repeat. PURE.
pub(crate) fn placed_twice_on_one_path(
    module: &trust_ir::Module,
    fired_at: &BTreeMap<ExitKey, Vec<trust_ir::BlockId>>,
) -> Option<ExitKey> {
    let repeated: Vec<(&ExitKey, &Vec<trust_ir::BlockId>)> =
        fired_at.iter().filter(|(_, blocks)| blocks.len() > 1).collect();
    if repeated.is_empty() {
        return None;
    }
    let f = module.functions.iter().find(|f| function_has_drop(f))?;
    let index: BTreeMap<trust_ir::BlockId, usize> =
        f.blocks.iter().enumerate().map(|(i, b)| (b.id, i)).collect();
    let succ: Vec<Vec<usize>> = f
        .blocks
        .iter()
        .map(|b| {
            b.body
                .last()
                .map(|n| {
                    n.inst
                        .successor_edges()
                        .iter()
                        .filter_map(|e| index.get(&e.target))
                        .copied()
                        .collect()
                })
                .unwrap_or_default()
        })
        .collect();
    // Forward edges: drop every edge into a block on the depth-first stack.
    let n = f.blocks.len();
    let mut forward: Vec<Vec<usize>> = vec![Vec::new(); n];
    let mut state = vec![0u8; n]; // 0 new, 1 on stack, 2 done
    if let Some(&start) = index.get(&f.entry) {
        let mut stack: Vec<(usize, usize)> = vec![(start, 0)];
        state[start] = 1;
        while let Some((b, i)) = stack.pop() {
            if i < succ[b].len() {
                stack.push((b, i + 1));
                let t = succ[b][i];
                match state[t] {
                    0 => {
                        forward[b].push(t);
                        state[t] = 1;
                        stack.push((t, 0));
                    }
                    2 => forward[b].push(t),
                    _ => {} // a back edge
                }
            } else {
                state[b] = 2;
            }
        }
    }
    let reaches = |from: usize, to: usize| {
        let mut seen = vec![false; n];
        let mut stack = vec![from];
        while let Some(b) = stack.pop() {
            for &t in &forward[b] {
                if t == to {
                    return true;
                }
                if !std::mem::replace(&mut seen[t], true) {
                    stack.push(t);
                }
            }
        }
        false
    };
    for (key, blocks) in repeated {
        let idx: Vec<usize> = blocks.iter().filter_map(|b| index.get(b)).copied().collect();
        for (i, a) in idx.iter().enumerate() {
            for b in &idx[i + 1..] {
                if a == b || reaches(*a, *b) || reaches(*b, *a) {
                    return Some(*key);
                }
            }
        }
    }
    None
}

/// Why a drop of a root spelled at `ty` has no canonical trust-ir spelling, or `None` when
/// `Inst::Drop { ty, .. }` is its one spelling. trust-ir v55 (amendment D, SPEC §20 rules 5a
/// and 5b) gives a drop ONE spelling: a drop of a trivially droppable type is spelled by
/// absence, and a drop of a refined type is spelled at its base. `validate_module` refuses any
/// other as `NonCanonicalDrop`, which fails the WHOLE crate module, so `emit_one_drop` asks
/// this on both of its paths (the promoted slot and the SSA value) and fails the placement
/// instead. A root is planned because its Rust type needs a drop, so a trivially droppable
/// spelling has lost the destructor the drop runs. `types` is the body's `types` table
/// (`Ty::Array` element ids index it). PURE.
pub(crate) fn unspellable_drop_type(ty: &Ty, types: &[Ty]) -> Option<String> {
    if ty.is_refine() {
        return Some(format!("root spelled as the refined `{ty}`: a drop is spelled at its base"));
    }
    ty.is_trivially_droppable(types).then(|| {
        format!("root spelled as the trivially droppable `{ty}`, which carries no destructor")
    })
}

/// Does `f` carry an `Inst::Drop`? A body that does is never interpretation-eligible: the
/// reference interpreter refuses the instruction with a `TypeError`, which the interpretation
/// differential would report as a THIR defect (design §1.6). PURE.
pub fn function_has_drop(f: &trust_ir::Function) -> bool {
    f.blocks.iter().flat_map(|b| b.body.iter()).any(|n| matches!(n.inst, Inst::Drop { .. }))
}

/// The forcing rule, as a pure function so it can be pinned: a body is interpretation-eligible
/// only if it carries no `Inst::Drop`.
pub fn drops_force_not_interpretable(contains_call: bool, module_has_drop: bool) -> bool {
    contains_call || module_has_drop
}

#[cfg(test)]
mod tests;
