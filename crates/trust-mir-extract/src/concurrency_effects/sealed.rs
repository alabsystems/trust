// ignore-tidy-file-filelength -- 5322 code lines after the 1.101 sealed-trait port (2026-10-18..19), recorded 2026-10-20; do not grow casually
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
//! Sealed types: a writers check that leans on Rust's own rules.
//!
//! A `Seal` an island declares on a struct `C` of the crate (design
//! 2026-09-29 §3a: a cell whose only write is its join, a stamp only its
//! source mints) says, of safe code:
//!
//! - (A) a field of a live value of `C` changes only while one of the seal's
//!   WRITERS is executing;
//! - (B) a value of `C` is built only in its MAKERS, which are called only
//!   from its `madeBy` fns and are never used as fn values;
//! - (C) for a seal with a writer: a place whose type OWNS a `C` is given a
//!   whole value at most once while its storage lives: not a second time by
//!   an assignment in this crate, and not by code of another crate that this
//!   crate instantiates with such a type (except the seal's `trusts`). (A
//!   sealed type with no writer is a TOKEN: its values never change, and
//!   where one sits is no one's concern.)
//!
//! Unlike the writer census ([`super::writer_origins`]) this check follows no
//! pointer and tells no arm from another. Every condition is read off ONE
//! statement and the types in it, and Rust carries the rest:
//!
//! - PRIVACY. `C` is not reachable from another crate, its fields are not
//!   `pub` and no maker of it can be called from another crate: every body
//!   that can name a field, or call a maker, is one this check reads.
//! - THE BORROW CHECKER. A writer may use a field mutably only in its own
//!   body (no closure), on a place that starts at a `&mut` parameter whose
//!   lifetime is named NOWHERE ELSE in the fn's signature (but on a `&` the
//!   fn hands back), or at a value the body owns. Nothing the fn is handed,
//!   and nothing it hands back, has a type that can hold a `&mut` of that
//!   lifetime, so safe code cannot keep the borrow past the call.
//! - PLAIN FIELDS ([`Checker::plain`]): a `&` writes nothing, nothing
//!   outside `C` shares a field's data, and every write into a field's own
//!   data goes through a `&mut` borrow of a place through the field.
//! - THE COMPILER'S OWN INSTANCES, for (C). Generic code is judged where it
//!   is made concrete ([`Checker::walk`]). What an instance is, and what it
//!   runs, is asked of the compiler and never re-derived: a fn item by
//!   `Instance::try_resolve`, a drop by its drop-glue instance, a `dyn` by
//!   `vtable_entries`, the body of every shim (drop glue, the built-in
//!   `clone`, a fn item called through `Fn`) by `instance_mir`, and what a
//!   body of another crate uses by the monomorphization collector's own
//!   walk (`items_of_instance`, asked as `trust_seal_items_of_instance`,
//!   which in a check build lists a body without MIR where the collector
//!   would stop the build). Review 12 measured the first build, which
//!   re-derived each of these by hand: every false pass it found against
//!   (C) but two was an instance the hand-written walk never read. Review
//!   13 measured the rebuild: what it found was in the rules that had just
//!   been made to refuse less (each is narrowed again below, with the
//!   program that broke it) and in how an optimized body of another crate
//!   is read (a raw copy left as a statement, a pointer given another
//!   type, a fn inlined away: [`Fact::Recast`], [`Fact::Inlined`]).
//!
//! The conditions, by the names the spec gives them:
//!
//! - S1 shape: a struct of this crate with a field and no generic parameter,
//!   no `pub` field, not `Copy`, sealed once; in a crate another can depend
//!   on, the type and its makers are not reachable from outside; the crate
//!   enables no macro-2.0 items and has no `unsafe impl` (but of `Send` and
//!   `Sync`) that a type owning one can meet.
//! - S2 fields: a mutable use of a place that goes through a field of `C`
//!   (assigned, a call's result, mutably borrowed, moved out of through a
//!   pointer) is in a writer's own body, on a place as described above. A
//!   raw borrow of such a place is an error anywhere.
//! - S3 making: a struct expression of `C` is in a maker's own body; `C`'s
//!   constructor fn is never mentioned; no `const` of the crate holds a `C`
//!   in its value (judged where it is defined, by its type as the constant
//!   sees it, and again where it is used at a concrete type). S3': a maker
//!   is mentioned only as the callee of a call, in the own body of a
//!   `madeBy` fn or of a maker (an `async fn`'s too; not a closure or an
//!   `async` block in one, which can be handed on and run anywhere).
//! - S4 no value over another: (a) an assignment whose target's type owns a
//!   `C`, unless the target is a bare local not assigned since its storage
//!   began; a write through a field of a union another field of which owns
//!   one; (b) an instance of a fn that is no body of this crate with a type
//!   that owns one among its type arguments; (c) a body of another crate,
//!   reached with a type of this crate among its type arguments, that does
//!   (a), copies raw memory onto such a place, or gives a pointer to one a
//!   type that no longer says so; (d) a value that owns one handed, behind
//!   a pointer that owns it or can write it, to a `dyn` of a trait of
//!   another crate (or of no trait): code that names no type of this crate
//!   can then replace it. What mentions no type parameter is judged where
//!   it stands, in every body of the crate; what does, at each instance the
//!   crate makes of the body, and where the body stands too, OPEN: what it
//!   names at a type that mentions its parameters is followed as an
//!   instance's is (a fn of this crate or of another, resolved in the body's
//!   own typing environment; a constant; a drop; a vtable's methods), and
//!   judged whatever the parameters stand for ([`Work::open`]). Where the
//!   compiler names no one body (an impl a where-clause or a projection bound
//!   picks), the item is an ABSTRACT impl: unknown code at every type it is
//!   handed ([`Checker::unresolved`]). A crate with a `global_asm!` item is
//!   refused.
//!   A `trusts` entry names a fn, a trait or a static ([`Checker::
//!   trust_item`]); it covers what the fn runs beneath it that it chose, and
//!   a body it did not choose only through the trusts of fns of THAT body's
//!   crate on the way; and a fn reached as a VALUE in a body of a crate
//!   outside the standard library (a fn pointer, a vtable's method), for
//!   what the inputs its caller hands it can reach, only through a trust
//!   that names it ([`Handed::Pointer`]); a `dyn` of a trait of another
//!   crate among those inputs may carry what any coercion handed to such a
//!   `dyn` ([`Checker::dyn_handed`]). S4e counts only what the fn's own
//!   source does with `unsafe`, not what a fn inlined into it does (that
//!   fn is asked as itself: [`Checker::crate_code`]).
//! - S5 plain fields.

use rustc_middle::mir::visit::{MutatingUseContext, NonMutatingUseContext, PlaceContext, Visitor};
use rustc_middle::mono::MonoItem;
use rustc_middle::ty::{InstanceKind, ShimKind, TypeSuperVisitable, TypeVisitable};
use rustc_span::def_id::CrateNum;

use super::*;

/// A seal an island declares on a type of the crate (`Trust.Protocol.Seal`).
#[derive(Clone, Debug)]
pub struct SealDecl {
    /// The declaration's name in the island (`HarnessPolicy.cell`).
    pub name: String,
    /// The sealed type (`PolicyCell`, `order::PolicyCell`).
    pub type_name: String,
    /// The fns that may change a field of a value of it.
    pub writers: Vec<String>,
    /// The fns that may build a value of it.
    pub makers: Vec<String>,
    /// The fns that may call a maker.
    pub made_by: Vec<String>,
    /// The fns of other crates that may be handed a value holding one, and
    /// the traits of other crates a `dyn` of which may hold one.
    pub trusts: Vec<String>,
    /// Where the declaration is.
    pub span: Span,
}

/// A declared seal, with its names resolved.
struct Seal<'a, 'tcx> {
    decl: &'a SealDecl,
    adt: ty::AdtDef<'tcx>,
    writers: Vec<DefId>,
    makers: Vec<DefId>,
    made_by: Vec<DefId>,
    /// The `madeBy` names that name nothing in this build (a test's fn in a
    /// build without tests): they allow nothing.
    absent: Vec<String>,
}

/// Where a statement that builds a value, or calls a maker, is.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Own {
    /// In the body of a fn itself.
    Body,
    /// In the body of an `async fn` itself: it runs once for each call, when
    /// the future the call made is polled.
    AsyncBody,
    /// In a closure, or an `async` block: it can be handed on and run
    /// anywhere, any number of times.
    Closure,
    /// In an inline `const { }` (or another constant in a body): evaluated
    /// once, when the program is compiled, and its one value copied at each
    /// run. (Review 2 of the review-14 build: it was read as a closure, and
    /// the note said it could be handed on and run anywhere.)
    Const,
}

/// What a statement does that a seal has a condition about.
#[derive(Clone, Debug)]
enum Site<'tcx> {
    /// S2: a mutable use of a place through a field of the sealed type.
    /// `refused`: why a writer may not make it either.
    Field { what: &'static str, refused: Option<&'static str> },
    /// S3: a struct expression of the sealed type.
    Build { own: Own },
    /// S3: the sealed type's constructor fn, mentioned.
    Ctor,
    /// S3: a `const` of this crate whose initializer runs this maker.
    /// `holds`: whether the constant's type may hold a value of the sealed
    /// type (`ty`, as the constant sees it).
    Constant { maker: DefId, holds: bool, ty: Ty<'tcx> },
    /// S3': a maker, called (`callee`) or taken as a value.
    Maker { maker: DefId, callee: bool, own: Own },
    /// S4a: a value of a type that owns one, put where one may be; in a body
    /// of another crate when `through` names the fn of it this crate named.
    /// `kept`: the place is one an `async` body keeps across an `.await`.
    /// `cover`: the item whose `trusts` entry would cover it there
    /// ([`Through::cover`]).
    Over { ty: Ty<'tcx>, through: Option<DefId>, kept: bool, cover: Option<DefId> },
    /// S4a: a write through a field of a union another field of which owns
    /// one.
    Union { ty: Ty<'tcx>, through: Option<DefId>, cover: Option<DefId> },
    /// S4b: a fn that is no body of this crate, at a type that owns one.
    /// `value`: reached as a VALUE (a fn pointer, a vtable's method), which
    /// only a trust that names it covers ([`Handed::Pointer`]).
    Foreign { def: DefId, ty: Ty<'tcx>, value: bool },
    /// S4b, in an open reading: an item of THIS crate (a trait's method or
    /// constant whose impl a where-clause picks) where the compiler names no
    /// one body, handed a value of this type, which owns one beyond what the
    /// item's declaration names ([`Checker::unresolved`]).
    Picked { def: DefId, ty: Ty<'tcx> },
    /// S4d: a value of the first type, which owns one, handed behind an
    /// owning pointer to the second, a `dyn` this crate does not define.
    Erased { ty: Ty<'tcx>, to: Ty<'tcx>, through: Option<DefId>, cover: Option<DefId> },
    /// S4c: in a body of another crate, a pointer to a value of the first
    /// type, which owns one, given the second type, which says nothing of
    /// it: what is written through it from then on is not seen.
    Recast { ty: Ty<'tcx>, to: Ty<'tcx>, through: DefId, cover: Option<DefId> },
    /// S4e: a fn of a crate outside the standard library that does what only
    /// `unsafe` code can (`op`) and handles a value of this type, through
    /// which a sealed value can be written.
    Works { def: DefId, ty: Ty<'tcx>, op: &'static str },
    /// S1: a fn this crate declares in an `extern` block as `safe` to call
    /// (no body to read, and not Rust), called.
    Extern { def: DefId },
    /// S1, S5 and the limits of what is read: about the type or the crate.
    Shape(String),
}

struct Found<'tcx> {
    seal: usize,
    /// The fn or item the statement's body belongs to.
    root: DefId,
    span: Span,
    site: Site<'tcx>,
}

/// What a body does that depends on the types it is made concrete at: read
/// once per body, judged at each instance ([`Checker::walk`]).
#[derive(Clone, Debug)]
enum Fact<'tcx> {
    /// A whole value written to a place of this type that may already hold
    /// one. `kept`: a place an `async` body keeps across an `.await`.
    Store { ty: Ty<'tcx>, kept: bool, span: Span },
    /// A write through field `field` of a union of this type.
    Union { ty: Ty<'tcx>, field: usize, span: Span },
    /// A fn item named: the callee of a call (`called`), or a value.
    Fn { ty: Ty<'tcx>, called: bool, span: Span },
    /// A value of this type dropped.
    Drop { ty: Ty<'tcx>, span: Span },
    /// An unsizing coercion.
    Unsize { source: Ty<'tcx>, target: Ty<'tcx>, span: Span },
    /// A closure made a fn pointer.
    Closure { ty: Ty<'tcx>, span: Span },
    /// A `const` item's value used.
    Const { def: DefId, args: GenericArgs<'tcx>, span: Span },
    /// In a body of another crate: a pointer given another type (a pointer
    /// cast, a transmute, an address taken as a number).
    Recast { source: Ty<'tcx>, target: Ty<'tcx>, span: Span },
    /// A fn the optimizer INLINED into this body (an optimized body of
    /// another crate): it is a callee all the same, asked what any fn of
    /// another crate is asked (S4b) and read as its own instance. (What it
    /// left in this body is read here too, as this body's: no reading is
    /// dropped for it.)
    /// `outer`: the fns it was inlined THROUGH, outermost first (a fn
    /// inlined into a fn inlined here): it is reached beneath them, as it
    /// would be had none been inlined.
    Inlined { callee: ty::Instance<'tcx>, outer: Vec<ty::Instance<'tcx>>, span: Span },
    /// In a body of a crate outside the standard library: the type of one of
    /// its locals. (S4e: what the body handles, at an instance.)
    Holds { ty: Ty<'tcx> },
    /// In a body of a crate outside the standard library: it does something
    /// only `unsafe` code can (the first such thing, for the note).
    Unsafe { what: &'static str },
    /// In an optimized body of another crate: the facts after this one, up
    /// to the next, are of code the optimizer inlined through these fns
    /// (outermost first; none: the body's own code). What that code CALLS,
    /// drops, makes a `dyn` or a fn pointer of, or names as a constant is
    /// reached beneath them, as it would be had none been inlined (review 2
    /// of the review-14 build: a trusted driver of crate B inlined into crate
    /// A's fn ran B's impl method on A's way, and B's trust was lost). A
    /// store is still read on the body's own way: the inliner writes the
    /// callee's return value straight into the CALLER's place.
    At { outer: Rc<[ty::Instance<'tcx>]> },
}

/// What [`Checker::resolve`] says runs.
enum Resolved<'tcx> {
    /// The one body the compiler resolves it to.
    Item(ty::Instance<'tcx>),
    /// In an open reading, no one body: an impl the instance picks (a
    /// where-clause or a projection bound says only that one exists), or
    /// arguments the item's environment cannot normalize. An ABSTRACT impl:
    /// unknown code at every type it is handed ([`Checker::unresolved`]).
    Open,
    /// Nothing runs (at concrete types, no one fn: a bound that cannot
    /// hold), or the walk stopped there and said so.
    None,
}

/// How a body comes to name an instance.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Handed {
    /// A fn item called (or a drop run, or what the compiler's collector
    /// says the body uses).
    Named,
    /// A fn as a VALUE: a fn item made a fn pointer, or a closure made one.
    /// It runs wherever the pointer is called, which this check does not
    /// follow, on what the caller hands it: in a body of a crate outside the
    /// standard library, what covered the way to it covers none of what its
    /// inputs can reach (review 2 of the review-14 build: a trusted
    /// `swapper::<T>() -> fn(&mut T, &mut T)` handed out `mem::swap::<T>`, and
    /// the swap this crate then made through the pointer was covered by the
    /// trust of `swapper`). [`Checker::caller_reach`].
    Pointer,
    /// The same of a method put in a vtable, and of the drop of what the
    /// `dyn` holds: its first input is the `dyn`'s own value, which the code
    /// that made the `dyn` put there (handed on with its type hidden, which
    /// a trust of that code covers, and says), and the others are the
    /// caller's.
    Vtable,
    /// A `const` item's initializer: it is handed nothing.
    Value,
    /// A fn the optimizer inlined into an optimized body of another crate.
    Inlined,
}

impl<'tcx> Fact<'tcx> {
    /// Whether the fact mentions a type parameter of its body: what it says
    /// is then known only at an instance.
    fn names_parameter(&self) -> bool {
        match *self {
            Fact::Store { ty, .. }
            | Fact::Union { ty, .. }
            | Fact::Fn { ty, .. }
            | Fact::Drop { ty, .. }
            | Fact::Closure { ty, .. }
            | Fact::Holds { ty } => ty.has_non_region_param(),
            Fact::Unsafe { .. } => false,
            Fact::Unsize { source, target, .. } | Fact::Recast { source, target, .. } => {
                source.has_non_region_param() || target.has_non_region_param()
            }
            Fact::Const { args, .. } => args.has_non_region_param(),
            Fact::Inlined { callee, ref outer, .. } => {
                callee.has_non_region_param()
                    || outer.iter().any(|outer| outer.has_non_region_param())
            }
            Fact::At { ref outer } => outer.iter().any(|outer| outer.has_non_region_param()),
        }
    }
}

/// How a body that is not this crate's (a body of another crate, a shim the
/// compiler writes) was reached.
#[derive(Clone, Copy)]
struct Through {
    /// Where a body of this crate named what led to it,
    at: Span,
    /// the fn or item that body belongs to,
    root: DefId,
    /// what was named there,
    named: DefId,
    /// and the seals whose `trusts` name a fn on the way.
    trusted: u64,
    /// For each crate outside the standard library that a fn on the way is
    /// of, the seals whose `trusts` name a fn OF THAT CRATE on the way: all
    /// that a trust says of code of that crate which the fn running it did
    /// not choose ([`Checker::reach`]). Kept for every crate on the way, not
    /// only the last one entered (review 2 of the review-14 build: crate A's
    /// trusted fn ran crate B's driver, which ran A's own impl method, and
    /// the trust of A's fn had been dropped on entering B). Interned
    /// ([`Checker::own_tables`]).
    own: OwnId,
    /// The item whose `trusts` entry would cover what is read now: the first
    /// fn a trust can name on the way since the way last lost what covered
    /// it (a body the fn running it did not choose, a fn reached as a value):
    /// what a note asks for when no fn that is handed a holder is to blame
    /// (`None`: no entry names one).
    cover: Option<DefId>,
    /// Whether the way lost what covered it to a fn reached as a VALUE (a fn
    /// pointer, a vtable's method: [`Handed::Pointer`]), which only a trust
    /// that names it covers: a note about a closure beneath it asks for no
    /// trust of the code that ran it.
    valued: bool,
}

/// A table of [`Through::own`], interned: sorted by crate, no zero entry.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
struct OwnId(u32);

impl OwnId {
    /// The table with no crate in it.
    const NONE: OwnId = OwnId(0);
}

/// A body made concrete: still to be read.
#[derive(Clone, Copy)]
struct Work<'tcx> {
    /// The body and what it is made concrete at. A body of this crate that
    /// has a type parameter is also read WHERE IT STANDS (its own
    /// parameters for arguments).
    instance: ty::Instance<'tcx>,
    /// For a body that is not this crate's.
    through: Option<Through>,
    /// An OPEN reading ([`Checker::read_instance`]): the item of this crate
    /// whose type parameters the instance's arguments name. A generic body
    /// of this crate read where it stands is one, and so is every body it
    /// names at a type that mentions its parameters (a fn of this crate or
    /// of another, a constant, a drop, a vtable's method), and every body
    /// those name in turn: what each says WHATEVER the parameters stand for
    /// is judged, read off its facts at those arguments, in the item's own
    /// typing environment. (Review 3 of the review-14 build: the reading
    /// where a library's generic fn stands judged a store and a call of a fn
    /// of another crate, and followed nothing: a helper of this crate, a
    /// trait method of another, a constant whose value swaps, a `dyn` made of
    /// a holder, a write of a union's field, each at `(T, App)`, held, and a
    /// crate that depends on the library swapped two holders through them.)
    open: Option<DefId>,
}

/// What two readings must share to be one ([`Checker::key`]): the instance,
/// the typing environment of an open reading, and whether it is read as this
/// crate's own; the first two with each parameter named by its index alone.
type WorkKey<'tcx> = (ty::Instance<'tcx>, Option<ty::ParamEnv<'tcx>>, bool);

/// Names every type and const parameter by its index alone (`T` of one item
/// and `U` of another, both the first, are one name), for [`WorkKey`]: only
/// a key is folded so, never what is asked of the compiler.
struct ByIndex<'tcx>(TyCtxt<'tcx>);

impl<'tcx> ty::TypeFolder<TyCtxt<'tcx>> for ByIndex<'tcx> {
    fn cx(&self) -> TyCtxt<'tcx> {
        self.0
    }

    fn fold_ty(&mut self, ty: Ty<'tcx>) -> Ty<'tcx> {
        if !ty.has_param() {
            return ty;
        }
        match *ty.kind() {
            ty::Param(param) => {
                Ty::new_param(self.0, param.index, rustc_span::symbol::kw::Underscore)
            }
            _ => ty::TypeSuperFoldable::super_fold_with(ty, self),
        }
    }

    fn fold_const(&mut self, ct: ty::Const<'tcx>) -> ty::Const<'tcx> {
        if !ct.has_param() {
            return ct;
        }
        match ct.kind() {
            ty::ConstKind::Param(param) => ty::Const::new_param(
                self.0,
                ty::ParamConst::new(param.index, rustc_span::symbol::kw::Underscore),
            ),
            _ => ty::TypeSuperFoldable::super_fold_with(ct, self),
        }
    }
}

/// What the walk knows of what each `dyn` was handed ([`Checker::erasures`]):
/// `erased`, `erased_reach`, `erased_foreign`, `erased_foreign_held`.
type Erasures = (
    FxHashMap<DefId, u64>,
    FxHashMap<DefId, u64>,
    FxHashMap<Option<DefId>, u64>,
    FxHashMap<Option<DefId>, u64>,
);

/// A step of the walk: depth first, so that how deep one fn is inside its
/// own instances is known, as the compiler counts it.
enum Step<'tcx> {
    Enter(Work<'tcx>),
    Leave(DefId),
}

struct Checker<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    seals: Vec<Seal<'a, 'tcx>>,
    /// The seals whose type a type owns (a bit each), for the types asked.
    owns: FxHashMap<Ty<'tcx>, u64>,
    /// Whether a type is plain data, for the types asked.
    plain: FxHashMap<Ty<'tcx>, bool>,
    /// The traits OF THIS CRATE a value owning a sealed type was handed to a
    /// `dyn` of, behind an owning pointer: such a `dyn` owns one from then
    /// on.
    erased: FxHashMap<DefId, u64>,
    /// The same for a value through which a sealed value can be WRITTEN (it
    /// owns one, or points to one): what a `dyn` of the trait may reach.
    erased_reach: FxHashMap<DefId, u64>,
    /// The same for a `dyn` of a trait of ANOTHER crate (or of no trait,
    /// `None`): what a value handed to one, in any body read, lets be
    /// written. A `dyn` of such a trait that only points to a holder is let
    /// pass (S4d), and whoever is later handed the `dyn` can be handed that
    /// too ([`Self::caller_reach`]; review 3 of the review-14 build: a fn
    /// value `fn(&mut dyn Any, &mut dyn Any)` was taken to be handed nothing
    /// that reaches a holder, and a trust of the fn that handed it out
    /// covered the swap it made of two holders behind two `&mut dyn Any`).
    erased_foreign: FxHashMap<Option<DefId>, u64>,
    /// The same of what a `dyn` of a trait of another crate OWNS from then
    /// on: what a value that owns one was handed to one as, behind an
    /// owning pointer (let pass on the trait's entry in `trusts`, or beneath
    /// a trusted fn). Such a `dyn` owns one wherever it goes next: put in
    /// another value, or upcast to a `dyn` of a supertrait (review 5 of the
    /// review-14 build: a `Box<dyn comp::Component>`, its trait trusted, was
    /// upcast to a `Box<dyn Any>` and swapped, the `dyn` taken to own
    /// nothing).
    erased_foreign_held: FxHashMap<Option<DefId>, u64>,
    /// Every unsizing coercion the walk met, as (source, target, made in a
    /// body of a crate outside the standard library, the open reading's
    /// item): what [`Self::settle_erasures`] reads again until `erased`,
    /// `erased_reach` and `erased_foreign` stop growing.
    unsize_log: Vec<(Ty<'tcx>, Ty<'tcx>, bool, Option<DefId>)>,
    unsize_seen: FxHashSet<(Ty<'tcx>, Ty<'tcx>, bool, Option<DefId>)>,
    /// The seals a value of which can be written through a value of a type
    /// (`false`), or through a `&` to one (`true`), for the types asked.
    reaches: FxHashMap<(Ty<'tcx>, bool), u64>,
    /// [`Self::reach_of`] read off a struct's or enum's definition
    /// ([`Summary`]), for the definitions asked (`None`: not readable so).
    summaries: FxHashMap<(DefId, bool), Option<Summary>>,
    /// [`Self::owns`] read off a struct's, enum's or union's definition
    /// ([`Self::owns_summary`]), for the definitions asked (`None`: not
    /// readable so).
    owned_defs: FxHashMap<DefId, Option<u64>>,
    /// [`Self::owns_whatever`] and [`Self::reach_open`], for the questions
    /// asked: (type, the item it is read in, `aliases` or `shared`). Each
    /// answer is a whole walk's (one that met a type too large to read is
    /// not kept), cleared with [`Self::owns`] whenever what a `dyn` holds
    /// grows. (Review 5 of the review-14 build: unkept, every open fact at
    /// `(T, App)` walked `App`'s whole type again, and 6,000 generic fns
    /// over a type of 6,000 parts took 107 s where the build took 6.)
    owns_open: FxHashMap<(Ty<'tcx>, DefId, bool), u64>,
    reached_open: FxHashMap<(Ty<'tcx>, DefId, bool), u64>,
    /// For an open reading's item: the seals its typing environment can tie
    /// a type parameter to ([`Self::env_mask`]).
    env_links: FxHashMap<DefId, u64>,
    /// For an associated type of a trait of this crate: the seals an impl
    /// may make it hold or reach ([`Self::local_assoc_mask`]).
    assoc_links: FxHashMap<DefId, u64>,
    /// For a trait reference resolution asks the solver about: whether the
    /// selection overflows the recursion limit ([`Self::solver_overflows`]).
    overflows: FxHashMap<(ty::TypingEnv<'tcx>, DefId, GenericArgs<'tcx>), bool>,
    /// What the bodies say whatever they are instantiated at (S2, S3, S3').
    fixed: Vec<Found<'tcx>>,
    /// What the instances say (S4).
    found: Vec<Found<'tcx>>,
    /// Each body's facts: this crate's from its pre-steal MIR, another
    /// crate's from the MIR its metadata carries, a shim's from the MIR the
    /// compiler writes for it (`None`: there is none to read).
    facts: FxHashMap<InstanceKind<'tcx>, Option<Rc<[Fact<'tcx>]>>>,
    /// The bodies of this crate none of whose facts mentions a type
    /// parameter: read where they stand, they are read.
    settled: FxHashSet<DefId>,
    /// For a writer, the parameters that are a `&mut` whose lifetime is
    /// named nowhere else in the fn's signature (S2).
    fresh_params: FxHashMap<DefId, Rc<[mir::Local]>>,
    /// The readings made, by key ([`Work::key`]): for a body that is not
    /// this crate's, the seals covered (`trusted`, `own`) on every way it
    /// was read on.
    seen: FxHashMap<WorkKey<'tcx>, (u64, OwnId)>,
    /// For an open reading's item, its typing environment as a key names
    /// it ([`Self::key`]).
    scope_envs: FxHashMap<DefId, ty::ParamEnv<'tcx>>,
    /// The tables of [`Through::own`], by [`OwnId`] (the first is empty),
    /// and the other way round.
    own_tables: Vec<Rc<[(CrateNum, u64)]>>,
    own_index: FxHashMap<Rc<[(CrateNum, u64)]>, OwnId>,
    /// For a `trusts` entry (seal, entry): a constant (or another item a
    /// trust does not name) whose path it matched. A constant runs nothing:
    /// what it hands out runs where it is called, and is judged there.
    misnamed: FxHashMap<(usize, usize), DefId>,
    /// The names that anchor a `trusts` entry at a crate (`::two::keep`):
    /// the crate's extern-prelude names in this crate, and its own name when
    /// no other crate of the build has it ([`Self::anchors`]).
    anchors: Option<FxHashMap<CrateNum, Vec<String>>>,
    queue: Vec<Step<'tcx>>,
    /// How many instances of one fn are being read, one inside another.
    depth: FxHashMap<DefId, usize>,
    /// The `trusts` entries that named something (seal, entry).
    used_trusts: FxHashSet<(usize, usize)>,
    /// For a `trusts` entry (seal, entry): the types holding one that the fn
    /// it names was run at. A trust is a NAME: it covers the fn at every
    /// type, and the note says which.
    trusted_at: FxHashMap<(usize, usize), BTreeSet<String>>,
    /// By seal: what a value holding one was handed on as, beneath a trusted
    /// fn, in a form whose type no longer shows it. The author's word covers
    /// it, and the note says so.
    handed_on: FxHashMap<usize, BTreeSet<String>>,
    /// By seal: the pointers to such a value given a type that no longer
    /// says so, beneath a trusted fn (an allocator's, mostly).
    recast_on: FxHashMap<usize, BTreeSet<String>>,
    /// The `trusts` entries (seal, entry) that name an item, for the items
    /// asked.
    trusting: FxHashMap<DefId, Rc<[(usize, usize)]>>,
    /// For a `trusts` entry (seal, entry): the items of the crate graph its
    /// word was RELIED ON for (a site it covered, a body read beneath it:
    /// where [`Self::used_trusts`] is noted), by where each is defined (its
    /// crate, and its path there), with one of them for each. Items of one
    /// crate at one path (std's `From` impls for `Vec`, each
    /// `alloc::vec::Vec::from`) are one name: no entry can tell them apart.
    /// More than one is an error. (An item the walk only met, a fn of std's
    /// own beneath `Mutex::lock` that names no type of this crate, is
    /// covered by nothing it says.)
    /// (Keyed by the item's path, its crate and, for an item of an impl
    /// whose own type is not a struct, enum or union, the impl: such impls of
    /// one trait in one module share a path with each other and with the
    /// trait's own item, [`entry_path`], and are told apart here, so that an
    /// entry relied on for two of them is refused.)
    entry_items: FxHashMap<(usize, usize), BTreeMap<(String, u32, Option<u32>), DefId>>,
    /// The items at which a `trusts` entry's word would be relied on, had
    /// one named them ([`Self::relied`]), whether or not one did.
    relied_on: FxHashSet<DefId>,
    /// The same, by where each is defined: what a suggested entry must not
    /// also name. Filled before the report.
    asked_paths: Vec<(CrateNum, Vec<String>)>,
    /// Whether a crate is the standard library's (one of the sysroot's).
    resident: FxHashMap<CrateNum, bool>,
    /// [`Self::works_on`], for the instances asked (and the open reading's
    /// item, for an instance whose arguments name its parameters).
    worked: FxHashMap<(ty::Instance<'tcx>, Option<DefId>), Option<(u64, Ty<'tcx>, &'static str)>>,
    /// The parts of a type as the compiler's walks count them, and how
    /// deep it nests ([`TreeSize`]), for the types asked.
    tree: FxHashMap<Ty<'tcx>, (u64, u32)>,
    /// Whether a type walk or the instance walk gave up at its bound.
    cut: bool,
    bodies: usize,
    instances: usize,
}

/// The most types one question about a type may open before it is answered
/// "owns every sealed type" (fail-closed): far above any real type, a guard
/// against a type that grows as it is walked.
const WALK_BOUND: usize = 50_000;

/// The most types one question "is it plain data" opens before the answer is
/// no: a sealed field's type is small.
const PLAIN_BOUND: usize = 4_096;

/// The most types (or erasures) kept for one line of a note that lists them:
/// the note names the first few and says how many more there are.
const LISTED: usize = 64;

/// The most instances the walk reads before the seals are refused.
const INSTANCE_BOUND: usize = 2_000_000;

/// The most parts a type an instance is made at may have, counted as the
/// compiler's own walks of a type count them (part by part: `(X, X)` has
/// X's parts twice) before the walk stops and the seals are refused. A type
/// shares its parts, so it can double at each step of a polymorphic
/// recursion while the compiler's own count of distinct parts (the type
/// length limit) grows by one: asking what such a type's drop runs then
/// takes time that doubles at each step. Far above any type a program
/// writes.
const TREE_BOUND: u64 = 1 << 22;

/// The deepest a type an instance is made at may nest before the walk stops
/// and the seals are refused. The compiler's walks of a type (its trait
/// solver, its checks of bound variables) recurse once per level, and at a
/// raised recursion limit polymorphic recursion makes types deep enough to
/// exhaust its stack (review 2 of the review-14 build: dead `grow(Some(x))`
/// at `#![recursion_limit = "2048"]` crashed the compiler at about 1,600
/// levels, and was refused cleanly at 1,300). Far deeper than any type a
/// program writes.
const DEPTH_BOUND: u32 = 512;

/// Counts the parts of a type as a walk that does not share them would,
/// sharing the count instead ([`Checker::tree`]): saturating; and how deep
/// it nests. A closure, a coroutine and a coroutine-closure count by what
/// they capture (their upvars), as the compiler's walks of one read it:
/// its drop drops those, and its signature and the generic arguments of the
/// fn it is in are no part of its value (review 2 of the review-14 build:
/// counting both made a closure that names and captures its argument count
/// twice, std's `fold` wraps one closure in another at each adaptor, and a
/// plain chain of 15 `map`s was refused as a doubling type).
struct TreeSize<'m, 'tcx> {
    memo: &'m mut FxHashMap<Ty<'tcx>, (u64, u32)>,
    total: u64,
    depth: u32,
}

impl<'m, 'tcx> ty::TypeVisitor<TyCtxt<'tcx>> for TreeSize<'m, 'tcx> {
    fn visit_ty(&mut self, ty: Ty<'tcx>) {
        let (size, depth) = match self.memo.get(&ty) {
            Some(&known) => known,
            None => {
                let mut inner = TreeSize { memo: &mut *self.memo, total: 1, depth: 0 };
                rustc_data_structures::stack::ensure_sufficient_stack(|| match *ty.kind() {
                    ty::Closure(_, args) => {
                        args.as_closure().tupled_upvars_ty().visit_with(&mut inner)
                    }
                    ty::CoroutineClosure(_, args) => {
                        args.as_coroutine_closure().tupled_upvars_ty().visit_with(&mut inner)
                    }
                    ty::Coroutine(_, args) => {
                        args.as_coroutine().tupled_upvars_ty().visit_with(&mut inner)
                    }
                    _ => ty.super_visit_with(&mut inner),
                });
                let known = (inner.total, inner.depth.saturating_add(1));
                self.memo.insert(ty, known);
                known
            }
        };
        self.total = self.total.saturating_add(size).min(TREE_BOUND << 1);
        self.depth = self.depth.max(depth);
    }
}

/// What a struct, enum or union lets be written through what it holds, read
/// off its definition with its type parameters left open ([`Checker::
/// reach_of`] where a walk of its instances has no end): the seals reached
/// whatever the parameters are, and the type parameters reached, behind a
/// `&` all the way (`shared`) or not (`owned`), a bit each by its index.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct Summary {
    mask: u64,
    shared: u64,
    owned: u64,
}

/// What an unsizing coercion hands to one `dyn` it makes
/// ([`Checker::erasures_of`]).
struct Erasure<'tcx> {
    /// The value's type, and the `dyn` it is handed to (with its bounds).
    concrete: Ty<'tcx>,
    to: Ty<'tcx>,
    predicates: &'tcx ty::List<ty::PolyExistentialPredicate<'tcx>>,
    principal: Option<DefId>,
    /// The seals a `dyn` of a trait of this crate holds from then on; of
    /// another's, what is refused unless trusted (S4d).
    held: u64,
    /// The seals a value of which can be written through the value.
    reached: u64,
    /// The seals the value OWNS, which the `dyn` owns from then on (behind a
    /// pointer that has a grip on it).
    owned: u64,
    /// The open reading's item, when the value's type names its parameters.
    mode: Option<DefId>,
}

/// Check every body of the crate against the seals its islands declare, and
/// fail the build at a seal that does not hold.
pub fn check_seals<'tcx>(tcx: TyCtxt<'tcx>, decls: &[SealDecl]) {
    if decls.is_empty() {
        return;
    }
    let mut seals: Vec<Seal<'_, 'tcx>> = Vec::new();
    for decl in decls {
        let Some(seal) = resolve(tcx, decl) else { continue };
        // S1: a type has one seal. (Every site is laid to the seal on its
        // type: a second one would be asked nothing, and hold.)
        if let Some(first) = seals.iter().find(|first| first.adt.did() == seal.adt.did()) {
            tcx.dcx()
                .struct_span_err(
                    decl.span,
                    format!(
                        "seal `{}` is on `{}`, which seal `{}` already seals: a type has one seal",
                        decl.name,
                        tcx.item_name(seal.adt.did()),
                        first.decl.name
                    ),
                )
                .with_span_note(first.decl.span, "the first seal on the type")
                .with_help("say all of it in one seal: its writers, makers and callers together")
                .emit();
            continue;
        }
        seals.push(seal);
    }
    if seals.is_empty() {
        return;
    }
    if seals.len() > 64 {
        tcx.dcx().span_err(seals[64].decl.span, "more than 64 seals in one crate are not read");
        return;
    }
    let mut checker = Checker {
        tcx,
        seals,
        owns: FxHashMap::default(),
        plain: FxHashMap::default(),
        erased: FxHashMap::default(),
        erased_reach: FxHashMap::default(),
        erased_foreign: FxHashMap::default(),
        erased_foreign_held: FxHashMap::default(),
        unsize_log: Vec::new(),
        unsize_seen: FxHashSet::default(),
        reaches: FxHashMap::default(),
        summaries: FxHashMap::default(),
        owned_defs: FxHashMap::default(),
        owns_open: FxHashMap::default(),
        reached_open: FxHashMap::default(),
        env_links: FxHashMap::default(),
        assoc_links: FxHashMap::default(),
        overflows: FxHashMap::default(),
        fixed: Vec::new(),
        found: Vec::new(),
        facts: FxHashMap::default(),
        settled: FxHashSet::default(),
        fresh_params: FxHashMap::default(),
        seen: FxHashMap::default(),
        scope_envs: FxHashMap::default(),
        own_tables: vec![Rc::from(Vec::new())],
        own_index: FxHashMap::default(),
        misnamed: FxHashMap::default(),
        anchors: None,
        queue: Vec::new(),
        depth: FxHashMap::default(),
        used_trusts: FxHashSet::default(),
        trusted_at: FxHashMap::default(),
        handed_on: FxHashMap::default(),
        recast_on: FxHashMap::default(),
        trusting: FxHashMap::default(),
        entry_items: FxHashMap::default(),
        relied_on: FxHashSet::default(),
        asked_paths: Vec::new(),
        resident: FxHashMap::default(),
        worked: FxHashMap::default(),
        tree: FxHashMap::default(),
        cut: false,
        bodies: 0,
        instances: 0,
    };
    checker.read_bodies();
    // A `dyn` of a trait of this crate that a value owning a sealed type is
    // handed to owns one from then on, which changes what the instances
    // already read were asked: read them again until no new such trait turns
    // up. What a coercion hands to a `dyn` is a question about its two types
    // alone, and the coercions met do not depend on what was handed to a
    // `dyn` (which instances are read turns on what their arguments name,
    // never on what a type owns): so the walk logs them, and after each walk
    // `settle_erasures` reads the log again until nothing grows, and the
    // instances are read once more only if something did. (Review 3 of the
    // review-14 build: each walk learned one link of a chain of `dyn`s
    // written in reverse order, and the check cost one walk per link.)
    loop {
        let erased = checker.erasures();
        checker.owns.clear();
        checker.reaches.clear();
        checker.summaries.clear();
        checker.owned_defs.clear();
        checker.owns_open.clear();
        checker.reached_open.clear();
        checker.env_links.clear();
        checker.assoc_links.clear();
        checker.worked.clear();
        checker.found.clear();
        checker.seen.clear();
        checker.depth.clear();
        checker.instances = 0;
        checker.walk();
        checker.settle_erasures();
        if checker.erasures() == erased {
            break;
        }
    }
    // (What a note suggests for `trusts` must name no other item met: also
    // none that the crate's shape relies on, which `judge_shape` is about to
    // say. Review 2 of the review-14 build: two `unsafe impl`s of two
    // crates' `marker::Pod` were each asked for the entry `marker::Pod`.)
    checker.shape_relied();
    checker.note_asked();
    checker.judge_shape();
    checker.judge_trusts();
    checker.report();
}

/// The items `names` name, each exactly one of the crate's, or an error at
/// the seal. `statics`: a `static` may be named too. `lenient`: a name that
/// names nothing is no error (it is handed back in the second list).
fn named_fns<'tcx>(
    tcx: TyCtxt<'tcx>,
    decl: &SealDecl,
    names: &[String],
    what: &str,
    statics: bool,
    lenient: bool,
) -> Option<(Vec<DefId>, Vec<String>)> {
    let mut out = Vec::new();
    let mut absent = Vec::new();
    for name in names {
        let mut named: Vec<DefId> = tcx
            .mir_keys(())
            .iter()
            .copied()
            .filter(|def| {
                let kind = tcx.def_kind(*def);
                matches!(kind, DefKind::Fn | DefKind::AssocFn)
                    || (statics && matches!(kind, DefKind::Static { nested: false, .. }))
            })
            .filter(|def| names_path(&item_path(tcx, def.to_def_id()), name))
            // (Not a fn the compiler wrote: a test build has a second `main`.)
            .filter(|def| {
                !matches!(
                    tcx.def_span(*def).ctxt().outer_expn_data().kind,
                    rustc_span::hygiene::ExpnKind::AstPass(_)
                )
            })
            .map(|def| def.to_def_id())
            .collect();
        named.sort_unstable_by_key(|def| def.index.as_u32());
        named.dedup();
        match named.as_slice() {
            [one] => out.push(*one),
            [] if lenient => absent.push(name.clone()),
            [] => {
                tcx.dcx()
                    .struct_span_err(
                        decl.span,
                        format!(
                            "seal `{}` names `{name}` as {what}, which is no fn of this crate",
                            decl.name
                        ),
                    )
                    .with_help(
                        "write a fn's name, with as much of its path as tells it apart \
                         (`offer`, `PolicyCell::offer`, `order::PolicyCell::offer`)",
                    )
                    .emit();
                return None;
            }
            several => {
                let paths: Vec<String> = several
                    .iter()
                    .map(|def| format!("`{}`", item_path(tcx, *def).join("::")))
                    .collect();
                tcx.dcx()
                    .struct_span_err(
                        decl.span,
                        format!(
                            "seal `{}` names `{name}` as {what}, which is {} fns: {}",
                            decl.name,
                            several.len(),
                            and_list(&paths)
                        ),
                    )
                    .with_help("write as much of the path as tells them apart")
                    .emit();
                return None;
            }
        }
    }
    Some((out, absent))
}

/// The seal `decl` with its type and fns found, and what S1 says of the type
/// alone checked; or `None` after an error at the seal.
fn resolve<'a, 'tcx>(tcx: TyCtxt<'tcx>, decl: &'a SealDecl) -> Option<Seal<'a, 'tcx>> {
    let refuse = |message: String, help: &str| {
        let mut diag = tcx.dcx().struct_span_err(decl.span, message);
        if !help.is_empty() {
            diag.help(help.to_owned());
        }
        diag.emit();
    };
    // The type: exactly one struct, enum or union of this crate.
    let mut types: Vec<DefId> = tcx
        .hir_crate_items(())
        .definitions()
        .filter(|def| {
            matches!(tcx.def_kind(*def), DefKind::Struct | DefKind::Enum | DefKind::Union)
        })
        .map(|def| def.to_def_id())
        .filter(|def| names_path(&item_path(tcx, *def), &decl.type_name))
        .collect();
    types.sort_unstable_by_key(|def| def.index.as_u32());
    let def = match types.as_slice() {
        [one] => *one,
        [] => {
            refuse(
                format!(
                    "seal `{}` is on `{}`, which is no struct of this crate",
                    decl.name, decl.type_name
                ),
                "a seal is declared in the crate that defines the type: write the type's name, \
                 with as much of its module path as tells it apart (`PolicyCell`, \
                 `order::PolicyCell`)",
            );
            return None;
        }
        several => {
            let paths: Vec<String> = several
                .iter()
                .map(|def| format!("`{}`", item_path(tcx, *def).join("::")))
                .collect();
            refuse(
                format!(
                    "seal `{}` is on `{}`, which is {} types: {}",
                    decl.name,
                    decl.type_name,
                    several.len(),
                    and_list(&paths)
                ),
                "write as much of the path as tells them apart",
            );
            return None;
        }
    };
    let adt = tcx.adt_def(def);
    let shown = tcx.item_name(def);
    // S1.
    if !adt.is_struct() {
        refuse(
            format!(
                "seal `{}` is on `{shown}`, which is {}: only a struct is sealed",
                decl.name,
                if adt.is_union() { "a union" } else { "an enum" }
            ),
            "an enum's variant is changed by assigning a whole new value, which a seal forbids, \
             and a union's fields share their bytes: seal a struct that keeps the enum in a \
             field",
        );
        return None;
    }
    if adt.all_fields().next().is_none() {
        refuse(format!("seal `{}` is on `{shown}`, which has no field to seal", decl.name), "");
        return None;
    }
    if tcx.generics_of(def).count() != 0 {
        refuse(
            format!(
                "seal `{}` is on `{shown}`, which has a generic parameter: a sealed type is \
                 one type",
                decl.name
            ),
            "what a parameter stands for is known only where the type is used, and a use in \
             another crate, or in generic code, is not one this check reads: write the type for \
             its one payload",
        );
        return None;
    }
    if let Some(field) = adt.all_fields().find(|field| tcx.visibility(field.did).is_public()) {
        tcx.dcx()
            .struct_span_err(
                decl.span,
                format!(
                    "seal `{}` is on `{shown}`, whose field `{}` is `pub`: another crate can \
                     write it",
                    decl.name, field.name
                ),
            )
            .with_span_note(tcx.def_span(field.did), "this field")
            .with_help("make every field private, or `pub(crate)`")
            .emit();
        return None;
    }
    // A crate nothing can depend on (a program, a test harness) has no
    // other crate to hide from.
    let depended_on = tcx.crate_types().iter().any(|kind| kind.has_metadata());
    if let Some(local) = def.as_local() {
        if depended_on && tcx.effective_visibilities(()).is_reachable(local) {
            refuse(
                format!(
                    "seal `{}` is on `{shown}`, which another crate can name: this check reads \
                     only this crate, and a crate that can hold a `{shown}` can put one value \
                     over another, unseen",
                    decl.name
                ),
                "make the type `pub(crate)` or narrower, and keep it out of every `pub` \
                 signature",
            );
            return None;
        }
    }
    if let Some(copy) = tcx.lang_items().copy_trait() {
        let self_ty = tcx.type_of(def).instantiate_identity().skip_norm_wip();
        let mut is_copy = false;
        tcx.for_each_relevant_impl(copy, self_ty, |_| is_copy = true);
        if is_copy {
            refuse(
                format!(
                    "seal `{}` is on `{shown}`, which is `Copy`: any code can make another \
                     value of it",
                    decl.name
                ),
                "a sealed type is neither `Copy` nor `Clone`",
            );
            return None;
        }
    }
    // A `trusts` entry says which fn (or trait) of another crate it means:
    // a bare `new` or `drop` would name every fn of that name. Judged on the
    // parts the entry is matched by ([`names_path`] drops an empty one), so
    // `::swap` and `swap::` are the bare name they are matched as. (Review
    // 1 of the review-14 build: `::swap` passed and trusted every `swap`.)
    let parts = |trusted: &str| -> Vec<String> {
        trusted.split("::").map(|part| part.trim().to_owned()).collect()
    };
    if let Some(bare) = decl
        .trusts
        .iter()
        .find(|trusted| parts(trusted).iter().filter(|part| !part.is_empty()).count() < 2)
    {
        refuse(
            format!(
                "seal `{}` trusts `{bare}`, a bare name: every fn of that name in every other \
                 crate would be trusted",
                decl.name
            ),
            "write it with its type or module (`Box::new`, `mem::drop`, `any::Any`)",
        );
        return None;
    }
    // (A leading `::` ANCHORS the entry at a crate, as Rust's own
    // `::krate::path` does: `Checker::entry_names`. Review 2 of the
    // review-14 build: two crates of one name had no entry of their own.)
    if let Some(gap) = decl.trusts.iter().find(|trusted| {
        let trusted = trusted.trim();
        parts(trusted.strip_prefix("::").unwrap_or(trusted)).iter().any(|part| part.is_empty())
    }) {
        refuse(
            format!(
                "seal `{}` trusts `{gap}`, a path with an empty part: an entry is two or more \
                 names joined by `::`, matched from the right against where the item is defined \
                 (or, anchored, `::`, a crate's name and the item's whole path in it)",
                decl.name
            ),
            "write the names alone, with no trailing or doubled `::` (`mem::swap`, \
             `core::mem::swap`, `::core::mem::swap`)",
        );
        return None;
    }
    let (writers, _) = named_fns(tcx, decl, &decl.writers, "a writer", false, false)?;
    let (makers, _) = named_fns(tcx, decl, &decl.makers, "a maker", false, false)?;
    let (made_by, absent) =
        named_fns(tcx, decl, &decl.made_by, "a fn that may call a maker", true, true)?;
    for maker in &makers {
        let shown_maker = item_path(tcx, *maker).join("::");
        // S3: a maker's callers must be nameable: a free fn, or a method of
        // the type's own.
        if let Some(parent) = tcx.opt_parent(*maker) {
            if matches!(tcx.def_kind(parent), DefKind::Impl { of_trait: true } | DefKind::Trait) {
                refuse(
                    format!(
                        "seal `{}` names `{shown_maker}` as a maker, which is a method of a \
                         trait: code that knows only the trait can call it",
                        decl.name,
                    ),
                    "build the value in an inherent or a free fn",
                );
                return None;
            }
        }
        // S1: and they must all be in this crate.
        if let Some(local) = maker.as_local() {
            if depended_on && tcx.effective_visibilities(()).is_reachable(local) {
                refuse(
                    format!(
                        "seal `{}` names `{shown_maker}` as a maker, which another crate can \
                         call: this check reads only this crate's calls",
                        decl.name,
                    ),
                    "make the maker `pub(crate)` or narrower",
                );
                return None;
            }
        }
    }
    Some(Seal { decl, adt, writers, makers, made_by, absent })
}

/// Counts how often one lifetime is named in a type.
struct Occurrences<'tcx> {
    of: ty::Region<'tcx>,
    count: usize,
}

impl<'tcx> ty::TypeVisitor<TyCtxt<'tcx>> for Occurrences<'tcx> {
    fn visit_region(&mut self, region: ty::Region<'tcx>) {
        if region == self.of {
            self.count += 1;
        }
    }
}

/// Whether a writer's return type hands back the lifetime `of` only as a
/// LENT borrow: `&'of T` with `T` free of `'of`, alone or in a tuple, an
/// `Option` or a `Result` of such (`lent`: those `T`). Anything else that
/// names `'of` is refused, and for reasons review 13 found one by one:
///
/// - `&'y &'of ()` is well-formed only if `'of: 'y`, a bound the fn's body
///   may then assume: it lets the body put a `&'of mut` of a field into a
///   `'y` place the caller keeps. A `&'of T` at the top gives only bounds
///   the other way (`T: 'of`).
/// - a type argument is no place to judge: `<&'of () as Tr>::Out` and
///   `Wrap<&'of ()>` with a field `T::Out` are both whatever an impl says,
///   a `&'of mut u8` included. `Option`, `Result` and tuples store their
///   arguments as they are.
///
/// A value of such a type holds no `&mut` of that lifetime; whether a `&`
/// of it can write is asked of what it points to (`Cell::from_mut` makes a
/// `&Cell<T>` of a `&mut T`).
fn only_lent<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>,
    of: ty::Region<'tcx>,
    lent: &mut Vec<Ty<'tcx>>,
) -> bool {
    let names = |ty: Ty<'tcx>| {
        let mut inside = Occurrences { of, count: 0 };
        ty.visit_with(&mut inside);
        inside.count != 0
    };
    match *ty.kind() {
        ty::Ref(region, inner, mutability) if region == of => {
            if mutability.is_mut() || names(inner) {
                return false;
            }
            lent.push(inner);
            true
        }
        ty::Tuple(parts) => parts.iter().all(|part| only_lent(tcx, part, of, lent)),
        ty::Adt(adt, args)
            if tcx.is_lang_item(adt.did(), LangItem::Option)
                || tcx.is_diagnostic_item(sym::Result, adt.did()) =>
        {
            args.types().all(|part| only_lent(tcx, part, of, lent))
        }
        _ => !names(ty),
    }
}

/// S2: the parameters of the fn `writer` that are a `&mut` whose lifetime is
/// the fn's own to choose at each call and is named NOWHERE ELSE in its
/// inputs (at any depth: a type argument, a `dyn` bound, a fn pointer), and
/// in its return type only as a lent borrow ([`only_lent`]: `fn get(&mut
/// self) -> &T`); with each, the types such a `&` points to, which the
/// caller holds to be plain data: a `&` of plain data writes nothing. (A
/// lifetime that a where-clause or the impl names is not one of these: it is
/// fixed outside the call.)
///
/// A borrow of a field made through such a parameter has that lifetime at
/// most. With nothing else in the signature able to hold a `&mut` of it,
/// and nothing in it that makes the lifetime outlive another, safe code
/// cannot store the borrow where it outlives the call: every other place it
/// can reach has a type with an unrelated lifetime, which the borrow checker
/// will not let it be written to.
fn fresh_params<'tcx>(tcx: TyCtxt<'tcx>, writer: DefId) -> Vec<(mir::Local, Vec<Ty<'tcx>>)> {
    if !matches!(tcx.def_kind(writer), DefKind::Fn | DefKind::AssocFn) {
        return Vec::new();
    }
    let sig = tcx.fn_sig(writer).instantiate_identity().skip_norm_wip();
    let sig = tcx.liberate_late_bound_regions(writer, sig);
    let mut fresh = Vec::new();
    for (index, input) in sig.inputs().iter().enumerate() {
        let ty::Ref(region, _, mutability) = *input.kind() else { continue };
        if !mutability.is_mut() || !matches!(region.kind(), ty::ReLateParam(..)) {
            continue;
        }
        let mut handed = Occurrences { of: region, count: 0 };
        for input in sig.inputs() {
            input.visit_with(&mut handed);
        }
        let mut lent = Vec::new();
        if handed.count == 1 && only_lent(tcx, sig.output(), region, &mut lent) {
            fresh.push((mir::Local::from_usize(index + 1), lent));
        }
    }
    fresh
}

/// [`item_path`] as a `trusts` entry names an item: a method (or constant)
/// of a trait impl whose own type is not a struct, enum or union (`impl<T:
/// Default> Reset for T`, `impl<T> Shuffle for [T]`, an impl for a `&mut T`,
/// a tuple or a `dyn`) is named with the trait, `coll::Reset::reset`, where
/// `item_path` names it by its module alone, as it names a free fn of the
/// same name there. (Review 5 of the review-14 build: the entry
/// `coll::reset`, given for a free fn that only measures, also named the
/// blanket impl's `reset`, which overwrote a holder; and no entry could name
/// either alone.) What remains one name is an impl's item and the trait's
/// own, and two impls of one trait in one module for types that are none of
/// these: an entry for one covers each.
fn entry_path(tcx: TyCtxt<'_>, def: DefId) -> Vec<String> {
    let mut path: Vec<String> = Vec::new();
    let mut current = Some(def);
    while let Some(at) = current {
        if at.is_crate_root() {
            break;
        }
        match tcx.def_kind(at) {
            DefKind::Impl { .. } => {
                match *tcx.type_of(at).instantiate_identity().skip_norm_wip().kind() {
                    ty::Adt(adt, _) => path.push(tcx.item_name(adt.did()).to_string()),
                    _ => {
                        if let Some(of) = tcx.impl_opt_trait_id(at) {
                            path.push(tcx.item_name(of).to_string());
                        }
                    }
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

/// `ty` as the item `scope` sees it: a projection that an impl or a bound
/// settles for every value of the item's parameters (`Self::Out` in a
/// generic impl, `<T as Tr>::Out` under a blanket impl) is what it stands
/// for. Regions erased.
fn seen_from<'tcx>(tcx: TyCtxt<'tcx>, scope: DefId, ty: Ty<'tcx>) -> Ty<'tcx> {
    let ty = tcx.erase_and_anonymize_regions(ty);
    if !ty.has_aliases() {
        return ty;
    }
    tcx.try_normalize_erasing_regions(
        ty::TypingEnv::post_analysis(tcx, scope),
        ty::Unnormalized::new_wip(ty),
    )
    .unwrap_or(ty)
}

/// What a type that is not concrete is taken to own.
#[derive(Clone, Copy)]
enum Abstract {
    /// Every sealed type: the type should have been concrete (fail-closed).
    Everything,
    /// Nothing, read as the item `scope` sees it: what a body or a constant
    /// says WHATEVER its parameters stand for. `aliases`: a projection that
    /// nothing settles is taken to own every sealed type all the same (it is
    /// some impl's to say what it is).
    Nothing { scope: DefId, aliases: bool },
}

/// The item an alias names: an associated type (of a trait or an impl), an
/// opaque type, a type alias.
fn alias_def(kind: ty::AliasTyKind<'_>) -> DefId {
    match kind {
        ty::AliasTyKind::Projection { def_id }
        | ty::AliasTyKind::Inherent { def_id }
        | ty::AliasTyKind::Opaque { def_id }
        | ty::AliasTyKind::Free { def_id } => def_id,
    }
}

/// Every type a value names, at any depth (a clause's).
struct TypesIn<'tcx>(Vec<Ty<'tcx>>);

impl<'tcx> ty::TypeVisitor<TyCtxt<'tcx>> for TypesIn<'tcx> {
    fn visit_ty(&mut self, ty: Ty<'tcx>) {
        self.0.push(ty);
        ty.super_visit_with(self);
    }
}

/// What an alias in a type an open reading reads is ([`Checker::alias_read`]).
enum AliasRead<'tcx> {
    /// What it normalizes to in the item's typing environment.
    Is(Ty<'tcx>),
    /// Rigid there: an impl exists, and nothing says what it is.
    Rigid,
    /// Not settled there: the bounds do not say an impl exists.
    Unsettled,
}

/// Whether a value of type `ty` can own nothing a seal speaks of, whatever
/// it is made concrete at: no fact about it is worth keeping.
fn owns_nothing(ty: Ty<'_>) -> bool {
    matches!(
        ty.kind(),
        ty::Bool
            | ty::Char
            | ty::Int(_)
            | ty::Uint(_)
            | ty::Float(_)
            | ty::Str
            | ty::Never
            | ty::Ref(..)
            | ty::RawPtr(..)
            | ty::FnDef(..)
            | ty::FnPtr(..)
    )
}

impl<'a, 'tcx> Checker<'a, 'tcx> {
    /// The seal whose type `def` is.
    fn sealed(&self, def: DefId) -> Option<usize> {
        self.seals.iter().position(|seal| seal.adt.did() == def)
    }

    fn all(&self) -> u64 {
        u64::MAX >> (64 - self.seals.len().clamp(1, 64))
    }

    /// T*: the seals whose type a value of the CONCRETE type `ty` OWNS, as a
    /// set of bits (bit `i`: seal `i`). By type and exact, except at
    /// [`WALK_BOUND`] and at a type that is not concrete, where the answer is
    /// "all of them".
    ///
    /// A struct, enum or union of any crate by its fields, private ones too,
    /// each normalized; any of them by its type arguments as well (whatever
    /// it keeps them in: a `Vec`, a `Mutex`, a raw pointer of its own); a
    /// tuple, array or slice; a closure by its captures and a coroutine by
    /// what it keeps across a suspension too; a `dyn` of a trait of this
    /// crate that a value owning one was handed to. A `&`, `&mut` or `*`
    /// owns nothing.
    fn owns(&mut self, ty: Ty<'tcx>) -> u64 {
        if let Some(known) = self.owns.get(&ty) {
            return *known;
        }
        let mut visited: FxHashSet<Ty<'tcx>> = FxHashSet::default();
        let mut mask = 0u64;
        let was_cut = std::mem::replace(&mut self.cut, false);
        self.owns_in(ty, &mut visited, &mut mask, Abstract::Everything);
        let cut_here = self.cut;
        self.cut = was_cut || cut_here;
        if cut_here && visited.len() > WALK_BOUND {
            // A NESTED type, which grows as it is walked: read it off its
            // definitions ([`Self::owns_defined`]), as `reach_of` does.
            if let Some(defined) = self.owns_defined(ty, false) {
                self.cut = was_cut;
                self.owns.insert(ty, defined);
                return defined;
            }
        }
        if mask == 0 {
            // Nothing the walk opened reaches a sealed type.
            for seen in visited {
                self.owns.insert(seen, 0);
            }
        } else {
            // (Only the type asked: a part reached through a type that holds
            // itself may own more than the walk saw below it.)
            self.owns.insert(ty, mask);
        }
        mask
    }

    /// [`Self::owns`] of a type that names a type parameter of the item
    /// `scope`: what it owns WHATEVER the parameter stands for (`(T, App)`
    /// owns what `App` does; so does `Wrap<T>` with a field `T::Out` that a
    /// blanket impl makes `App`). `aliases`: see [`Abstract::Nothing`].
    fn owns_whatever(&mut self, ty: Ty<'tcx>, scope: DefId, aliases: bool) -> u64 {
        let ty = seen_from(self.tcx, scope, ty);
        if let Some(&known) = self.owns_open.get(&(ty, scope, aliases)) {
            return known;
        }
        let mut visited: FxHashSet<Ty<'tcx>> = FxHashSet::default();
        let mut mask = 0u64;
        let was_cut = std::mem::replace(&mut self.cut, false);
        self.owns_in(ty, &mut visited, &mut mask, Abstract::Nothing { scope, aliases });
        let cut_here = self.cut;
        self.cut = was_cut || cut_here;
        if cut_here && visited.len() > WALK_BOUND {
            if let Some(defined) = self.owns_defined(ty, true) {
                self.cut = was_cut;
                self.owns_open.insert((ty, scope, aliases), defined);
                return defined;
            }
        }
        // (A walk that met a type too large to read answered "all of them":
        // asked again, not kept.)
        if !cut_here {
            self.owns_open.insert((ty, scope, aliases), mask);
        }
        mask
    }

    /// [`Self::owns`] by DEFINITIONS, as [`Self::reach_defined`] is for
    /// [`Self::reach_of`], where the walk of a type's instances has no end:
    /// a NESTED type, each step of which is a new, larger one (`Nest<T>`
    /// with a field `Weak<Nest<Option<T>>>`; review 4 of the review-14
    /// build: a plain `Nest<u8>` was taken to hold a `Cell`, and assigning
    /// one was refused with no `trusts` entry to answer it). Each struct,
    /// enum or union met is answered by what its definition owns whatever
    /// its parameters are ([`Self::owns_summary`]), and by what its type
    /// arguments own, each whole (`owns_in` reads every type argument as
    /// owned, wherever the type keeps it). The same answer as the walk's
    /// had it an end: what a field owns at the arguments is what it owns
    /// with the parameters left open, and what the argument of each
    /// parameter it names owns, which the type arguments add anyway; and
    /// both are least answers of the same steps. (`open`: the type names
    /// parameters of an open reading's item, which own nothing.) `None`
    /// where a part is not read so: a projection the definition does not
    /// settle, a closure, a coroutine.
    fn owns_defined(&mut self, ty: Ty<'tcx>, open: bool) -> Option<u64> {
        let mut mask = 0u64;
        self.owns_defined_in(ty, open, None, &mut mask, &mut Vec::new(), 0)?;
        Some(mask)
    }

    /// One step of [`Self::owns_defined`] over `ty`. With a `table` (the
    /// definitions being solved for, [`Self::owns_summary`]) a struct, enum
    /// or union met is answered from it and noted in `deps`, and a type
    /// parameter owns nothing of its own (what its argument owns is added
    /// where the type is used).
    fn owns_defined_in(
        &mut self,
        ty: Ty<'tcx>,
        open: bool,
        table: Option<&FxHashMap<DefId, u64>>,
        mask: &mut u64,
        deps: &mut Vec<DefId>,
        depth: usize,
    ) -> Option<()> {
        if depth > 512 {
            return None;
        }
        match *ty.kind() {
            ty::Adt(adt, args) => {
                let own = match table {
                    Some(table) => {
                        deps.push(adt.did());
                        table.get(&adt.did()).copied().unwrap_or(0)
                    }
                    None => self.owns_summary(adt.did())?,
                };
                *mask |= own;
                for arg in args.types() {
                    self.owns_defined_in(arg, open, table, mask, deps, depth + 1)?;
                }
            }
            ty::Tuple(fields) => {
                for field in fields.iter() {
                    self.owns_defined_in(field, open, table, mask, deps, depth + 1)?;
                }
            }
            ty::Array(inner, _) | ty::Slice(inner) | ty::Pat(inner, _) => {
                self.owns_defined_in(inner, open, table, mask, deps, depth + 1)?
            }
            ty::Dynamic(predicates, ..) => *mask |= self.dyn_owns(predicates.principal_def_id()),
            ty::Param(_) if table.is_some() || open => {}
            ty::Param(_)
            | ty::Closure(..)
            | ty::CoroutineClosure(..)
            | ty::Coroutine(..)
            | ty::Alias(..)
            | ty::Placeholder(_)
            | ty::Infer(_)
            | ty::Bound(..) => return None,
            // (A `&`, `&mut` or `*` owns nothing; nor does a scalar, a fn.)
            _ => {}
        }
        Some(())
    }

    /// What the definition `did` owns whatever its parameters are (its
    /// sealed bit, and what its fields own with the parameters left open),
    /// solved with every definition it leads to as the least answer of
    /// [`Self::owns_defined_in`]'s steps (iterated from nothing until no
    /// answer grows: each step only adds). `None`: not readable so.
    fn owns_summary(&mut self, did: DefId) -> Option<u64> {
        if let Some(known) = self.owned_defs.get(&did) {
            return *known;
        }
        let tcx = self.tcx;
        let mut order: Vec<DefId> = vec![did];
        let mut solved: FxHashSet<DefId> = FxHashSet::default();
        let mut table: FxHashMap<DefId, u64> = FxHashMap::default();
        table.insert(did, 0);
        let answer = 'solve: loop {
            let mut grew = false;
            let mut index = 0;
            while index < order.len() {
                let at = order[index];
                index += 1;
                let mut deps = Vec::new();
                let adt = tcx.adt_def(at);
                let identity = GenericArgs::identity_for_item(tcx, at);
                let mut step = self.sealed(at).map_or(0u64, |seal| 1 << seal);
                for field in adt.all_fields() {
                    let field = seen_from(tcx, at, field.ty(tcx, identity).skip_norm_wip());
                    if self
                        .owns_defined_in(field, false, Some(&table), &mut step, &mut deps, 0)
                        .is_none()
                    {
                        break 'solve None;
                    }
                }
                for dep in deps {
                    if table.contains_key(&dep) {
                        continue;
                    }
                    match self.owned_defs.get(&dep) {
                        Some(Some(known)) => {
                            solved.insert(dep);
                            table.insert(dep, *known);
                        }
                        Some(None) => break 'solve None,
                        None => {
                            if order.len() >= PLAIN_BOUND {
                                break 'solve None;
                            }
                            table.insert(dep, 0);
                            order.push(dep);
                            grew = true;
                        }
                    }
                }
                let old = table[&at];
                if old | step != old {
                    table.insert(at, old | step);
                    grew = true;
                }
            }
            if !grew {
                break Some(table[&did]);
            }
        };
        match answer {
            Some(_) => {
                for (at, owned) in table {
                    if !solved.contains(&at) {
                        self.owned_defs.insert(at, Some(owned));
                    }
                }
            }
            None => {
                self.owned_defs.insert(did, None);
            }
        }
        answer
    }

    /// [`Self::owns`] of a concrete type, or, in an open reading (`mode`: the
    /// item whose parameters it names), [`Self::owns_whatever`] (a type
    /// parameter owns nothing; a projection the item's bounds keep RIGID
    /// owns every sealed type where it can be tied to one,
    /// [`Self::alias_mask`]).
    fn owns_mode(&mut self, ty: Ty<'tcx>, mode: Option<DefId>) -> u64 {
        match mode {
            Some(scope) if ty.has_non_region_param() || ty.has_aliases() => {
                self.owns_whatever(ty, scope, false)
            }
            _ => self.owns(ty),
        }
    }

    /// [`Self::reach_of`] of a type that names a type parameter of the item
    /// `scope`: what can be written through it WHATEVER the parameters stand
    /// for (a type parameter reaches nothing, a rigid projection what
    /// [`Self::alias_mask`] says; `&mut (T, App)` reaches what `App` owns).
    /// Kept by item ([`Self::reached_open`]).
    fn reach_open(&mut self, ty: Ty<'tcx>, scope: DefId, shared: bool) -> u64 {
        let ty = seen_from(self.tcx, scope, ty);
        if !ty.has_non_region_param() && !ty.has_aliases() {
            return self.reach_of(ty, shared);
        }
        if let Some(&known) = self.reached_open.get(&(ty, scope, shared)) {
            return known;
        }
        let mut visited: FxHashSet<(Ty<'tcx>, bool)> = FxHashSet::default();
        let mut mask = 0u64;
        let was_cut = std::mem::replace(&mut self.cut, false);
        self.reach_in(
            ty,
            shared,
            &mut visited,
            &mut mask,
            Abstract::Nothing { scope, aliases: false },
        );
        let cut_here = self.cut;
        self.cut = was_cut || cut_here;
        if cut_here && visited.len() > WALK_BOUND {
            // (A nested type: off its definitions, as `reach_of` reads one.)
            if let Some(defined) = self.reach_defined(ty, shared, true) {
                self.cut = was_cut;
                self.reached_open.insert((ty, scope, shared), defined);
                return defined;
            }
        }
        if !cut_here {
            self.reached_open.insert((ty, scope, shared), mask);
        }
        mask
    }

    /// [`Self::reach_of`], or in an open reading [`Self::reach_open`].
    fn reach_mode(&mut self, ty: Ty<'tcx>, mode: Option<DefId>, shared: bool) -> u64 {
        match mode {
            Some(scope) if ty.has_non_region_param() || ty.has_aliases() => {
                self.reach_open(ty, scope, shared)
            }
            _ => self.reach_of(ty, shared),
        }
    }

    /// What every `dyn` of a trait of another crate (or of no trait) in a
    /// value of type `ty` may have been handed, at any depth: what a value
    /// handed to such a `dyn` anywhere in the walk lets be written
    /// ([`Self::erased_foreign`]).
    fn dyn_handed(&self, ty: Ty<'tcx>) -> u64 {
        let mut mask = 0u64;
        for part in ty.walk() {
            let ty::GenericArgKind::Type(part) = part.kind() else { continue };
            if let ty::Dynamic(predicates, ..) = *part.kind() {
                let principal = predicates.principal_def_id();
                if !principal.is_some_and(|principal| principal.is_local()) {
                    mask |= self.erased_foreign.get(&principal).copied().unwrap_or(0);
                }
            }
        }
        mask
    }

    /// What the walk knows of what each `dyn` was handed.
    fn erasures(&self) -> Erasures {
        (
            self.erased.clone(),
            self.erased_reach.clone(),
            self.erased_foreign.clone(),
            self.erased_foreign_held.clone(),
        )
    }

    /// Read each coercion the walk logged again, with nothing kept of what a
    /// type owns or reaches, until what each `dyn` was handed stops growing.
    /// Each round only adds (a finite set of traits, 64 seals each), so it
    /// ends; a round asks a few questions about two types per coercion, not
    /// a walk of the instances.
    fn settle_erasures(&mut self) {
        loop {
            let before = self.erasures();
            self.owns.clear();
            self.reaches.clear();
            self.summaries.clear();
            self.owned_defs.clear();
            self.owns_open.clear();
            self.reached_open.clear();
            self.env_links.clear();
            self.assoc_links.clear();
            let log = self.unsize_log.clone();
            for (source, target, in_third, open) in log {
                for erasure in self.erasures_of(source, target, in_third, open) {
                    self.record_erasure(&erasure);
                }
            }
            if self.erasures() == before {
                break;
            }
        }
    }

    /// The seals whose type a value that a pointer in a value of type `ty`
    /// POINTS TO owns: of a `&`, a `&mut` or a raw pointer, and of one kept
    /// in a field (`NonNull<App>`), a few fields deep. (`mode`: an open
    /// reading's item, [`Self::owns_mode`].)
    fn pointed(&mut self, ty: Ty<'tcx>, mode: Option<DefId>) -> u64 {
        fn walk<'tcx>(
            this: &mut Checker<'_, 'tcx>,
            ty: Ty<'tcx>,
            depth: usize,
            mask: &mut u64,
            mode: Option<DefId>,
        ) {
            match *ty.kind() {
                ty::Ref(_, pointee, _) | ty::RawPtr(pointee, _) => {
                    *mask |= this.owns_mode(pointee, mode)
                }
                ty::Adt(adt, args) if depth < 4 && !adt.is_enum() => {
                    for field in adt.all_fields() {
                        let field = field.ty(this.tcx, args).skip_norm_wip();
                        let field = match mode {
                            Some(scope) => seen_from(this.tcx, scope, field),
                            None => at_instance(this.tcx, None, field),
                        };
                        walk(this, field, depth + 1, mask, mode);
                    }
                }
                ty::Tuple(parts) if depth < 4 => {
                    for part in parts.iter() {
                        walk(this, part, depth + 1, mask, mode);
                    }
                }
                _ => {}
            }
        }
        let mut mask = 0u64;
        walk(self, ty, 0, &mut mask, mode);
        mask
    }

    /// The seals among `mask` whose values have a place that matters (S4):
    /// those with a writer.
    fn placed(&self, mask: u64) -> u64 {
        let mut placed = 0u64;
        for (index, seal) in self.seals.iter().enumerate() {
            if !seal.writers.is_empty() {
                placed |= 1 << index;
            }
        }
        mask & placed
    }

    /// `open`: what a type that is not concrete owns.
    fn owns_in(
        &mut self,
        ty: Ty<'tcx>,
        visited: &mut FxHashSet<Ty<'tcx>>,
        mask: &mut u64,
        open: Abstract,
    ) {
        // (What is known was asked of concrete types: the whole answer, or
        // "all of them" at a walk's bound, which is never less. Review 5 of
        // the review-14 build: a known answer that was not nothing was walked
        // again, `App`'s whole type for every open fact at `(T, App)`.)
        if !ty.has_non_region_param() {
            if let Some(known) = self.owns.get(&ty) {
                *mask |= *known;
                return;
            }
            // (In an open walk, a concrete part is asked as itself, and kept.)
            if matches!(open, Abstract::Nothing { .. }) && !ty.has_aliases() {
                *mask |= self.owns(ty);
                return;
            }
        }
        if !visited.insert(ty) {
            return;
        }
        if visited.len() > WALK_BOUND {
            self.cut = true;
            *mask = self.all();
            return;
        }
        let tcx = self.tcx;
        rustc_data_structures::stack::ensure_sufficient_stack(|| match *ty.kind() {
            ty::Adt(adt, args) => {
                if let Some(seal) = self.sealed(adt.did()) {
                    *mask |= 1 << seal;
                }
                for inner in args.types() {
                    self.owns_in(inner, visited, mask, open);
                }
                for field in adt.all_fields() {
                    let field = field.ty(tcx, args).skip_norm_wip();
                    let field = match open {
                        Abstract::Everything => at_instance(tcx, None, field),
                        Abstract::Nothing { scope, .. } => seen_from(tcx, scope, field),
                    };
                    self.owns_in(field, visited, mask, open);
                }
            }
            ty::Tuple(fields) => {
                for field in fields.iter() {
                    self.owns_in(field, visited, mask, open);
                }
            }
            ty::Array(inner, _) | ty::Slice(inner) | ty::Pat(inner, _) => {
                self.owns_in(inner, visited, mask, open)
            }
            ty::Closure(_, args) => {
                for upvar in args.as_closure().upvar_tys().iter() {
                    self.owns_in(upvar, visited, mask, open);
                }
            }
            ty::CoroutineClosure(_, args) => {
                for upvar in args.as_coroutine_closure().upvar_tys().iter() {
                    self.owns_in(upvar, visited, mask, open);
                }
            }
            ty::Coroutine(def, args) => {
                for upvar in args.as_coroutine().upvar_tys().iter() {
                    self.owns_in(upvar, visited, mask, open);
                }
                // What it keeps across a suspension.
                let kept = tcx.coroutine_hidden_types(def).instantiate(tcx, args).skip_norm_wip();
                for kept in tcx.instantiate_bound_regions_with_erased(kept).types.iter() {
                    let kept = match open {
                        Abstract::Everything => at_instance(tcx, None, kept),
                        Abstract::Nothing { scope, .. } => seen_from(tcx, scope, kept),
                    };
                    self.owns_in(kept, visited, mask, open);
                }
            }
            // (Of a trait of this crate: what a value that owns one was
            // handed to a `dyn` of it as. Of another crate's, or of none:
            // what was handed to one on the trait's entry in `trusts`, or
            // beneath a trusted fn, which S4d lets pass.)
            ty::Dynamic(predicates, ..) => *mask |= self.dyn_owns(predicates.principal_def_id()),
            // Not a concrete type: what it stands for is not known here.
            ty::Alias(..) => match open {
                Abstract::Everything => {
                    self.cut = true;
                    *mask = self.all();
                }
                Abstract::Nothing { aliases: true, .. } => *mask = self.all(),
                Abstract::Nothing { scope, aliases: false } => match self.alias_read(ty, scope) {
                    AliasRead::Is(normalized) => self.owns_in(normalized, visited, mask, open),
                    AliasRead::Rigid => *mask |= self.alias_mask(ty, scope),
                    AliasRead::Unsettled => {}
                },
            },
            ty::Param(_) => {
                if matches!(open, Abstract::Everything) {
                    self.cut = true;
                    *mask = self.all();
                }
            }
            ty::Placeholder(_) | ty::Infer(_) | ty::Bound(..) => {
                self.cut |= matches!(open, Abstract::Everything);
                *mask = self.all();
            }
            _ => {}
        });
    }

    /// What a `dyn` of the trait `principal` (of no trait: `None`) owns:
    /// what a value that owns one was handed to one as, behind an owning
    /// pointer ([`Self::erased`], [`Self::erased_foreign_held`]).
    fn dyn_owns(&self, principal: Option<DefId>) -> u64 {
        match principal {
            Some(principal) if principal.is_local() => {
                self.erased.get(&principal).copied().unwrap_or(0)
            }
            principal => self.erased_foreign_held.get(&principal).copied().unwrap_or(0),
        }
    }

    /// What a projection (or another alias) left in a type an open reading
    /// reads is, in the typing environment of the item `scope`: what it
    /// normalizes to; RIGID (the item's bounds say an impl exists, and
    /// nothing says what the projection is: a where-clause, a parameter's
    /// bound, or one that shadows the impl that would settle it); or
    /// UNSETTLED (the bounds there do not say an impl exists: a vtable's
    /// method whose own where-clause the `dyn` does not prove, `fn m(&self)
    /// where X: Tr2`, names `<X as Tr2>::Out`, and runs only where `X: Tr2`
    /// is proved, in an instance read as such).
    fn alias_read(&self, ty: Ty<'tcx>, scope: DefId) -> AliasRead<'tcx> {
        let tcx = self.tcx;
        match tcx.try_normalize_erasing_regions(
            ty::TypingEnv::post_analysis(tcx, scope),
            ty::Unnormalized::new_wip(ty),
        ) {
            Ok(normalized) if normalized != ty => AliasRead::Is(normalized),
            Ok(_) => AliasRead::Rigid,
            Err(_) => AliasRead::Unsettled,
        }
    }

    /// The seals a RIGID alias `ty` may own or reach, read whatever the
    /// parameters of the item `scope` stand for, fail-closed: at an instance
    /// it is the value some impl gives it, which is made of its own
    /// arguments' parts, of an impl's own types, and of what the item's
    /// bounds say a projection is. So it may hold what its own arguments
    /// own or reach (`<(T, App) as Id>::Out`, where a where-clause the
    /// compiler does not need shadows the blanket impl that makes it `(T,
    /// App)`; `<Option<(T, App)> as IntoIterator>::Item`); what an impl of
    /// this crate's trait makes it ([`Self::local_assoc_mask`]: `impl<X> Out
    /// for X { type O = App; }`); and what the item's bounds tie a parameter
    /// to ([`Self::env_mask`]: `K: Sw<Item = (T, App)>`, under which a
    /// dependency's blanket impl can make `<K as Tr2>::N` the `(T, App)`).
    /// (Review 5 of the review-14 build: a rigid projection was taken to own
    /// nothing, and each of the first two shapes swapped two holders under a
    /// seal that held.) Nothing else: an impl of another crate's trait (and
    /// no impl of this crate can be for types that name nothing of this
    /// crate, the orphan rules) names no type of this crate itself, and where
    /// a parameter is a type of this crate, the instance is the crate's that
    /// makes it, as for a parameter ([`Abstract::Nothing`]).
    fn alias_mask(&mut self, ty: Ty<'tcx>, scope: DefId) -> u64 {
        let ty::Alias(_, alias) = *ty.kind() else { return self.all() };
        let mut mask = 0u64;
        if alias_def(alias.kind).is_local() {
            match alias.kind {
                ty::AliasTyKind::Projection { def_id } => mask |= self.local_assoc_mask(def_id),
                _ => return self.all(),
            }
        }
        for arg in alias.args.types() {
            mask |= self.owns_whatever(arg, scope, false) | self.reach_open(arg, scope, false);
        }
        mask | self.env_mask(scope)
    }

    /// What an associated type `assoc` of a trait of THIS crate may own or
    /// reach in some impl of the crate, read where that impl stands (its own
    /// parameters own nothing; `impl<X> Out for X { type O = App; }` owns
    /// `App`'s, `type Op = fn(&mut P, &mut P)` nothing): what a rigid
    /// projection of it stands for at an instance is such an impl's value at
    /// the projection's own arguments, or that of an impl of a crate that
    /// depends on this one, at an instance only that crate makes
    /// ([`Abstract::Nothing`]). Its default too, where the trait gives one.
    /// (Asked again while it is being answered: every seal, fail-closed.)
    fn local_assoc_mask(&mut self, assoc: DefId) -> u64 {
        if let Some(&known) = self.assoc_links.get(&assoc) {
            return known;
        }
        let all = self.all();
        self.assoc_links.insert(assoc, all);
        let tcx = self.tcx;
        let mut values: Vec<DefId> = Vec::new();
        if tcx.defaultness(assoc).has_value() {
            values.push(assoc);
        }
        let of = tcx.parent(assoc);
        let impls: Vec<LocalDefId> =
            tcx.all_local_trait_impls(()).get(&of).cloned().unwrap_or_default();
        for implementation in impls {
            if let Some(&item) =
                tcx.impl_item_implementor_ids(implementation.to_def_id()).get(&assoc)
            {
                values.push(item);
            }
        }
        let mut mask = 0u64;
        for item in values {
            let value = tcx.type_of(item).instantiate_identity().skip_norm_wip();
            mask |= self.owns_whatever(value, item, false) | self.reach_open(value, item, false);
        }
        self.assoc_links.insert(assoc, mask);
        mask
    }

    /// What the typing environment of an open reading's item can tie a type
    /// parameter to: the seals its bounds' types own or reach, so that what
    /// a crate's code does at the bare parameter (or at a projection of it)
    /// may be done to one whatever the parameters stand for (`M: Make<Out =
    /// App>`, `K: Sw<Item = (T, App)>`, `P: DerefMut<Target = App>`, `F:
    /// FnOnce(&mut App)`). Each concrete part of a bound by what it owns and
    /// lets be written ([`Self::owns`], [`Self::reach_of`]); a struct, enum
    /// or union of this crate with parameters by its definition ([`Self::
    /// owns_summary`], [`Self::summarize`]; every seal where it is not read
    /// so); a closure or fn of this crate, every seal; a `dyn`, what was
    /// handed to one. (A projection in a bound adds nothing of its own: what
    /// it is, the bounds and its arguments say.) Where the bounds tie none,
    /// a parameter, and a projection of one, stands for a type that the
    /// crate instantiating the item makes (review 5 of the review-14 build:
    /// `dep::direct::<M>` under `M: Make<Out = App>`, a dependency's swap at
    /// `M::Out`, was never followed, and a crate that depends on the library
    /// swapped two holders through it).
    fn env_mask(&mut self, scope: DefId) -> u64 {
        if let Some(&known) = self.env_links.get(&scope) {
            return known;
        }
        let tcx = self.tcx;
        let all = self.all();
        let env = ty::TypingEnv::post_analysis(tcx, scope).param_env;
        let mut mask = 0u64;
        for clause in env.caller_bounds() {
            let mut parts = TypesIn(Vec::new());
            clause.visit_with(&mut parts);
            for part in parts.0 {
                if !part.has_non_region_param()
                    && !part.has_aliases()
                    && !part.has_escaping_bound_vars()
                {
                    let part = tcx.erase_and_anonymize_regions(part);
                    mask |= self.owns(part) | self.reach_of(part, false);
                    continue;
                }
                mask |= match *part.kind() {
                    ty::Adt(adt, _) if adt.did().is_local() => {
                        self.owns_summary(adt.did()).unwrap_or(all)
                            | self.summarize((adt.did(), false)).map_or(all, |sum| sum.mask)
                    }
                    ty::Closure(def, _)
                    | ty::CoroutineClosure(def, _)
                    | ty::Coroutine(def, _)
                    | ty::FnDef(def, _)
                    | ty::Foreign(def)
                        if def.is_local() =>
                    {
                        all
                    }
                    ty::Dynamic(predicates, ..) => match predicates.principal_def_id() {
                        Some(principal) if principal.is_local() => {
                            self.erased.get(&principal).copied().unwrap_or(0)
                                | self.erased_reach.get(&principal).copied().unwrap_or(0)
                        }
                        principal => {
                            self.erased_foreign.get(&principal).copied().unwrap_or(0)
                                | self.dyn_owns(principal)
                        }
                    },
                    _ => 0,
                };
            }
        }
        self.env_links.insert(scope, mask);
        mask
    }

    /// The seals a value of which sound code can WRITE when it holds a value
    /// of the CONCRETE type `ty`: one the value owns ([`Self::owns`]), and
    /// one it points to, at any depth: behind a `&mut` or a raw pointer,
    /// behind a `&` when a cell or a raw pointer lies on the way, in a field
    /// or a type argument of a type of any crate, among the inputs and the
    /// output of a fn pointer. What a type SAYS can be reached through it:
    /// the question asked of code of another crate that does what the
    /// compiler does not check (S4e), and of a value handed to a `dyn` (S4d).
    /// Fail-closed like [`Self::owns`]: "all of them" at [`WALK_BOUND`] and
    /// at a type that is not concrete.
    ///
    /// `shared`: the same through a `&` to a value of type `ty`: what sound
    /// code handed only that `&` can write. Nothing of plain data; what an
    /// `UnsafeCell` on the way holds; what a raw pointer on the way points
    /// to (it can be copied out). Std's owning pointers and containers lend
    /// what they hold as a `&` again (`&Box<App>`, `&Vec<App>`, `&Rc<App>`);
    /// a type argument that any other type keeps only in a `PhantomData`
    /// is taken to be kept behind a pointer of the type's own, which writes.
    fn reach_of(&mut self, ty: Ty<'tcx>, shared: bool) -> u64 {
        if let Some(known) = self.reaches.get(&(ty, shared)) {
            return *known;
        }
        let mut visited: FxHashSet<(Ty<'tcx>, bool)> = FxHashSet::default();
        let mut mask = 0u64;
        let was_cut = std::mem::replace(&mut self.cut, false);
        self.reach_in(ty, shared, &mut visited, &mut mask, Abstract::Everything);
        let cut_here = self.cut;
        self.cut = was_cut || cut_here;
        if cut_here && visited.len() > WALK_BOUND {
            // A type that grows as it is walked, a NESTED type (`Node<T>`
            // with a field `&Node<Option<T>>`): each step is a new, larger
            // type, and the walk has no end. Its definitions are finitely
            // many: read it off them instead ([`Self::reach_defined`]), the
            // same answer the walk would give had it an end. (Review 1 of
            // the review-14 build: a plain `&Node<App>` as a `&dyn Debug`
            // was refused at the bound.)
            if let Some(defined) = self.reach_defined(ty, shared, false) {
                self.cut = was_cut;
                self.reaches.insert((ty, shared), defined);
                return defined;
            }
        }
        if mask == 0 {
            for seen in visited {
                self.reaches.insert(seen, 0);
            }
        } else {
            // (Only the type asked, as in `owns`.)
            self.reaches.insert((ty, shared), mask);
        }
        mask
    }

    fn reach_in(
        &mut self,
        ty: Ty<'tcx>,
        shared: bool,
        visited: &mut FxHashSet<(Ty<'tcx>, bool)>,
        mask: &mut u64,
        open: Abstract,
    ) {
        // (What is known was asked of concrete types.)
        if let Some(known) = self.reaches.get(&(ty, shared)) {
            *mask |= *known;
            return;
        }
        // (In an open walk, a concrete part is asked as itself, and kept.)
        if matches!(open, Abstract::Nothing { .. })
            && !ty.has_non_region_param()
            && !ty.has_aliases()
        {
            *mask |= self.reach_of(ty, shared);
            return;
        }
        if !visited.insert((ty, shared)) {
            return;
        }
        if visited.len() > WALK_BOUND {
            self.cut = true;
            *mask = self.all();
            return;
        }
        let tcx = self.tcx;
        rustc_data_structures::stack::ensure_sufficient_stack(|| match *ty.kind() {
            ty::Adt(adt, args) => {
                // (Behind a `&` a sealed value is plain data, S5.)
                if let (false, Some(seal)) = (shared, self.sealed(adt.did())) {
                    *mask |= 1 << seal;
                }
                let lends = shared && self.lends(adt);
                if lends {
                    for inner in args.types() {
                        self.reach_in(inner, true, visited, mask, open);
                    }
                    return;
                }
                let cell = adt.is_unsafe_cell();
                if !shared || cell || adt.is_phantom_data() {
                    for inner in args.types() {
                        self.reach_in(inner, false, visited, mask, open);
                    }
                }
                for field in adt.all_fields() {
                    let field = field.ty(tcx, args).skip_norm_wip();
                    let field = match open {
                        Abstract::Everything => at_instance(tcx, None, field),
                        Abstract::Nothing { scope, .. } => seen_from(tcx, scope, field),
                    };
                    self.reach_in(field, shared && !cell, visited, mask, open);
                }
            }
            // (Through a `&`, a `&mut` in the value lends a `&`.)
            ty::Ref(_, inner, mutability) => {
                self.reach_in(inner, shared || mutability.is_not(), visited, mask, open)
            }
            // (A raw pointer is copied out of whatever lends it.)
            ty::RawPtr(inner, _) => self.reach_in(inner, false, visited, mask, open),
            ty::Tuple(fields) => {
                for field in fields.iter() {
                    self.reach_in(field, shared, visited, mask, open);
                }
            }
            ty::Array(inner, _) | ty::Slice(inner) | ty::Pat(inner, _) => {
                self.reach_in(inner, shared, visited, mask, open)
            }
            ty::Closure(_, args) => {
                for upvar in args.as_closure().upvar_tys().iter() {
                    self.reach_in(upvar, shared, visited, mask, open);
                }
            }
            ty::CoroutineClosure(_, args) => {
                for upvar in args.as_coroutine_closure().upvar_tys().iter() {
                    self.reach_in(upvar, shared, visited, mask, open);
                }
            }
            ty::Coroutine(def, args) => {
                for upvar in args.as_coroutine().upvar_tys().iter() {
                    self.reach_in(upvar, shared, visited, mask, open);
                }
                let kept = tcx.coroutine_hidden_types(def).instantiate(tcx, args).skip_norm_wip();
                for kept in tcx.instantiate_bound_regions_with_erased(kept).types.iter() {
                    let kept = match open {
                        Abstract::Everything => at_instance(tcx, None, kept),
                        Abstract::Nothing { scope, .. } => seen_from(tcx, scope, kept),
                    };
                    self.reach_in(kept, shared, visited, mask, open);
                }
            }
            // What a fn takes and hands back: a fn pointer given another
            // signature is handed what its new one says.
            ty::FnPtr(..) => {
                let sig = tcx.instantiate_bound_regions_with_erased(ty.fn_sig(tcx));
                for part in sig.inputs_and_output.iter() {
                    let part = match open {
                        Abstract::Everything => at_instance(tcx, None, part),
                        Abstract::Nothing { scope, .. } => seen_from(tcx, scope, part),
                    };
                    self.reach_in(part, false, visited, mask, open);
                }
            }
            ty::FnDef(_, args) => {
                for inner in args.skip_binder().types() {
                    self.reach_in(inner, false, visited, mask, open);
                }
            }
            // (Of a trait of this crate: what was handed to a `dyn` of it. A
            // `dyn` of any other trait is handed nothing that reaches one
            // without the hander being told (S4d), but what it was let own,
            // on its entry in `trusts` or beneath a trusted fn.)
            ty::Dynamic(predicates, ..) => {
                let principal = predicates.principal_def_id();
                *mask |= self.dyn_owns(principal);
                if let Some(principal) = principal.filter(|principal| principal.is_local()) {
                    *mask |= self.erased_reach.get(&principal).copied().unwrap_or(0);
                }
            }
            // Not a concrete type: what it stands for is not known here.
            ty::Alias(..) => match open {
                Abstract::Everything => {
                    self.cut = true;
                    *mask = self.all();
                }
                Abstract::Nothing { aliases: true, .. } => *mask = self.all(),
                Abstract::Nothing { scope, aliases: false } => match self.alias_read(ty, scope) {
                    AliasRead::Is(normalized) => {
                        self.reach_in(normalized, shared, visited, mask, open)
                    }
                    AliasRead::Rigid => *mask |= self.alias_mask(ty, scope),
                    AliasRead::Unsettled => {}
                },
            },
            ty::Param(_) => {
                if matches!(open, Abstract::Everything) {
                    self.cut = true;
                    *mask = self.all();
                }
            }
            ty::Placeholder(_) | ty::Infer(_) | ty::Bound(..) => {
                self.cut |= matches!(open, Abstract::Everything);
                *mask = self.all();
            }
            _ => {}
        });
    }

    /// Whether a `&` to a value of the struct or enum `adt` lends what it
    /// holds only as a `&` again: std's owning pointers and containers.
    fn lends(&mut self, adt: ty::AdtDef<'tcx>) -> bool {
        adt.is_box()
            || (!adt.did().is_local()
                && !self.third_party(adt.did())
                && matches!(
                    self.tcx.item_name(adt.did()).as_str(),
                    "Vec"
                        | "String"
                        | "VecDeque"
                        | "BTreeMap"
                        | "BTreeSet"
                        | "HashMap"
                        | "HashSet"
                        | "BinaryHeap"
                        | "LinkedList"
                        | "Rc"
                        | "Arc"
                ))
    }

    /// [`Self::reach_of`] by DEFINITIONS: the walk of [`Self::reach_in`],
    /// where each struct, enum or union met is answered by its
    /// [`Summary`] applied to its type arguments, rather than by walking
    /// its fields at those arguments. A type that grows as it is walked
    /// (each instance names a larger one) has finitely many definitions,
    /// so this has an end where the walk has none, and it gives what the
    /// walk would: the walk's answer is the least one that satisfies each
    /// step, and so is each summary's, of the same steps with the
    /// parameters left open. `None` where a part is not read so (a
    /// projection that the definition does not settle, a closure).
    fn reach_defined(&mut self, ty: Ty<'tcx>, shared: bool, open: bool) -> Option<u64> {
        let mut acc = Summary::default();
        self.defined_in(ty, shared, None, &mut acc, &mut Vec::new(), 0, open)?;
        Some(acc.mask)
    }

    /// One step of [`Self::reach_defined`] over `ty`. With a `table` (the
    /// summaries being solved for, by [`Self::summarize`]) a struct or enum
    /// met is answered from it and noted in `deps`, and a type parameter is
    /// a bit of `acc`; without one, `ty` is concrete, and each definition
    /// met is solved on its own.
    fn defined_in(
        &mut self,
        ty: Ty<'tcx>,
        shared: bool,
        table: Option<&FxHashMap<(DefId, bool), Summary>>,
        acc: &mut Summary,
        deps: &mut Vec<(DefId, bool)>,
        depth: usize,
        open: bool,
    ) -> Option<()> {
        // (A type a definition writes is small; one a walk of the concrete
        // type would open is a part of it, smaller still.)
        if depth > 512 {
            return None;
        }
        let tcx = self.tcx;
        match *ty.kind() {
            ty::Adt(adt, args) => {
                let key = (adt.did(), shared);
                let summary = match table {
                    Some(table) => {
                        deps.push(key);
                        table.get(&key).copied().unwrap_or_default()
                    }
                    None => self.summarize(key)?,
                };
                acc.mask |= summary.mask;
                for (index, arg) in args.iter().enumerate() {
                    let Some(arg) = arg.as_type() else { continue };
                    if index >= 64 {
                        return None;
                    }
                    if summary.shared & (1 << index) != 0 {
                        self.defined_in(arg, true, table, acc, deps, depth + 1, open)?;
                    }
                    if summary.owned & (1 << index) != 0 {
                        self.defined_in(arg, false, table, acc, deps, depth + 1, open)?;
                    }
                }
            }
            // (A parameter of an open reading's item reaches nothing, as in
            // `reach_open`.)
            ty::Param(_) if table.is_none() && open => {}
            ty::Param(param) => {
                if table.is_none() || param.index >= 64 {
                    return None;
                }
                let bit = 1u64 << param.index;
                if shared {
                    acc.shared |= bit;
                } else {
                    acc.owned |= bit;
                }
            }
            ty::Ref(_, inner, mutability) => self.defined_in(
                inner,
                shared || mutability.is_not(),
                table,
                acc,
                deps,
                depth + 1,
                open,
            )?,
            ty::RawPtr(inner, _) => {
                self.defined_in(inner, false, table, acc, deps, depth + 1, open)?
            }
            ty::Tuple(fields) => {
                for field in fields.iter() {
                    self.defined_in(field, shared, table, acc, deps, depth + 1, open)?;
                }
            }
            ty::Array(inner, _) | ty::Slice(inner) | ty::Pat(inner, _) => {
                self.defined_in(inner, shared, table, acc, deps, depth + 1, open)?
            }
            ty::FnPtr(..) => {
                let sig = tcx.instantiate_bound_regions_with_erased(ty.fn_sig(tcx));
                for part in sig.inputs_and_output.iter() {
                    self.defined_in(part, false, table, acc, deps, depth + 1, open)?;
                }
            }
            ty::FnDef(_, args) => {
                for inner in args.skip_binder().types() {
                    self.defined_in(inner, false, table, acc, deps, depth + 1, open)?;
                }
            }
            ty::Dynamic(predicates, ..) => {
                let principal = predicates.principal_def_id();
                acc.mask |= self.dyn_owns(principal);
                if let Some(principal) = principal.filter(|principal| principal.is_local()) {
                    acc.mask |= self.erased_reach.get(&principal).copied().unwrap_or(0);
                }
            }
            ty::Closure(..)
            | ty::CoroutineClosure(..)
            | ty::Coroutine(..)
            | ty::Alias(..)
            | ty::Placeholder(_)
            | ty::Infer(_)
            | ty::Bound(..) => return None,
            _ => {}
        }
        Some(())
    }

    /// The [`Summary`] of the definition `key.0` (`key.1`: behind a `&` all
    /// the way), solved with every definition it leads to, as the least
    /// answer of [`Self::summary_step`] for each (iterated from nothing
    /// until no answer grows: each step only adds).
    fn summarize(&mut self, key: (DefId, bool)) -> Option<Summary> {
        if let Some(known) = self.summaries.get(&key) {
            return *known;
        }
        let mut order: Vec<(DefId, bool)> = vec![key];
        let mut solved: FxHashMap<(DefId, bool), Summary> = FxHashMap::default();
        let mut table: FxHashMap<(DefId, bool), Summary> = FxHashMap::default();
        table.insert(key, Summary::default());
        let answer = 'solve: loop {
            let mut grew = false;
            let mut index = 0;
            while index < order.len() {
                let at = order[index];
                index += 1;
                let mut deps = Vec::new();
                let Some(step) = self.summary_step(at, &table, &mut deps) else {
                    break 'solve None;
                };
                for dep in deps {
                    if table.contains_key(&dep) {
                        continue;
                    }
                    match self.summaries.get(&dep) {
                        Some(Some(known)) => {
                            solved.insert(dep, *known);
                            table.insert(dep, *known);
                        }
                        Some(None) => break 'solve None,
                        None => {
                            if order.len() >= PLAIN_BOUND {
                                break 'solve None;
                            }
                            table.insert(dep, Summary::default());
                            order.push(dep);
                            grew = true;
                        }
                    }
                }
                let old = table[&at];
                let new = Summary {
                    mask: old.mask | step.mask,
                    shared: old.shared | step.shared,
                    owned: old.owned | step.owned,
                };
                if new != old {
                    table.insert(at, new);
                    grew = true;
                }
            }
            if !grew {
                break Some(table[&key]);
            }
        };
        match answer {
            Some(_) => {
                for (at, summary) in table {
                    if !solved.contains_key(&at) {
                        self.summaries.insert(at, Some(summary));
                    }
                }
            }
            None => {
                self.summaries.insert(key, None);
            }
        }
        answer
    }

    /// One evaluation of the definition `did`'s [`Summary`] (behind a `&`
    /// all the way: `shared`), the other definitions answered from `table`:
    /// [`Self::reach_in`]'s step for a struct, enum or union, with its type
    /// parameters left open and its fields read as the definition writes
    /// them (normalized where the definition settles a projection).
    fn summary_step(
        &mut self,
        (did, shared): (DefId, bool),
        table: &FxHashMap<(DefId, bool), Summary>,
        deps: &mut Vec<(DefId, bool)>,
    ) -> Option<Summary> {
        let tcx = self.tcx;
        let adt = tcx.adt_def(did);
        let identity = GenericArgs::identity_for_item(tcx, did);
        if identity.len() > 64 {
            return None;
        }
        let params = identity
            .iter()
            .enumerate()
            .filter(|(_, arg)| arg.as_type().is_some())
            .fold(0u64, |mask, (index, _)| mask | (1 << index));
        let mut acc = Summary::default();
        // (Behind a `&` a sealed value is plain data, S5.)
        if let (false, Some(seal)) = (shared, self.sealed(did)) {
            acc.mask |= 1 << seal;
        }
        if shared && self.lends(adt) {
            acc.shared |= params;
            return Some(acc);
        }
        let cell = adt.is_unsafe_cell();
        if !shared || cell || adt.is_phantom_data() {
            acc.owned |= params;
        }
        for field in adt.all_fields() {
            let field = seen_from(tcx, did, field.ty(tcx, identity).skip_norm_wip());
            self.defined_in(field, shared && !cell, Some(table), &mut acc, deps, 0, false)?;
        }
        Some(acc)
    }

    /// S5: whether a value of type `ty` is plain data: no pointer that can
    /// write, no state shared with anything else, and no data of its own
    /// that is written other than through a `&mut` of the value.
    ///
    /// A struct or enum of any crate is plain when every field is (so a
    /// fieldless enum is, and `Duration`, and `Option` of a plain type), but
    /// an `UnsafeCell`, a union, a `Box` (its dereference is no place at
    /// this MIR phase) and a `Cow`. A std container that keeps its data
    /// behind a pointer of its own is plain by NAME, when every type
    /// argument, the defaulted ones too (an allocator, a hasher), is.
    fn plain(&mut self, ty: Ty<'tcx>) -> bool {
        if let Some(known) = self.plain.get(&ty) {
            return *known;
        }
        // One question: a type met again while it is still open is taken to
        // be plain (a type that holds itself through a `Vec`), so a "yes"
        // given underneath leans on the answer to the question itself. It is
        // kept only when that answer is yes; a "no" leans on nothing.
        let mut answers: FxHashMap<Ty<'tcx>, bool> = FxHashMap::default();
        let answer = self.plain_in(ty, &mut answers);
        for (seen, plain) in answers {
            if answer || !plain {
                self.plain.insert(seen, plain);
            }
        }
        answer
    }

    fn plain_in(&mut self, ty: Ty<'tcx>, answers: &mut FxHashMap<Ty<'tcx>, bool>) -> bool {
        if let Some(known) = self.plain.get(&ty) {
            return *known;
        }
        if let Some(open) = answers.get(&ty) {
            return *open;
        }
        if answers.len() >= PLAIN_BOUND {
            // A type that grows as it is walked: not plain (fail-closed).
            self.cut = true;
            return false;
        }
        answers.insert(ty, true);
        let tcx = self.tcx;
        let answer = rustc_data_structures::stack::ensure_sufficient_stack(|| match *ty.kind() {
            ty::Bool | ty::Char | ty::Int(_) | ty::Uint(_) | ty::Float(_) | ty::Str | ty::Never => {
                true
            }
            ty::Tuple(fields) => fields.iter().all(|field| self.plain_in(field, answers)),
            ty::Array(inner, _) | ty::Slice(inner) | ty::Pat(inner, _) => {
                self.plain_in(inner, answers)
            }
            // (A `&` to plain data: nothing is written through it.)
            ty::Ref(_, inner, mutability) => !mutability.is_mut() && self.plain_in(inner, answers),
            ty::Adt(adt, _) if adt.is_union() || adt.is_unsafe_cell() || ty.is_box() => false,
            ty::Adt(adt, args) if crate::def_is_in_sysroot_resident_crate(tcx, adt.did()) => {
                match tcx.item_name(adt.did()).as_str() {
                    "Cow" => false,
                    // Their data is behind a pointer of their own, written
                    // only through a `&mut` of the container.
                    "Vec" | "String" | "HashMap" | "HashSet" | "BTreeMap" | "BTreeSet"
                    | "VecDeque" | "BinaryHeap" | "LinkedList" | "PathBuf" | "OsString"
                    | "CString" => args.types().all(|inner| self.plain_in(inner, answers)),
                    _ => adt.all_fields().all(|field| {
                        let field = at_instance(tcx, None, field.ty(tcx, args).skip_norm_wip());
                        self.plain_in(field, answers)
                    }),
                }
            }
            ty::Adt(adt, args) => adt.all_fields().all(|field| {
                let field = at_instance(tcx, None, field.ty(tcx, args).skip_norm_wip());
                self.plain_in(field, answers)
            }),
            _ => false,
        });
        answers.insert(ty, answer);
        answer
    }

    // ----- the bodies of this crate ---------------------------------------

    fn read_bodies(&mut self) {
        let tcx = self.tcx;
        let mut defs: Vec<LocalDefId> = tcx.mir_keys(()).iter().copied().collect();
        defs.sort_unstable_by_key(|def| def.local_def_index.as_u32());
        let mut constants: Vec<LocalDefId> = Vec::new();
        for def in defs {
            if tcx.is_foreign_item(def) {
                continue;
            }
            let kind = tcx.def_kind(def);
            if matches!(kind, DefKind::Const | DefKind::AssocConst | DefKind::AnonConst)
                && tcx.trivial_const(def).is_none()
            {
                constants.push(def);
            }
            let in_const = matches!(
                tcx.hir_body_const_context(def),
                Some(rustc_hir::ConstContext::Const { .. } | rustc_hir::ConstContext::Static(_))
            );
            // A trivial constant's value is known as it stands: it has no
            // body, and none of its own promoted constants, to read (asking
            // for either is a compiler bug).
            if matches!(kind, DefKind::Const | DefKind::AssocConst | DefKind::AnonConst)
                && tcx.trivial_const(def).is_some()
            {
                continue;
            }
            let mut facts: Vec<Fact<'tcx>> = Vec::new();
            match kind {
                DefKind::Fn
                | DefKind::AssocFn
                | DefKind::Closure
                | DefKind::SyntheticCoroutineBody
                    if !in_const =>
                {
                    // (The body as drop elaboration left it, without the
                    // checks the census adds for its own count of panics:
                    // those name `align_of::<C>`, which is no code the
                    // program wrote.)
                    let body = tcx.mir_drops_elaborated_and_const_checked(def);
                    let body = body.borrow();
                    self.read_body(Some(def), def.to_def_id(), &body, &mut facts);
                }
                // (A closure in a `const` or a `static`: const evaluation
                // owns its body by now.)
                DefKind::Fn | DefKind::AssocFn | DefKind::Closure => {
                    self.read_body(Some(def), def.to_def_id(), tcx.mir_for_ctfe(def), &mut facts);
                }
                DefKind::Const
                | DefKind::AssocConst
                | DefKind::AnonConst
                | DefKind::Static { nested: false, .. } => {
                    self.read_body(Some(def), def.to_def_id(), tcx.mir_for_ctfe(def), &mut facts);
                }
                _ => continue,
            }
            for promoted in tcx.promoted_mir(def).iter() {
                self.read_body(Some(def), def.to_def_id(), promoted, &mut facts);
            }
            if !facts.iter().any(|fact| fact.names_parameter()) {
                self.settled.insert(def.to_def_id());
            }
            self.facts.insert(InstanceKind::Item(def.to_def_id()), Some(facts.into()));
        }
        self.judge_constants(&constants);
    }

    /// S3: no `const` of this crate runs a maker. A value of a sealed type
    /// comes into being in a maker only (the struct expression is in its own
    /// body), so a constant's value holds one only if evaluating its
    /// initializer RAN a maker: called it, or called a fn of this crate that
    /// does. Constant evaluation runs nothing else of this crate: it calls
    /// no trait method, no fn pointer and no closure, and it runs no
    /// destructor. (So a fn only NAMED in the initializer does not run: the
    /// `const` that `thread_local!` writes names the fn that builds each
    /// thread's value, and builds none.) Each use of a constant that ran a
    /// maker, wherever the use is (in this crate, in a generic fn of
    /// another, in a crate that depends on this one), is a new value that
    /// no maker built there: the constant is refused where it is defined.
    ///
    /// By what the initializer RUNS, not by the constant's type. Reviews 12
    /// to 14 each broke a reading of the type: a projection only a use
    /// settles, a where-clause that shadows the impl which would settle it,
    /// a type of another crate that keeps the value in bytes of its own; and
    /// the type refuses `[const { None }; 4]`, which holds none.
    fn judge_constants(&mut self, constants: &[LocalDefId]) {
        let tcx = self.tcx;
        // The fns of this crate each body CALLS.
        let mut calls: FxHashMap<DefId, Vec<DefId>> = FxHashMap::default();
        for (kind, facts) in self.facts.iter() {
            let (InstanceKind::Item(def), Some(facts)) = (kind, facts) else { continue };
            if !def.is_local() {
                continue;
            }
            let called = calls.entry(*def).or_default();
            for fact in facts.iter() {
                if let Fact::Fn { ty, called: true, .. } = fact {
                    if let ty::FnDef(callee, _) = *ty.kind() {
                        if callee.is_local() {
                            called.push(callee);
                        }
                    }
                }
            }
        }
        for &constant in constants {
            let constant = constant.to_def_id();
            let mut ran: Vec<Option<DefId>> = vec![None; self.seals.len()];
            let mut seen: FxHashSet<DefId> = FxHashSet::default();
            let mut open = vec![constant];
            while let Some(at) = open.pop() {
                if !seen.insert(at) {
                    continue;
                }
                for &callee in calls.get(&at).map_or(&[][..], |called| &called[..]) {
                    for (seal, ran) in ran.iter_mut().enumerate() {
                        // (A method of a trait of this crate stands for any
                        // impl of it: constant evaluation calls none today.)
                        if self.seals[seal].makers.contains(&callee)
                            || tcx.trait_of_assoc(callee).is_some()
                        {
                            ran.get_or_insert(callee);
                        }
                    }
                    open.push(callee);
                }
            }
            let root = tcx.typeck_root_def_id(constant);
            // (For the note only: whether its type may hold one. The verdict
            // is by what it runs. Review 2 of the review-14 build: the note
            // said each use of a `u64` constant is a new sealed value. An
            // inline `const` is declared at a placeholder type: its type is
            // read off its own body.)
            let ty = tcx.mir_for_ctfe(constant).return_ty();
            let ty = seen_from(tcx, constant, ty);
            let may_hold = self.owns_whatever(ty, constant, true);
            // (A `dyn` may hold one: what was handed to one is known only
            // once the walk has run.)
            let open = ty.has_non_region_param()
                || ty.has_aliases()
                || ty.walk().any(
                    |part| matches!(part.kind(), ty::GenericArgKind::Type(part) if part.is_trait()),
                );
            for (seal, ran) in ran.into_iter().enumerate() {
                if let Some(maker) = ran {
                    let holds = open || may_hold & (1 << seal) != 0;
                    let site = Site::Constant { maker, holds, ty };
                    self.fixed(seal, root, tcx.def_span(constant), site);
                }
            }
        }
    }

    /// Read one body: what it does whatever it is instantiated at goes to
    /// `fixed` (a body of this crate only: `local`), what depends on its
    /// instance to `facts`.
    fn read_body(
        &mut self,
        local: Option<LocalDefId>,
        def: DefId,
        body: &mir::Body<'tcx>,
        facts: &mut Vec<Fact<'tcx>>,
    ) {
        self.bodies += 1;
        let tcx = self.tcx;
        let root = tcx.typeck_root_def_id(def);
        let own = if root == def {
            Own::Body
        } else if matches!(tcx.def_kind(def), DefKind::AnonConst) {
            Own::Const
        } else if tcx.opt_parent(def) == Some(root)
            && matches!(
                tcx.coroutine_kind(def),
                Some(rustc_hir::CoroutineKind::Desugared(
                    rustc_hir::CoroutineDesugaring::Async,
                    rustc_hir::CoroutineSource::Fn
                ))
            )
        {
            Own::AsyncBody
        } else {
            Own::Closure
        };
        let fresh: Rc<[mir::Local]> = if local.is_some() && own == Own::Body {
            match self.fresh_params.get(&root) {
                Some(fresh) => fresh.clone(),
                None => {
                    let mut fresh: Vec<mir::Local> = Vec::new();
                    for (param, lent) in fresh_params(tcx, root) {
                        // (What is lent, as the writer sees it: `&Self::View`
                        // with `type View = u8` lends a `u8`.)
                        if lent.into_iter().all(|pointee| self.plain(seen_from(tcx, root, pointee)))
                        {
                            fresh.push(param);
                        }
                    }
                    let fresh: Rc<[mir::Local]> = fresh.into();
                    self.fresh_params.insert(root, fresh.clone());
                    fresh
                }
            }
        } else {
            Rc::from(Vec::new())
        };
        // The locals whose first assignment S4a lets pass: of a type that can
        // own something.
        let mut watched: FxHashMap<mir::Local, usize> = FxHashMap::default();
        for (local, decl) in body.local_decls.iter_enumerated() {
            if !owns_nothing(decl.ty) {
                let index = watched.len();
                watched.insert(local, index);
            }
        }
        let assigned = assigned_since_live(body, &watched);
        // S4e: a body of a crate outside the standard library is also asked
        // what it handles, and whether it does what only `unsafe` code can.
        let third = local.is_none() && self.third_party(def);
        if third {
            let mut held: FxHashSet<Ty<'tcx>> = FxHashSet::default();
            for decl in body.local_decls.iter() {
                let ty = tcx.erase_and_anonymize_regions(decl.ty);
                if !ty.is_primitive() && !ty.is_unit() && !ty.is_never() && held.insert(ty) {
                    facts.push(Fact::Holds { ty });
                }
            }
        }
        let (crate_code, own_code) =
            if third { self.crate_code(def, body) } else { (Vec::new(), false) };
        // (For a body of another crate: what each scope's code was inlined
        // through, outermost first.)
        let chains = local.is_none().then(|| inline_chains(tcx, body));
        let mut reader = Reader {
            checker: self,
            body,
            local: local.is_some(),
            third,
            unsafe_op: None,
            crate_code,
            own_code,
            chains,
            chain_said: None,
            root,
            own,
            // (In its state-machine form: what it keeps across a suspension
            // is a field of its first argument.)
            coroutine: body.coroutine.is_some() || tcx.is_coroutine(def),
            fresh,
            watched,
            assigned,
            now: Locals::none(0),
            facts,
        };
        reader.visit_body(body);
        if third && reader.unsafe_op.is_none() {
            reader.unsafe_op = reader.unsafe_calls_inlined();
        }
        if let Some(what) = reader.unsafe_op {
            facts.push(Fact::Unsafe { what });
        }
        for scope in body.source_scopes.iter() {
            if let Some((callee, span)) = scope.inlined {
                let callee = tcx.erase_and_anonymize_regions(callee);
                let mut outer = Vec::new();
                let mut up = scope.inlined_parent_scope;
                while let Some(parent) = up {
                    let parent = &body.source_scopes[parent];
                    if let Some((through, _)) = parent.inlined {
                        outer.push(tcx.erase_and_anonymize_regions(through));
                    }
                    up = parent.inlined_parent_scope;
                    if outer.len() > 64 {
                        break;
                    }
                }
                outer.reverse();
                facts.push(Fact::Inlined { callee, outer, span });
            }
        }
    }

    /// For each source scope of a body `def` of a crate outside the standard
    /// library: whether what only `unsafe` code can do, done in it, is the
    /// doing of THIS body's code, which the check does not read (S4e). The
    /// code of a scope inside a fn the optimizer inlined here is that fn's
    /// (the innermost one around it): it is asked about as that fn, at its
    /// own instance, as the call it was would be (`Fact::Inlined`), with
    /// what IT handles, and never charged to this body (review 3 of the
    /// review-14 build: a third crate's `unsafe` on its own `u8`, inlined
    /// here, was paired with this body's holders, and a trust of the fn that
    /// did it no longer covered it). The body's own code counts when its
    /// SOURCE has user `unsafe`: an `unsafe` block (a macro's included, a
    /// std macro's too: `pin!`, a `thread_local!` declared in the fn), an
    /// `unsafe fn`, an `unsafe impl` (`trust_def_has_user_unsafe_source`, the
    /// fact the fn's own compiler recorded from its HIR, beside the MIR in
    /// its metadata; a missing row answers "it has"). A fn whose source has
    /// none does nothing only `unsafe` code can: what its MIR does of the
    /// kind is the compiler's own lowering of safe code (`format_args!`'s
    /// call of `fmt::Arguments::new`, an `async` body's transmute of its
    /// resume argument, a move out of a `Box`, the alignment checks a debug
    /// build adds to each), which Rust's guarantee covers. (Review 2 of the
    /// review-14 build: each of these refused a seal over a crate that
    /// forbids `unsafe`.) What those statements store, cast or call is still
    /// read, by its shape, as every body's is.
    fn crate_code(&mut self, def: DefId, body: &mir::Body<'tcx>) -> (Vec<bool>, bool) {
        let tcx = self.tcx;
        let counts = |this: &mut Self, code: DefId| {
            (code.is_local() || this.third_party(code))
                && tcx.trust_def_has_user_unsafe_source(code)
        };
        let own = counts(self, def);
        let mut crate_code = Vec::with_capacity(body.source_scopes.len());
        for data in body.source_scopes.iter() {
            let start = if data.inlined.is_some() {
                Some(data)
            } else {
                data.inlined_parent_scope.map(|parent| &body.source_scopes[parent])
            };
            // (The inlined fn's own: asked about at its own instance.)
            let inlined = start.and_then(|start| start.inlined).is_some();
            crate_code.push(!inlined && own);
        }
        (crate_code, own)
    }

    /// Whether the call at `span` is the expansion of a macro of the
    /// standard library that is no built-in (`pin!` calls `Pin::new_unchecked`
    /// of a local of its own): that macro's own code, whose `unsafe` is
    /// std's, as std's code inlined is (S4e). Asked of calls only. Not a
    /// built-in macro: `asm!` is one, and what it runs is the author's. What
    /// the author handed the macro keeps the author's span.
    ///
    /// Also a call the COMPILER writes in lowering a format string (the
    /// desugaring `format_args!` and its kin mark: `fmt::Arguments::new`,
    /// `fmt::rt::Argument::new_display`; what the author hands the macro
    /// keeps the author's span), and what [`Self::compiler_written`] says.
    /// (Review 3 of the review-14 build: in a fn whose source holds `pin!`,
    /// `eprintln!`'s `Arguments::new` was read as the fn's own call of an
    /// `unsafe fn`.)
    fn std_macro(&mut self, span: Span) -> bool {
        if self.compiler_written(span) {
            return true;
        }
        let data = span.ctxt().outer_expn_data();
        if matches!(
            data.kind,
            rustc_span::hygiene::ExpnKind::Desugaring(
                rustc_span::DesugaringKind::FormatLiteral { .. }
            )
        ) {
            return true;
        }
        if !matches!(data.kind, rustc_span::hygiene::ExpnKind::Macro(..)) {
            return false;
        }
        let Some(mac) = data.macro_def_id else { return false };
        if mac.is_local() || self.third_party(mac) {
            return false;
        }
        !rustc_attr_ir::find_attr!(self.tcx, mac, RustcBuiltinMacro { .. })
    }

    /// Whether what stands at `span` is code the compiler wrote in lowering
    /// `.await` (`IntoFuture::into_future`, `Pin::new_unchecked` of the
    /// awaited value it keeps, `get_context`, `poll`, the `yield`) or an
    /// `async` body (the state machine around it): no token of it is the
    /// author's (the awaited expression, and every statement of the body,
    /// keeps its own span). Asked of every operation, not only calls.
    fn compiler_written(&self, span: Span) -> bool {
        matches!(
            span.ctxt().outer_expn_data().kind,
            rustc_span::hygiene::ExpnKind::Desugaring(
                rustc_span::DesugaringKind::Await | rustc_span::DesugaringKind::Async
            )
        )
    }

    /// The facts of the body `kind` names: of this crate's as read at the
    /// start; of another crate's from the MIR its metadata carries; of a
    /// shim's from the MIR the compiler writes for it.
    fn facts_at(&mut self, kind: InstanceKind<'tcx>) -> Option<Rc<[Fact<'tcx>]>> {
        if let Some(known) = self.facts.get(&kind) {
            return known.clone();
        }
        let tcx = self.tcx;
        let mut promoted = None;
        let body: Option<&'tcx mir::Body<'tcx>> = match kind {
            // (A body of this crate that was not read at the start is none
            // the walk follows: a constructor, a foreign item.)
            InstanceKind::Item(def) if def.is_local() => None,
            InstanceKind::Item(def) => {
                promoted = Some(def);
                match tcx.def_kind(def) {
                    DefKind::Fn
                    | DefKind::AssocFn
                    | DefKind::Closure
                    | DefKind::SyntheticCoroutineBody
                        if tcx.is_mir_available(def) =>
                    {
                        Some(tcx.instance_mir(kind))
                    }
                    DefKind::Const
                    | DefKind::AssocConst
                    | DefKind::AnonConst
                        // (Every constant's CTFE MIR is in its crate's
                        // metadata, but a trivial one's: it names nothing.)
                        if tcx.trivial_const(def).is_none() =>
                    {
                        Some(tcx.mir_for_ctfe(def))
                    }
                    _ => {
                        promoted = None;
                        None
                    }
                }
            }
            InstanceKind::Intrinsic(..)
            | InstanceKind::LlvmIntrinsic(..)
            | InstanceKind::Virtual(..) => None,
            InstanceKind::Shim(shim) if Self::shim_is_read(shim) => Some(tcx.instance_mir(kind)),
            InstanceKind::Shim(_) => None,
        };
        let facts = body.map(|body| {
            let mut facts = Vec::new();
            self.read_body(None, kind.def_id(), body, &mut facts);
            if let Some(def) = promoted {
                for promoted in tcx.promoted_mir(def).iter() {
                    self.read_body(None, def, promoted, &mut facts);
                }
            }
            Rc::from(facts)
        });
        self.facts.insert(kind, facts.clone());
        facts
    }

    /// Whether the MIR of the shim is asked of the compiler. Not of the drop
    /// of a coroutine of THIS crate (the compiler builds it from the
    /// coroutine's optimized MIR, which would steal the MIR the crate's
    /// other checks still read: [`Self::drops_coroutine`] answers for it),
    /// of empty drop glue, nor of the shims of `async` drop (a nightly
    /// feature: refused where met).
    fn shim_is_read(shim: ShimKind<'tcx>) -> bool {
        match shim {
            ShimKind::DropGlue(_, None) => false,
            ShimKind::DropGlue(_, Some(ty)) => {
                !matches!(*ty.kind(), ty::Coroutine(def, _) if def.is_local())
            }
            ShimKind::FutureDropPoll(..)
            | ShimKind::AsyncDropGlueCtor(..)
            | ShimKind::AsyncDropGlue(..) => false,
            _ => true,
        }
    }

    fn fixed(&mut self, seal: usize, root: DefId, span: Span, site: Site<'tcx>) {
        self.fixed.push(Found { seal, root, span, site });
    }

    fn found_each(&mut self, mask: u64, root: DefId, span: Span, site: Site<'tcx>) {
        for seal in 0..self.seals.len() {
            if mask & (1 << seal) != 0 {
                self.found.push(Found { seal, root, span, site: site.clone() });
            }
        }
    }

    // ----- the instances ---------------------------------------------------

    /// Whether `args` name a type of this crate at any depth: only then can a
    /// generic body of another crate reach code or a type of this one. In an
    /// open reading (`open`: its item), a type parameter is no type of this
    /// crate (it stands for whatever a crate that depends on this one makes
    /// it), and a projection is read by what it names (and is this crate's
    /// where its trait is), unless the item's bounds tie a parameter to a
    /// sealed value ([`Self::env_mask`]: `M: Make<Out = App>` makes what
    /// `dep::direct::<M>` does at `M::Out` a thing done to an `App`, whatever
    /// `M` stands for). (Review 5 of the review-14 build: such a call, at the
    /// bare parameter, was never followed.)
    fn names_local_in(&mut self, args: GenericArgs<'tcx>, open: Option<DefId>) -> bool {
        let mut parameter = false;
        let local = args.iter().any(|arg| {
            arg.walk().any(|part| match part.kind() {
                ty::GenericArgKind::Type(ty) => match *ty.kind() {
                    ty::Adt(adt, _) => adt.did().is_local(),
                    ty::Closure(def, _)
                    | ty::CoroutineClosure(def, _)
                    | ty::Coroutine(def, _)
                    | ty::FnDef(def, _)
                    | ty::Foreign(def) => def.is_local(),
                    ty::Dynamic(predicates, ..) => {
                        predicates.principal_def_id().is_some_and(|def| def.is_local())
                    }
                    ty::Alias(_, alias) => {
                        parameter = true;
                        open.is_none() || alias_def(alias.kind).is_local()
                    }
                    ty::Param(_) => {
                        parameter = true;
                        open.is_none()
                    }
                    _ => false,
                },
                _ => false,
            })
        });
        local || (parameter && open.is_some_and(|scope| self.env_mask(scope) != 0))
    }

    /// The path a `trusts` entry is matched against: the item's, with its
    /// crate's name in front (`seal_dep::fill`, `alloc::boxed::Box::new`;
    /// [`entry_path`]).
    fn trust_path(&self, def: DefId) -> Vec<String> {
        let mut path = entry_path(self.tcx, def);
        path[0] = self.tcx.crate_name(def.krate).to_string();
        path
    }

    /// An entry that names `def` in `trusts`: the end of its path (where it
    /// is DEFINED, which is not always where it is used from:
    /// `function::FnMut`, not `ops::FnMut`), two parts or more, and as many
    /// as it takes to name no other item an entry's word would be relied on
    /// for (review 1 of the review-14 build: `Vec::push` named a
    /// dependency's `stack::Vec::push` too). Where every end of its path
    /// names another such item too (two crates of one name, two versions of
    /// one crate, or a crate's whole path ending another's), the path
    /// anchored at its crate (`::two::keep`, `::b::keep`), when the crate has
    /// a name that anchors ([`Self::ensure_anchors`]); else `None`: no entry
    /// names it alone. (Review 2 of the review-14 build: the error suggested
    /// `samedep::keep` "and" `samedep::keep`.)
    fn trust_entry(&self, def: DefId) -> Option<String> {
        let path = self.trust_path(def);
        let ends = |whole: &[String], end: &[String]| {
            end.len() <= whole.len() && whole[whole.len() - end.len()..] == *end
        };
        for start in (0..path.len().saturating_sub(1)).rev() {
            let end = &path[start..];
            let other = self
                .asked_paths
                .iter()
                .any(|(krate, asked)| (*krate != def.krate || *asked != path) && ends(asked, end));
            if !other {
                return Some(end.join("::"));
            }
        }
        let anchor = self.anchors.as_ref()?.get(&def.krate)?.first()?;
        let item = entry_path(self.tcx, def);
        (item.len() > 1).then(|| format!("::{anchor}::{}", item[1..].join("::")))
    }

    /// [`Self::trust_entry`] as a note says it: in backquotes, or that no
    /// entry names it alone.
    fn entry_shown(&self, def: DefId) -> String {
        match self.trust_entry(def) {
            Some(entry) => format!("`{entry}`"),
            None => format!(
                "none names `{}` alone: another crate of the build has the same name and the \
                 same path, and this crate names neither; trust a fn on the way to it",
                self.trust_path(def).join("::")
            ),
        }
    }

    /// The item a `trusts` entry names for the body `def`: a fn (and a
    /// constructor), a trait, a static; for the body of an `async fn` (or a
    /// `gen fn`), the fn itself, whose own code it is. None for a closure or
    /// an `async` block (code a fn hands on, which runs where it is called),
    /// for a constant (it runs nothing: what it hands out, a fn pointer or a
    /// closure, runs where that is called, and is judged there), and for a
    /// shim. (Review 2 of the review-14 build: a trust of the constant
    /// `Tab::SWAP = mem::swap::<T>` covered the swap this crate made through
    /// it; a closure was trusted by the name of the fn it is in.)
    fn trust_item(&self, def: DefId) -> Option<DefId> {
        let tcx = self.tcx;
        match tcx.def_kind(def) {
            DefKind::Fn
            | DefKind::AssocFn
            | DefKind::Ctor(..)
            | DefKind::Trait
            | DefKind::TraitAlias
            | DefKind::Static { .. } => Some(def),
            DefKind::Closure => {
                let own_body = matches!(
                    tcx.coroutine_kind(def),
                    Some(rustc_hir::CoroutineKind::Desugared(_, rustc_hir::CoroutineSource::Fn))
                );
                let parent = tcx.parent(def);
                (own_body && matches!(tcx.def_kind(parent), DefKind::Fn | DefKind::AssocFn))
                    .then_some(parent)
            }
            _ => None,
        }
    }

    /// Whether the `trusts` entry `entry` names the item `def`: matched from
    /// the right against its path where it is defined, with its crate's name
    /// in front; or, an entry that starts with `::`, its crate's anchor
    /// ([`Self::ensure_anchors`]) and then its WHOLE path in that crate, as
    /// Rust's own `::krate::path` names one.
    fn entry_names(&mut self, entry: &str, def: DefId) -> bool {
        let entry = entry.trim();
        let Some(anchored) = entry.strip_prefix("::") else {
            return names_path(&self.trust_path(def), entry);
        };
        let parts: Vec<&str> = anchored.split("::").map(str::trim).collect();
        let Some((anchor, rest)) = parts.split_first() else { return false };
        self.ensure_anchors();
        let anchors = self.anchors.as_ref().and_then(|anchors| anchors.get(&def.krate));
        if !anchors.is_some_and(|names| names.iter().any(|name| name == anchor)) {
            return false;
        }
        let path = entry_path(self.tcx, def);
        path.len() == rest.len() + 1
            && path[1..].iter().map(String::as_str).eq(rest.iter().copied())
    }

    /// Fill [`Self::anchors`]: the names a `trusts` entry may anchor at a
    /// crate (`::two::keep`). What this crate's extern prelude calls the
    /// crate (`--extern two=libsamedep-2.rlib`, `--extern b`, an `extern
    /// crate x as y;` at its root), as Rust's own `::two` would resolve; and
    /// the crate's own name, where no other crate of the build has it (`core`,
    /// `alloc`). A name two crates would answer to anchors neither.
    fn ensure_anchors(&mut self) {
        if self.anchors.is_some() {
            return;
        }
        let tcx = self.tcx;
        let mut named: FxHashMap<String, FxHashSet<CrateNum>> = FxHashMap::default();
        let mut by_name: FxHashMap<Symbol, Vec<CrateNum>> = FxHashMap::default();
        for &krate in tcx.crates(()).iter() {
            by_name.entry(tcx.crate_name(krate)).or_default().push(krate);
        }
        for (name, crates) in by_name.iter() {
            if let [one] = crates[..] {
                named.entry(name.to_string()).or_default().insert(one);
            }
        }
        // (Each file a crate was loaded from, as the extern options name
        // them: canonical.)
        let mut files: FxHashMap<std::path::PathBuf, CrateNum> = FxHashMap::default();
        for &krate in tcx.crates(()).iter() {
            for path in tcx.used_crate_source(krate).paths() {
                let path = std::fs::canonicalize(path).unwrap_or_else(|_| path.clone());
                files.insert(path, krate);
            }
        }
        for (name, entry) in tcx.sess.opts.externs.iter() {
            if !entry.add_prelude {
                continue;
            }
            let mut found: FxHashSet<CrateNum> = FxHashSet::default();
            match entry.files() {
                Some(given) => {
                    for file in given {
                        if let Some(&krate) = files.get(file.canonicalized()) {
                            found.insert(krate);
                        }
                    }
                }
                None => {
                    for &krate in tcx.crates(()).iter() {
                        if tcx.crate_name(krate).as_str() == name.as_str()
                            && tcx.extern_crate(krate).is_some_and(|loaded| loaded.is_direct())
                        {
                            found.insert(krate);
                        }
                    }
                }
            }
            if found.len() == 1 {
                named.entry(name.clone()).or_default().extend(found);
            }
        }
        for def in tcx.hir_crate_items(()).definitions() {
            if matches!(tcx.def_kind(def), DefKind::ExternCrate)
                && tcx.parent(def.to_def_id()).is_crate_root()
            {
                if let Some(krate) = tcx.extern_mod_stmt_cnum(def) {
                    named
                        .entry(tcx.item_name(def.to_def_id()).to_string())
                        .or_default()
                        .insert(krate);
                }
            }
        }
        let mut anchors: FxHashMap<CrateNum, Vec<String>> = FxHashMap::default();
        for (name, crates) in named {
            if let (1, Some(&krate)) = (crates.len(), crates.iter().next()) {
                anchors.entry(krate).or_default().push(name);
            }
        }
        for names in anchors.values_mut() {
            names.sort_unstable();
        }
        self.anchors = Some(anchors);
    }

    /// How a note tells `def`'s crate from another of the same name: the
    /// standard library's own, or the name this crate gives it.
    fn crate_shown(&self, def: DefId) -> String {
        let tcx = self.tcx;
        if in_sysroot(tcx, def.krate) {
            return format!(" (of the standard library's own `{}`)", tcx.crate_name(def.krate));
        }
        match self.anchors.as_ref().and_then(|anchors| anchors.get(&def.krate)) {
            Some(names) if !names.is_empty() => {
                format!(" (of the crate this one names `{}`)", names[0])
            }
            _ => String::new(),
        }
    }

    /// The `trusts` entries, as (seal, entry), that name `def` (a fn, or a
    /// trait, of another crate: [`Self::trust_item`]). Each entry keeps what
    /// it named ([`Self::entry_items`]): one that names two items is refused
    /// at the seal ([`Self::judge_trusts`]). An entry whose path a constant
    /// has is noted ([`Self::misnamed`]): it names nothing.
    fn trusts_of(&mut self, def: DefId) -> Rc<[(usize, usize)]> {
        if let Some(known) = self.trusting.get(&def) {
            return known.clone();
        }
        let item = self.trust_item(def);
        let entries: Rc<[(usize, usize)]> = match item {
            Some(item) if item != def => self.trusts_of(item),
            Some(_) => {
                let mut entries = Vec::new();
                for seal in 0..self.seals.len() {
                    for index in 0..self.seals[seal].decl.trusts.len() {
                        let trusted = self.seals[seal].decl.trusts[index].clone();
                        if self.entry_names(&trusted, def) {
                            entries.push((seal, index));
                        }
                    }
                }
                entries.into()
            }
            None => {
                if matches!(
                    self.tcx.def_kind(def),
                    DefKind::Const { .. } | DefKind::AssocConst { .. }
                ) {
                    for seal in 0..self.seals.len() {
                        for index in 0..self.seals[seal].decl.trusts.len() {
                            let trusted = self.seals[seal].decl.trusts[index].clone();
                            if self.entry_names(&trusted, def) {
                                self.misnamed.entry((seal, index)).or_insert(def);
                            }
                        }
                    }
                }
                Rc::from(Vec::new())
            }
        };
        self.trusting.insert(def, entries.clone());
        entries
    }

    /// Fill [`Self::asked_paths`]: every item a `trusts` entry's word would
    /// be relied on at so far, by where it is defined.
    fn note_asked(&mut self) {
        self.ensure_anchors();
        let mut asked: Vec<(CrateNum, Vec<String>)> =
            self.relied_on.iter().map(|def| (def.krate, self.trust_path(*def))).collect();
        asked.sort_unstable_by(|a, b| (a.0.as_u32(), &a.1).cmp(&(b.0.as_u32(), &b.1)));
        asked.dedup();
        self.asked_paths = asked;
    }

    /// What the crate's shape relies on a `trusts` entry for, noted before
    /// any note suggests one ([`Self::judge_shape`] says it): each static the
    /// crate declares `safe` in an `extern` block, and each trait of another
    /// crate it has an `unsafe impl` of.
    fn shape_relied(&mut self) {
        let tcx = self.tcx;
        let statics: Vec<DefId> = tcx
            .hir_crate_items(())
            .foreign_items()
            .map(|item| item.owner_id.def_id.to_def_id())
            .filter(|def| {
                matches!(
                    tcx.def_kind(*def),
                    DefKind::Static { safety: rustc_hir::Safety::Safe, .. }
                )
            })
            .collect();
        for def in statics {
            self.relied_on.insert(def);
        }
        let traits: Vec<DefId> = tcx
            .all_local_trait_impls(())
            .iter()
            .filter(|(of, impls)| {
                !of.is_local()
                    && !tcx.trait_is_auto(**of)
                    && impls.iter().any(|implementation| {
                        tcx.impl_trait_header(implementation.to_def_id()).safety.is_unsafe()
                    })
            })
            .map(|(of, _)| *of)
            .collect();
        for of in traits {
            self.relied_on.insert(of);
        }
    }

    /// A `trusts` entry names ONE item, as every other name in a seal does:
    /// one that names two (of two crates, or at two paths of one crate)
    /// would trust each, and the author's word was about one. Asked of the
    /// items its word was relied on for (an item the check never relied on
    /// it for is covered by nothing it says).
    /// Also fills [`Self::asked_paths`] for the entries notes suggest.
    fn judge_trusts(&mut self) {
        self.note_asked();
        // (Items at one path in one crate are one name, but those of impls
        // whose own type is no struct, enum or union, each its own, and apart
        // from the trait's own item at that path: [`Self::entry_items`].)
        let mut entries: Vec<((usize, usize), Vec<DefId>)> = self
            .entry_items
            .iter()
            .filter(|(_, named)| named.len() > 1)
            .map(|(entry, named)| (*entry, named.values().copied().collect()))
            .collect();
        entries.sort_unstable_by_key(|(entry, _)| *entry);
        for ((seal, index), named) in entries {
            // (Two items at one printed path: said whose each is.)
            let printed: Vec<String> =
                named.iter().map(|def| self.trust_path(*def).join("::")).collect();
            let shown: Vec<String> = named
                .iter()
                .zip(printed.iter())
                .take(LISTED)
                .map(|(def, path)| {
                    let twice = printed.iter().filter(|other| *other == path).count() > 1;
                    let whose = if twice { self.crate_shown(*def) } else { String::new() };
                    format!("`{path}`{whose}")
                })
                .collect();
            let apart: Vec<String> =
                named.iter().take(LISTED).map(|def| self.entry_shown(*def)).collect();
            let site = Site::Shape(format!(
                "its `trusts` entry `{}` names {} items: {}. An entry names one item (the end of \
                 its path where it is defined, or `::` and the crate's name in this crate and its \
                 whole path there), and this one would trust each of them on a word given for \
                 one: write as much of the path as tells them apart ({})",
                self.seals[seal].decl.trusts[index],
                named.len(),
                and_list(&shown),
                and_list(&apart),
            ));
            let (did, span) = (self.seals[seal].adt.did(), self.seals[seal].decl.span);
            self.fixed(seal, did, span, site);
        }
    }

    /// The seals whose `trusts` name `def`.
    fn trusting(&mut self, def: DefId) -> u64 {
        self.trusts_of(def).iter().fold(0, |mask, (seal, _)| mask | (1 << seal))
    }

    /// Note that each `trusts` entry that names `def` is in use.
    fn trust_used(&mut self, def: DefId) {
        self.relied_on.insert(def);
        for entry in self.trusts_of(def).iter() {
            self.relied(*entry, def);
        }
    }

    /// The `trusts` entry `entry` covers `def` here: in use, and naming it
    /// ([`Self::entry_items`]).
    fn relied(&mut self, entry: (usize, usize), def: DefId) {
        self.used_trusts.insert(entry);
        let path = self.trust_path(def).join("::");
        let tcx = self.tcx;
        let apart = tcx
            .opt_parent(def)
            .filter(|parent| matches!(tcx.def_kind(*parent), DefKind::Impl { .. }))
            .filter(|parent| {
                !matches!(
                    tcx.type_of(*parent).instantiate_identity().skip_norm_wip().kind(),
                    ty::Adt(..)
                )
            })
            .map(|parent| parent.index.as_u32());
        self.entry_items
            .entry(entry)
            .or_default()
            .entry((path, def.krate.as_u32(), apart))
            .or_insert(def);
    }

    /// Note, for each `trusts` entry that names `def`, the type holding a
    /// sealed value (of the seals `owned`) that it was run at.
    fn trusted_at(&mut self, def: DefId, owner: Ty<'tcx>, owned: u64) {
        self.relied_on.insert(def);
        for &(seal, index) in self.trusts_of(def).iter() {
            if owned & (1 << seal) == 0 {
                continue;
            }
            self.relied((seal, index), def);
            let at = self.trusted_at.entry((seal, index)).or_default();
            if at.len() < LISTED {
                at.insert(format!("`{owner}`"));
            }
        }
    }

    /// Whether `def` is of a crate outside the standard library (and not
    /// this one): code whose `unsafe` the check does not read (S4e).
    fn third_party(&mut self, def: DefId) -> bool {
        if def.is_local() {
            return false;
        }
        let tcx = self.tcx;
        !*self.resident.entry(def.krate).or_insert_with(|| in_sysroot(tcx, def.krate))
    }

    /// S4. Every body of this crate is read where it stands, and from there
    /// what each instance names, as the compiler resolves it: a fn, a drop,
    /// the vtable of a coercion, a closure, a `const` item's initializer.
    /// What a body that is not this crate's uses is the compiler's own
    /// answer ([`Self::read_instance`]).
    fn walk(&mut self) {
        let tcx = self.tcx;
        let mut roots: Vec<DefId> = self
            .facts
            .iter()
            .filter_map(|(kind, facts)| match kind {
                InstanceKind::Item(def) if def.is_local() && facts.is_some() => Some(*def),
                _ => None,
            })
            .collect();
        roots.sort_unstable_by_key(|def| def.index.as_u32());
        for root in roots.iter().rev() {
            let standing = self.standing(*root);
            // A body whose where-clauses, those that name no type parameter,
            // hold at no lifetime can never be called (a call must prove
            // them, and nothing can): it never runs, and the compiler makes
            // nothing it names. Asked as `reach` asks it. (Review 1 of the
            // review-14 build: `fn odd<'a>(..) where &'a mut u8: Tr`, read
            // where it stands, led the compiler to a panic, and refused
            // every seal at an alias nothing could settle.)
            if self.impossible(standing) {
                continue;
            }
            // (Read where it stands, a generic body is an open reading of its
            // own parameters.)
            let open = (!self.settled.contains(root) && standing.args.has_non_region_param())
                .then(|| tcx.typeck_root_def_id(*root));
            self.enqueue(Work { instance: standing, through: None, open });
        }
        // What the compiler itself calls: the start-up code, at the type
        // `main` hands back (its `Termination::report` runs after `main`).
        if let (Some((main, _)), Some(start)) = (tcx.entry_fn(()), tcx.lang_items().start_fn()) {
            let sig = tcx.fn_sig(main).instantiate_identity().skip_norm_wip();
            if let (Some(output), true) = (sig.output().no_bound_vars(), main.is_local()) {
                let output = at_instance(tcx, None, output);
                let args = tcx.mk_args(&[output.into()]);
                let resolved = ty::Instance::try_resolve(
                    tcx,
                    ty::TypingEnv::fully_monomorphized(),
                    start,
                    args,
                );
                if let Ok(Some(instance)) = resolved {
                    let from = Work { instance: self.standing(main), through: None, open: None };
                    self.reach(from, instance, tcx.def_span(main), Handed::Named);
                }
            }
        }
        let limit = tcx.recursion_limit().0;
        while let Some(step) = self.queue.pop() {
            let work = match step {
                Step::Enter(work) => work,
                Step::Leave(def) => {
                    if let Some(depth) = self.depth.get_mut(&def) {
                        *depth = depth.saturating_sub(1);
                    }
                    continue;
                }
            };
            let stop = if self.instances > INSTANCE_BOUND {
                Some(format!(
                    "the crate makes more than {INSTANCE_BOUND} instances of its generic code: \
                     the check stopped reading them"
                ))
            } else {
                // As the compiler counts it where it makes the instances: a
                // fn instantiated inside its own instances deeper than the
                // recursion limit is taken to grow without end. (Drop glue
                // makes tight loops of its own: four times the margin.)
                let def = work.instance.def_id();
                let depth = self.depth.get(&def).copied().unwrap_or(0);
                let glue = matches!(work.instance.def, InstanceKind::Shim(ShimKind::DropGlue(..)));
                let depth = if glue { depth / 4 } else { depth };
                (depth > limit).then(|| {
                    // (Review 1 of the review-14 build: the text said the
                    // compiler stops there, of code the compiler never
                    // instantiates.)
                    format!(
                        "the crate instantiates `{}` inside its own instances deeper than the \
                         recursion limit ({limit}): the check stopped reading there. (Where code \
                         that runs does this, the compiler stops at the same limit, with an \
                         error; code that nothing calls the compiler never instantiates, and \
                         this check reads every body, also one nothing calls.)",
                        tcx.def_path_str(def)
                    )
                })
            };
            if let Some(why) = stop {
                self.cut = true;
                let all = self.all();
                let root = work.through.map_or(work.instance.def_id(), |way| way.root);
                let span = work.through.map_or(self.seals[0].decl.span, |way| way.at);
                self.found_each(all, root, span, Site::Shape(why));
                if self.instances > INSTANCE_BOUND {
                    self.queue.clear();
                    break;
                }
                continue;
            }
            let def = work.instance.def_id();
            *self.depth.entry(def).or_insert(0) += 1;
            self.queue.push(Step::Leave(def));
            self.read_instance(work);
        }
    }

    /// Whether `instance` is one the compiler never makes because bounds it
    /// needs hold for no lifetime: of a fn or a constant, its where-clauses
    /// that name no type parameter (with one, the bound is asked where the
    /// parameter is known); of the drop glue of a struct or enum, the
    /// type's own where-clauses at its arguments (`W<&mut u8>` of a `struct
    /// W<T: Tr>` names a type that exists only where `&mut u8: Tr` is
    /// assumed). The compiler's own answer
    /// (`instantiate_and_check_impossible_predicates`). Nothing that can run
    /// is skipped: a call must prove the callee's bounds, and a value of a
    /// type can exist only where the type's are proved.
    fn impossible(&self, instance: ty::Instance<'tcx>) -> bool {
        let tcx = self.tcx;
        match instance.def {
            InstanceKind::Item(def) => {
                tcx.instantiate_and_check_impossible_clauses((def, instance.args))
            }
            InstanceKind::Shim(ShimKind::DropGlue(_, Some(ty))) => match *ty.kind() {
                ty::Adt(adt, args) => {
                    tcx.instantiate_and_check_impossible_clauses((adt.did(), args))
                }
                _ => false,
            },
            _ => false,
        }
    }

    /// The body `def` of this crate where it stands: its own parameters for
    /// arguments.
    fn standing(&self, def: DefId) -> ty::Instance<'tcx> {
        let tcx = self.tcx;
        let args = tcx.erase_and_anonymize_regions(GenericArgs::identity_for_item(tcx, def));
        ty::Instance { def: InstanceKind::Item(def), args }
    }

    /// What a reading is one with ([`WorkKey`]). An open reading is keyed by
    /// the TYPING ENVIRONMENT of its item, not by the item: everything it
    /// asks of its item (`TypingEnv::post_analysis` in `typing_env`, `sub`,
    /// `seen_from`, and the walks of a type read whatever the parameters
    /// stand for) is asked of that environment alone, which is a function
    /// of the item's normalized `param_env`; and, both read with their
    /// parameters named by index ([`ByIndex`]: the compiler tells a
    /// parameter by its index, and a name is only how it is printed), one
    /// instance in two items of one environment is the same question, and
    /// its reading finds the same sites at the same places (a site in a
    /// body of this crate is laid to that body's own item; one in another
    /// crate's, to the way, which keys of one reading already meet:
    /// `enqueue`). Only a note's name for the item can differ. (Review 4 of
    /// the review-14 build: keyed by the item, `f2::<T>` read in `f1`'s
    /// scope was read again in `f2`'s own, and every fn of a chain of N
    /// generic fns once per fn above it: N^2/2 readings, and a true program
    /// of 600 refused at the instance bound.)
    fn key(&mut self, work: &Work<'tcx>) -> WorkKey<'tcx> {
        let tcx = self.tcx;
        let Some(scope) = work.open else {
            return (work.instance, None, work.through.is_some());
        };
        let env = match self.scope_envs.get(&scope) {
            Some(env) => *env,
            None => {
                let env = ty::TypingEnv::post_analysis(tcx, scope).param_env;
                let env = ty::TypeFoldable::fold_with(env, &mut ByIndex(tcx));
                self.scope_envs.insert(scope, env);
                env
            }
        };
        let instance = ty::TypeFoldable::fold_with(work.instance, &mut ByIndex(tcx));
        (instance, Some(env), work.through.is_some())
    }

    fn enqueue(&mut self, mut work: Work<'tcx>) {
        // A body of this crate none of whose facts mentions a parameter says
        // the same at every instance: where it stands.
        if let InstanceKind::Item(def) = work.instance.def {
            if self.settled.contains(&def) {
                work.instance = self.standing(def);
                work.open = None;
            }
        }
        // One body reached on ways that trust different seals is read again
        // only for a seal that this way leaves uncovered and every earlier
        // reading covered, and then with what NO way covers: the seals
        // covered on this way and on every earlier one. What that reading
        // finds, some way read alone would find (a seal uncovered there is
        // uncovered on one of the ways; what the way adds beneath, it adds
        // whatever it started with), and it finds all that the way alone
        // would. Each such reading uncovers a seal more, so a body is read at
        // most 129 times on one key, where keying on the covered seals
        // themselves read it once per set of trusted fns on the paths to it
        // (review 1 of the review-14 build: 2^K readings of 2K instances, a
        // true program refused at the instance bound).
        // (Kept for each crate, `Through::own`, and met crate by crate: a crate
        // the new way does not have is dropped from the reading. Per seal,
        // what covers a site beneath is ONE part of the start (`trusted`, or
        // one crate's entry, the last a strip read) or a constant, so the met
        // reading finds what one of the ways alone finds, and a seal refused
        // on either way is refused. Each further reading of a key clears a
        // bit, so a key is read at most 65 times for each crate of its first
        // table, and once more. Review 3 of the review-14 build: keyed by the
        // SET of crates as well, a body beneath K crates' trusted fns on
        // alternative paths was read once per subset, 2^K times, and a true
        // program of 20 tiny crates was refused at the instance bound.)
        let key = self.key(&work);
        let covered = work.through.map_or((0, OwnId::NONE), |way| (way.trusted, way.own));
        match self.seen.get(&key).copied() {
            None => {
                self.seen.insert(key, covered);
            }
            Some(read) => {
                if read.0 & !covered.0 == 0 && self.own_within(read.1, covered.1) {
                    // (Every seal this way leaves uncovered was uncovered on
                    // a way already read.)
                    return;
                }
                let met = (read.0 & covered.0, self.own_meet(read.1, covered.1));
                self.seen.insert(key, met);
                if let Some(way) = work.through.as_mut() {
                    way.trusted = met.0;
                    way.own = met.1;
                }
            }
        }
        self.instances += 1;
        self.queue.push(Step::Enter(work));
    }

    /// `value` as the body of `instance` names it.
    fn at<T>(&self, instance: ty::Instance<'tcx>, value: T) -> T
    where
        T: rustc_middle::ty::TypeFoldable<TyCtxt<'tcx>> + Copy,
    {
        // (A shim written for one type names that type as it is.)
        let args = instance.def.has_polymorphic_mir_body().then_some(instance.args);
        at_instance(self.tcx, args, value)
    }

    /// `value` as the body of `instance` names it ([`Self::at`]); in an open
    /// reading (`open`: the item whose parameters the instance's arguments
    /// name), normalized in that item's typing environment where it still
    /// names a parameter (`<&mut (T, App) as Deref>::Target` is `(T, App)`).
    fn sub<T>(&self, instance: ty::Instance<'tcx>, value: T, open: Option<DefId>) -> T
    where
        T: rustc_middle::ty::TypeFoldable<TyCtxt<'tcx>> + Copy,
    {
        let tcx = self.tcx;
        let Some(scope) = open else { return self.at(instance, value) };
        let value = match instance.def.has_polymorphic_mir_body().then_some(instance.args) {
            Some(args) if !args.is_empty() => {
                ty::EarlyBinder::bind(tcx, value).instantiate(tcx, args).skip_norm_wip()
            }
            _ => value,
        };
        let value = tcx.erase_and_anonymize_regions(value);
        if !value.has_non_region_param() {
            return at_instance(tcx, None, value);
        }
        tcx.try_normalize_erasing_regions(
            ty::TypingEnv::post_analysis(tcx, scope),
            ty::Unnormalized::new_wip(value),
        )
        .unwrap_or(value)
    }

    /// Where an instance is resolved: in an open reading, in the typing
    /// environment of the item whose parameters it names (its where-clauses
    /// settle what they settle, a blanket impl applies whatever the
    /// parameters are, and a method whose impl a parameter picks is left
    /// unresolved); else fully concrete.
    fn typing_env(&self, open: Option<DefId>) -> ty::TypingEnv<'tcx> {
        match open {
            Some(scope) => ty::TypingEnv::post_analysis(self.tcx, scope),
            None => ty::TypingEnv::fully_monomorphized(),
        }
    }

    /// The compiler's own answer to which body `def` at `args` runs, asked
    /// so that nothing it is handed can make a query fail (in an open
    /// reading, `mode`: the arguments name the item's parameters, and the
    /// question is asked in the item's typing environment).
    ///
    /// Two queries may not be handed what an open reading meets, and are
    /// not: `Instance::try_resolve` normalizes the arguments with the
    /// infallible normalizer, which panics on a projection the environment
    /// cannot settle (review 4 of the review-14 build: a provided method
    /// with a where-clause the `dyn` does not prove, `fn m(&self) where X:
    /// Tr2`, read open in a body where `T: Tr2` does not hold, names
    /// `Default::default::<Vec<<T as Tr2>::Out>>`); and the trait solver
    /// stops the build, with no span and no word of the seal, at an
    /// obligation nested deeper than the recursion limit (review 4: dead
    /// polymorphic recursion that grows two levels a step, `grow(Some(Some(
    /// x.clone())))`, asked `Clone` of `Option` 130 deep before the walk cut
    /// at its 128th re-entry). So the arguments are first measured
    /// ([`Self::oversized`], which refuses every seal past the bound) and
    /// normalized with the fallible normalizer. Arguments an open reading's
    /// environment cannot normalize name a projection only a bound it lacks
    /// settles: which body runs is then not known here, and the item is
    /// read as an ABSTRACT impl ([`Resolved::Open`], [`Self::unresolved`]),
    /// never skipped. Arguments a concrete reading cannot normalize are
    /// unread, and refuse every seal.
    fn resolve(
        &mut self,
        work: Work<'tcx>,
        def: DefId,
        args: GenericArgs<'tcx>,
        mode: Option<DefId>,
    ) -> Resolved<'tcx> {
        let tcx = self.tcx;
        if self.oversized(work, args, || format!("`{}`", tcx.def_path_str(def))) {
            return Resolved::None;
        }
        let typing_env = self.typing_env(mode);
        let args =
            match tcx.try_normalize_erasing_regions(typing_env, ty::Unnormalized::new_wip(args)) {
                Ok(args) => args,
                Err(_) if mode.is_some() => return Resolved::Open,
                Err(_) => {
                    self.unread(
                        work,
                        format!(
                            "`{}` at types the compiler could not normalize",
                            tcx.def_path_str(def)
                        ),
                    );
                    return Resolved::None;
                }
            };
        // (The trait solver stops the build at an obligation nested deeper
        // than the recursion limit, and a type's depth does not bound an
        // obligation's: `impl<T> Tr for W<T> where V<T>: Tr` costs two levels
        // of one per level of `W`. So the trait of a trait's item is first
        // asked of the solver's own query mode, which says it overflowed
        // where the mode `try_resolve` uses stops the build. Review 5 of the
        // review-14 build: dead `grow(W(x))` stopped the build with E0275, no
        // span and no word of the seal, at half the depth bound.)
        if self.solver_overflows(typing_env, def, args) {
            self.overflowed(work, || format!("`{}`", tcx.def_path_str(def)));
            return Resolved::None;
        }
        match ty::Instance::try_resolve(tcx, typing_env, def, args) {
            Ok(Some(instance)) => Resolved::Item(instance),
            // (In an open reading: an impl the instance picks. At concrete
            // types: no one fn, an impossible bound: nothing runs.)
            Ok(None) if mode.is_some() => Resolved::Open,
            Ok(None) | Err(_) => Resolved::None,
        }
    }

    fn read_instance(&mut self, work: Work<'tcx>) {
        // Whether what `reach` does with `callee` can turn on a trust: it is
        // read as an instance (it names a type of this crate), or it is
        // asked about at a holder's type (S4b).
        fn beneath_turns<'tcx>(
            this: &mut Checker<'_, 'tcx>,
            callee: ty::Instance<'tcx>,
            open: Option<DefId>,
        ) -> bool {
            let mode = open.filter(|_| callee.has_non_region_param());
            this.names_local_in(callee.args, mode)
                || this.handed(callee, Handed::Inlined, mode).1.is_some()
        }
        let tcx = self.tcx;
        let instance = work.instance;
        let local = matches!(instance.def, InstanceKind::Item(def) if def.is_local());
        // A body that is not this crate's has no place in this crate's
        // source: what it does is laid to where this crate named the way to
        // it.
        let root =
            work.through.map_or_else(|| tcx.typeck_root_def_id(instance.def_id()), |way| way.root);
        let through = work.through.map(|way| way.named);
        let hidden = work.through.map_or(0, |way| way.trusted);
        let cover = work.through.and_then(|way| way.cover);
        let at = |span: Span| work.through.map_or(span, |way| way.at);
        // An open reading ([`Work::open`]): what names a parameter is judged
        // whatever the parameters stand for. Where a body of this crate
        // STANDS, what names none is judged too, as at any instance; in any
        // other open reading it is judged where its own body stands (a body
        // of another crate: it names no type of this crate).
        let open = work.open;
        let standing = local && open.is_some() && instance == self.standing(instance.def_id());
        // What the code of the facts read now was inlined through
        // ([`Fact::At`]).
        let mut inlined: Rc<[ty::Instance<'tcx>]> = Rc::from(Vec::new());
        if let InstanceKind::Shim(ShimKind::DropGlue(_, Some(ty))) = instance.def {
            if let ty::Coroutine(def, args) = *ty.kind() {
                if def.is_local() {
                    self.drops_coroutine(work, def, args);
                    return;
                }
            }
        }
        if let InstanceKind::Shim(
            ShimKind::FutureDropPoll(..)
            | ShimKind::AsyncDropGlueCtor(..)
            | ShimKind::AsyncDropGlue(..),
        ) = instance.def
        {
            self.unread(work, "the glue of `async` drop, a nightly feature".to_owned());
            return;
        }
        // A fn of another crate that the walk must read (it is made at a type
        // of this crate) and whose MIR its crate's metadata does not carry:
        // a dependency built for `check` (`--emit=metadata`), which encodes
        // no MIR to run. Its body is not read, so no seal is said to hold.
        // (Review 1 of the review-14 build: in a check build every generic
        // body of a dependency was silently skipped, and a seal "held" over
        // a `mem::swap` of two holders.)
        if let InstanceKind::Item(def) = instance.def {
            if !local
                && matches!(
                    tcx.def_kind(def),
                    DefKind::Fn | DefKind::AssocFn | DefKind::Closure | DefKind::SyntheticCoroutineBody
                )
                && !tcx.is_foreign_item(def)
                // (A fn that runs only in constant evaluation has none to
                // run, in any build.)
                && !(matches!(tcx.def_kind(def), DefKind::Fn | DefKind::AssocFn)
                    && matches!(tcx.constness(def), rustc_hir::Constness::Const { always: true }))
                && !tcx.is_mir_available(def)
            {
                self.unread(
                    work,
                    format!(
                        "the body of `{}`, which the metadata of its crate does not carry (a crate \
                         built for `check`, not `build`, keeps no MIR to read: check a seal in a \
                         build that compiles the dependencies)",
                        self.trust_path(def).join("::")
                    ),
                );
                return;
            }
        }
        let Some(facts) = self.facts_at(instance.def) else { return };
        for fact in facts.iter() {
            // (Beneath what its code was inlined through: `Fact::At`.)
            if let Fact::At { ref outer } = *fact {
                inlined = outer.clone();
                continue;
            }
            if open.is_some() && !standing && !fact.names_parameter() {
                continue;
            }
            // In an open reading, a fact whose types still name a parameter
            // at the instance is judged in the open reading's typing
            // environment, whatever the parameters stand for (`mode`); one
            // whose types the instance made concrete, as at any instance.
            let sub = |this: &Self, value: Ty<'tcx>| this.sub(instance, value, open);
            let mode_of = |value: Ty<'tcx>| open.filter(|_| value.has_non_region_param());
            let beneath = |this: &mut Self, turns: bool| {
                if inlined.is_empty() {
                    work
                } else {
                    let chain = inlined.clone();
                    this.beneath(work, instance, &chain, turns)
                }
            };
            match *fact {
                Fact::At { .. } => {}
                Fact::Store { ty, kept, span } => {
                    let ty = sub(self, ty);
                    let owned = self.owns_mode(ty, mode_of(ty));
                    let placed = self.placed(owned) & !hidden;
                    if placed != 0 {
                        let site = Site::Over { ty, through, kept, cover };
                        self.found_each(placed, root, at(span), site);
                    }
                }
                Fact::Union { ty, field, span } => {
                    let ty = sub(self, ty);
                    let mode = mode_of(ty);
                    let ty::Adt(adt, args) = *ty.kind() else { continue };
                    // Another field's bytes are a value that owns one.
                    let mut owned = 0u64;
                    for (index, other) in adt.all_fields().enumerate() {
                        if index != field {
                            let other = other.ty(tcx, args).skip_norm_wip();
                            let other = match mode {
                                Some(scope) => seen_from(tcx, scope, other),
                                None => at_instance(tcx, None, other),
                            };
                            owned |= self.owns_mode(other, mode);
                        }
                    }
                    let owned = self.placed(owned) & !hidden;
                    if owned != 0 {
                        let site = Site::Union { ty, through, cover };
                        self.found_each(owned, root, at(span), site);
                    }
                }
                Fact::Fn { ty, span, called } => {
                    if let ty::FnDef(def, args) = *sub(self, ty).kind() {
                        let mode =
                            open.filter(|_| args.has_non_region_param() || args.has_aliases());
                        match self.resolve(work, def, args.skip_binder(), mode) {
                            Resolved::Item(named) => {
                                let turns = beneath_turns(self, named, open);
                                let from = beneath(self, turns);
                                // (A fn item named as a value is a fn
                                // pointer: `Handed::Pointer`.)
                                let how = if called { Handed::Named } else { Handed::Pointer };
                                self.reach(from, named, span, how);
                            }
                            Resolved::Open => {
                                if let Some(scope) = mode {
                                    let from = beneath(self, true);
                                    self.unresolved(from, def, args.skip_binder(), span, scope);
                                }
                            }
                            Resolved::None => {}
                        }
                    }
                }
                Fact::Drop { ty, span } => {
                    let ty = sub(self, ty);
                    let mode = mode_of(ty);
                    let turns = self.names_local_in(tcx.mk_args(&[ty.into()]), mode);
                    let from = beneath(self, turns);
                    match mode {
                        Some(scope) => self.drops_open(from, ty, span, scope),
                        None => self.drops(from, ty, span),
                    }
                }
                Fact::Unsize { source, target, span } => {
                    let (source, target) = (sub(self, source), sub(self, target));
                    let mode = open.filter(|_| {
                        source.has_non_region_param()
                            || target.has_non_region_param()
                            || source.has_aliases()
                            || target.has_aliases()
                    });
                    let turns = self.names_local_in(tcx.mk_args(&[source.into()]), mode);
                    let from = beneath(self, turns);
                    self.unsizes(from, source, target, span, mode);
                }
                // A closure made a fn pointer: what a call through it runs.
                Fact::Closure { ty, span } => {
                    let ty = sub(self, ty);
                    if let ty::Closure(def, args) = *ty.kind() {
                        let called =
                            ty::Instance::resolve_closure(tcx, def, args, ty::ClosureKind::FnOnce);
                        let turns = self.names_local_in(args, mode_of(ty));
                        let from = beneath(self, turns);
                        self.reach(from, called, span, Handed::Pointer);
                    }
                }
                Fact::Inlined { callee, ref outer, span } => {
                    // Beneath what it was inlined through: what is trusted
                    // there, or was said of it, covers this one, as on the
                    // way of a call (`Checker::beneath`). (A trust of a fn
                    // inlined through is relied on only where what is
                    // reached beneath it can turn on one: it names a type of
                    // this crate, or is handed a holder.)
                    let callee = self.sub(instance, callee, open);
                    let turns = beneath_turns(self, callee, open);
                    let beneath = self.beneath(work, instance, outer, turns);
                    self.reach(beneath, callee, span, Handed::Inlined);
                }
                Fact::Recast { source, target, span } => {
                    let (source, target) = (sub(self, source), sub(self, target));
                    let mode = open
                        .filter(|_| source.has_non_region_param() || target.has_non_region_param());
                    let pointed = self.pointed(source, mode);
                    // (A pointer to a type that owns as much still says what
                    // is written through it: `*mut MaybeUninit<App>`.)
                    let still = match target.builtin_deref(true) {
                        Some(pointee) => self.owns_mode(pointee, mode),
                        None => 0,
                    };
                    let lost = self.placed(pointed & !still);
                    if let (true, Some(through)) = (lost & !hidden != 0, through) {
                        let site = Site::Recast { ty: source, to: target, through, cover };
                        self.found_each(lost & !hidden, root, at(span), site);
                    }
                    // (Beneath a trusted fn: part of what the author's word
                    // covers, and said when the seal holds.)
                    for seal in 0..self.seals.len() {
                        if lost & hidden & (1 << seal) != 0 {
                            let said = self.recast_on.entry(seal).or_default();
                            if said.len() < LISTED {
                                said.insert(format!("a `{source}` as a `{target}`"));
                            }
                        }
                    }
                }
                // (What a body of a crate outside the standard library
                // handles and does is asked where it is reached: `reach`.)
                Fact::Holds { .. } | Fact::Unsafe { .. } => {}
                // What a constant's initializer names is named here too.
                // (What it RUNS is judged where the constant is defined.)
                Fact::Const { def, args, span } => {
                    let args = self.sub(instance, args, open);
                    let mode = open.filter(|_| args.has_non_region_param() || args.has_aliases());
                    match self.resolve(work, def, args, mode) {
                        Resolved::Item(named) => {
                            let turns = self.names_local_in(args, mode);
                            let from = beneath(self, turns);
                            self.reach(from, named, span, Handed::Value);
                        }
                        Resolved::Open => {
                            if let Some(scope) = mode {
                                let from = beneath(self, true);
                                self.unresolved(from, def, args, span, scope);
                            }
                        }
                        Resolved::None => {}
                    }
                }
            }
        }
        // What a body that is not this crate's uses: the compiler's own
        // answer, the one it makes the program's instances from. (It reads
        // what the facts above cannot: a fn pointer or a vtable inside a
        // constant another body promoted, a fn item that optimization left
        // only as a type.)
        // (Not of an open reading: the collector makes concrete instances
        // only. What a generic body of another crate names at a type that
        // mentions a parameter its facts say: such a name cannot be in a
        // constant its compiler evaluated, which names no parameter.)
        // Asked as `trust_seal_items_of_instance`, which is `items_of_instance`
        // but where a body it lists has no MIR in its crate's metadata (a
        // dependency built for `check`): there the collector stops the build
        // ("missing optimized MIR", which names no seal; the check build of
        // aterm-gui, at the `Drop` impl of winit's `EventLoopProxy<Wake>` that
        // drop glue calls), and this lists it as used, as it is where the MIR
        // is there. The walk then reaches it as any other, and refuses every
        // seal where it would read it (the unread body, above).
        let collected = open.is_none()
            && match instance.def {
                InstanceKind::Item(def) => {
                    !local
                        && matches!(
                            tcx.def_kind(def),
                            DefKind::Fn
                                | DefKind::AssocFn
                                | DefKind::Closure
                                | DefKind::SyntheticCoroutineBody
                        )
                }
                InstanceKind::Shim(_) => true,
                InstanceKind::Intrinsic(..)
                | InstanceKind::LlvmIntrinsic(..)
                | InstanceKind::Virtual(..) => false,
            };
        if collected {
            let errors = tcx.dcx().err_count();
            let collected = tcx.trust_seal_items_of_instance(instance);
            if tcx.dcx().err_count() > errors {
                // (The compiler evaluates what an instance needs when it is
                // made; a full build makes only the instances that can run.)
                tcx.dcx()
                    .struct_span_note(
                        at(tcx.def_span(root)),
                        format!(
                            "the error above was met while a seal was checked: the check reads \
                             `{instance}`, which `{}` names, as it reads what every body of the \
                             crate names, also a body that nothing calls",
                            item_path(tcx, root)[1..].join("::")
                        ),
                    )
                    .emit();
            }
            match collected {
                Ok(items) => {
                    for item in items.used.iter().chain(items.mentioned.iter()) {
                        if let MonoItem::Fn(used) = item.node {
                            self.reach(work, used, item.span, Handed::Named);
                        }
                    }
                }
                Err(_) => self.unread(work, format!("what `{instance}` uses")),
            }
        }
    }

    /// Whether the body `def` (of another crate) is one a fn that runs it
    /// CHOSE: a free fn, or an inherent method, named by the code that calls
    /// it. Not a method of a trait (of an impl, or the trait's own provided
    /// one): which body runs is the type's, and so the caller's (a body
    /// inside such a method, too); nor a closure, a coroutine or the body
    /// an `async` closure runs when called once (a `SyntheticCoroutineBody`,
    /// which `is_closure_like` does not count: review 2 of the review-14
    /// build found one read as chosen, beneath a trusted runner), which
    /// whoever made it handed on. Said by the kind of item, never by what
    /// the body does.
    fn chosen(&self, def: DefId) -> bool {
        let tcx = self.tcx;
        if tcx.is_closure_like(def) || matches!(tcx.def_kind(def), DefKind::SyntheticCoroutineBody)
        {
            return false;
        }
        let owner = tcx.typeck_root_def_id(def);
        tcx.trait_of_assoc(owner).is_none() && tcx.trait_impl_of_assoc(owner).is_none()
    }

    /// How a body that is not this crate's, which `from` names at `span`, is
    /// reached. `named`: what stands for it in a note; `trusts`: whether a
    /// `trusts` entry may name it (a fn, not a shim).
    fn way(&mut self, from: Work<'tcx>, named: DefId, span: Span, trusts: bool) -> Through {
        let trusted = if trusts { self.trusting(named) } else { 0 };
        let item = if trusts { self.trust_item(named) } else { None };
        let mut way = match from.through {
            Some(way) => way,
            None => Through {
                at: span,
                root: self.tcx.typeck_root_def_id(from.instance.def_id()),
                named,
                trusted: 0,
                own: OwnId::NONE,
                cover: None,
                valued: false,
            },
        };
        way.trusted |= trusted;
        if way.cover.is_none() {
            way.cover = item;
        }
        if trusts && self.third_party(named) {
            // (A fn the way chose to call: what was said of the way covers
            // IT, through `trusted`. A body the way did NOT choose was
            // stripped of that before it got here: `reach`.) What covers the
            // bodies of this fn's crate that the way did not choose is only
            // what names a fn OF that crate on the way: kept for each crate.
            // (Review 1 of the review-14 build: every trust gathered on the
            // way was kept here, a trust of crate A's fn among them, and so
            // covered crate B's impl method. Review 2: entering B forgot what
            // named A's fns, and A's impl method beneath B was refused.)
            way.own = self.own_with(way.own, named.krate, trusted);
        }
        way
    }

    /// `work` as the code inlined through `chain` (outermost first) in the
    /// body of `instance` reaches what it names: beneath each, as a call of
    /// it would be (`reach`: a fn of a crate outside the standard library
    /// that the fn before it did not choose is stripped to its own crate's
    /// trusts; each one's trust is added, and kept for its crate), and with
    /// what each is handed (said where it is reached itself, `Fact::Inlined`).
    /// `turns`: whether what is reached can turn on a trust (the trusts of
    /// the chain are then relied on).
    fn beneath(
        &mut self,
        work: Work<'tcx>,
        instance: ty::Instance<'tcx>,
        chain: &[ty::Instance<'tcx>],
        turns: bool,
    ) -> Work<'tcx> {
        let mut beneath = work;
        if beneath.through.is_none() {
            return beneath;
        }
        for through in chain.iter() {
            let through = self.sub(instance, *through, work.open);
            let mode = work.open.filter(|_| through.has_non_region_param());
            let def = through.def_id();
            let (owned, _) = self.handed(through, Handed::Inlined, mode);
            let trusted = self.trusting(def);
            if turns {
                self.relied_on.insert(def);
                if trusted != 0 {
                    self.trust_used(def);
                }
            }
            let item = self.trust_item(def);
            let item_body = matches!(through.def, InstanceKind::Item(_));
            let unchosen = item_body && self.third_party(def) && !self.chosen(def);
            let own_crate = item_body && self.third_party(def);
            let Some(mut way) = beneath.through else { break };
            if unchosen {
                way.trusted = self.own_get(way.own, def.krate);
                way.cover = None;
            }
            way.trusted |= trusted | owned;
            if way.cover.is_none() {
                way.cover = item;
            }
            if own_crate {
                way.own = self.own_with(way.own, def.krate, trusted);
            }
            beneath.through = Some(way);
        }
        beneath
    }

    // ----- what the way keeps for each crate -------------------------------

    fn own_intern(&mut self, table: Vec<(CrateNum, u64)>) -> OwnId {
        if table.is_empty() {
            return OwnId::NONE;
        }
        let table: Rc<[(CrateNum, u64)]> = table.into();
        if let Some(&known) = self.own_index.get(&table) {
            return known;
        }
        let id = OwnId(self.own_tables.len() as u32);
        self.own_tables.push(table.clone());
        self.own_index.insert(table, id);
        id
    }

    /// The seals kept for `krate` in the table `own`.
    fn own_get(&self, own: OwnId, krate: CrateNum) -> u64 {
        self.own_tables[own.0 as usize]
            .iter()
            .find(|(of, _)| *of == krate)
            .map_or(0, |(_, bits)| *bits)
    }

    /// The table `own` with `bits` added for `krate`.
    fn own_with(&mut self, own: OwnId, krate: CrateNum, bits: u64) -> OwnId {
        if bits == 0 || self.own_get(own, krate) & bits == bits {
            return own;
        }
        let mut table: Vec<(CrateNum, u64)> = self.own_tables[own.0 as usize].to_vec();
        match table.iter_mut().find(|(of, _)| *of == krate) {
            Some((_, kept)) => *kept |= bits,
            None => table.push((krate, bits)),
        }
        table.sort_unstable_by_key(|(of, _)| of.as_u32());
        self.own_intern(table)
    }

    /// The table `own` with only the seals of `mask` kept.
    fn own_and(&mut self, own: OwnId, mask: u64) -> OwnId {
        let table: Vec<(CrateNum, u64)> = self.own_tables[own.0 as usize]
            .iter()
            .map(|&(krate, bits)| (krate, bits & mask))
            .filter(|(_, bits)| *bits != 0)
            .collect();
        self.own_intern(table)
    }

    /// For each crate, the seals both tables keep.
    fn own_meet(&mut self, a: OwnId, b: OwnId) -> OwnId {
        if a == b {
            return a;
        }
        let table: Vec<(CrateNum, u64)> = self.own_tables[a.0 as usize]
            .iter()
            .map(|&(krate, bits)| (krate, bits & self.own_get(b, krate)))
            .filter(|(_, bits)| *bits != 0)
            .collect();
        self.own_intern(table)
    }

    /// Whether each crate's seals in `a` are kept in `b` too.
    fn own_within(&self, a: OwnId, b: OwnId) -> bool {
        self.own_tables[a.0 as usize]
            .iter()
            .all(|&(krate, bits)| bits & !self.own_get(b, krate) == 0)
    }

    /// S4b of the instance `instance` of a fn of another crate: the seals a
    /// type argument of it owns (with a writer), the first such argument,
    /// and unless it is HANDED NOTHING. A fn that takes no argument, like a
    /// `const` item's initializer, is handed no place to write
    /// (`size_of::<App>()`, `TypeId::of`). Of a fn the optimizer inlined
    /// (which the build under review 13 did not ask about at all) the
    /// argument types are read: one handed neither a value that owns a
    /// sealed value, nor a pointer to one, nor anything through which one
    /// can be written ([`Self::reach_of`]) is handed nothing
    /// (`RawVec::<App>::new_in(alloc)`). (Review 14: read by the shapes of a
    /// few pointer types alone, an `Option<&mut App>` was "nothing".)
    /// The seals a value of which whoever calls `instance` through a fn
    /// pointer (or a `dyn`) can have it write: what its inputs let be
    /// written ([`Self::reach_of`], [`Self::owns`]), but the first input of a
    /// vtable's method or drop (`receiver`: the `dyn`'s own value). Read off
    /// the instance's own body, the compiler's, at the instance; every seal
    /// where there is none to read or a type is not concrete (fail-closed).
    /// Of the inputs, also what a `dyn` of a trait of another crate in one
    /// may have been handed anywhere ([`Self::dyn_handed`]). In an open
    /// reading (`mode`), what they reach whatever the parameters stand for.
    fn caller_reach(
        &mut self,
        instance: ty::Instance<'tcx>,
        receiver: bool,
        mode: Option<DefId>,
    ) -> u64 {
        let tcx = self.tcx;
        let body = match instance.def {
            InstanceKind::Item(def)
                if !def.is_local()
                    && matches!(
                        tcx.def_kind(def),
                        DefKind::Fn
                            | DefKind::AssocFn
                            | DefKind::Closure
                            | DefKind::SyntheticCoroutineBody
                    )
                    && !tcx.is_foreign_item(def)
                    && tcx.is_mir_available(def) =>
            {
                tcx.instance_mir(instance.def)
            }
            InstanceKind::Shim(shim) if Self::shim_is_read(shim) => tcx.instance_mir(instance.def),
            // (Empty drop glue drops nothing.)
            InstanceKind::Shim(ShimKind::DropGlue(_, None)) => return 0,
            _ => return self.placed(self.all()),
        };
        let mut reach = 0u64;
        for (index, local) in body.args_iter().enumerate() {
            if receiver && index == 0 {
                continue;
            }
            let ty = self.sub(instance, body.local_decls[local].ty, mode);
            if mode.is_none() && (ty.has_non_region_param() || ty.has_aliases()) {
                return self.placed(self.all());
            }
            reach |=
                self.reach_mode(ty, mode, false) | self.owns_mode(ty, mode) | self.dyn_handed(ty);
        }
        self.placed(reach)
    }

    fn handed(
        &mut self,
        instance: ty::Instance<'tcx>,
        how: Handed,
        mode: Option<DefId>,
    ) -> (u64, Option<Ty<'tcx>>) {
        let tcx = self.tcx;
        let (InstanceKind::Item(def) | InstanceKind::Intrinsic(def)) = instance.def else {
            return (0, None);
        };
        if def.is_local() {
            return (0, None);
        }
        // Rust 1.101's `pin!` calls this core helper with the pinned value's
        // type as its generic argument, although the value reaches it only
        // through `&mut PinMacroHelper<T>`; it is the same pointer-only
        // `Pin::new_unchecked` step the macro made directly before.
        if tcx.crate_name(def.krate) == sym::core
            && tcx
                .opt_item_name(def)
                .is_some_and(|name| name.as_str() == "pin_new_unchecked_in_helper")
            && tcx.opt_item_name(tcx.parent(def)).is_some_and(|name| name.as_str() == "pin")
        {
            return (0, None);
        }
        let mut owned = 0u64;
        let mut owner = None;
        for arg in instance.args.types() {
            let mask = self.owns_mode(arg, mode);
            let placed = self.placed(mask);
            if placed != 0 && owner.is_none() {
                owner = Some(arg);
            }
            owned |= placed;
        }
        if owner.is_none() || how == Handed::Value {
            return (0, None);
        }
        if matches!(tcx.def_kind(def), DefKind::Fn | DefKind::AssocFn) {
            let sig = tcx.fn_sig(def).instantiate(tcx, instance.args).skip_norm_wip();
            let sig = tcx.instantiate_bound_regions_with_erased(sig);
            if sig.inputs().is_empty() {
                return (0, None);
            }
            if how == Handed::Inlined {
                let mut given = 0u64;
                for input in sig.inputs().iter() {
                    let input = match mode {
                        Some(scope) => seen_from(tcx, scope, *input),
                        None => at_instance(tcx, None, *input),
                    };
                    given |= self.owns_mode(input, mode)
                        | self.pointed(input, mode)
                        | self.reach_mode(input, mode, false);
                }
                if self.placed(given) == 0 {
                    return (0, None);
                }
            }
        }
        (owned, owner)
    }

    /// The instance `instance`, named in `from` at `span`: to be read.
    fn reach(&mut self, from: Work<'tcx>, instance: ty::Instance<'tcx>, span: Span, how: Handed) {
        let tcx = self.tcx;
        let instance = tcx.erase_and_anonymize_regions(instance);
        // In an open reading, an instance whose arguments still name a
        // parameter is read open too ([`Work::open`]); one they made
        // concrete, as any instance.
        let mode = from.open.filter(|_| instance.has_non_region_param());
        // (Review 1 of the review-14 build: dead polymorphic recursion over
        // `(T, T)` ran for minutes in the compiler's walks of its types.)
        if self
            .oversized(from, instance.args, || format!("`{}`", tcx.def_path_str(instance.def_id())))
        {
            return;
        }
        // An instance whose own bounds do not hold is one the compiler never
        // makes: nothing runs. (A body of this crate whose where-clause
        // holds for no lifetime names such instances, `vec![app; 2]` under
        // `where &'a mut App: Clone`. Review 14: asked what one uses, the
        // compiler panics.)
        if self.impossible(instance) {
            return;
        }
        let def = match instance.def {
            // A call through a `dyn`: what it runs was put in a vtable where
            // the `dyn` was made, and is read from there.
            InstanceKind::Virtual(..) => return,
            InstanceKind::Item(def) if def.is_local() => {
                if tcx.is_foreign_item(def) {
                    self.extern_fn(from, def, span);
                    return;
                }
                // A body of this crate is read as its own, whatever led to
                // it.
                if self.facts.get(&instance.def).is_some_and(|facts| facts.is_some()) {
                    self.enqueue(Work { instance, through: None, open: mode });
                }
                return;
            }
            // A shim at a type that names a parameter is no body the compiler
            // writes (its drop glue is built for concrete types only): what it
            // runs is read off its type ([`Self::open_shim`]).
            InstanceKind::Shim(_) if let Some(scope) = mode => {
                self.open_shim(from, instance, span, how, scope);
                return;
            }
            InstanceKind::Item(def)
            | InstanceKind::Intrinsic(def)
            | InstanceKind::LlvmIntrinsic(def) => Some(def),
            InstanceKind::Shim(_) => None,
        };
        // What a fn is handed to run is the hander's, not the fn's: a closure
        // of another crate among the type arguments is read on the way that
        // led HERE, before the trust of the fn it is handed to is added (a
        // dependency's closure under a trusted `Option::map`). (A closure of
        // this crate is read as this crate's own wherever it is called.) But
        // the body of an `async fn` (or a `gen fn`) is the fn's own code, which
        // the fn's own trust covers wherever its future is polled, as when it
        // is reached through the poll ([`Self::trust_item`]; review 3 of the
        // review-14 build: a trusted `async fn` handed to a trusted executor,
        // polled by this crate's own, or `.await`ed, was read here with no
        // trust at all, and refused for its own body's store, where the same
        // body as a plain fn held on the same entry).
        for arg in instance.args.iter().flat_map(|arg| arg.walk()) {
            let ty::GenericArgKind::Type(handed) = arg.kind() else { continue };
            if let ty::Closure(closure, args)
            | ty::CoroutineClosure(closure, args)
            | ty::Coroutine(closure, args) = *handed.kind()
            {
                let open = from.open.filter(|_| args.has_non_region_param());
                if !closure.is_local() && self.names_local_in(args, open) {
                    let own_body = self.trust_item(closure).is_some();
                    let way = self.way(from, closure, span, own_body);
                    let handed = ty::Instance { def: InstanceKind::Item(closure), args };
                    self.enqueue(Work { instance: handed, through: Some(way), open });
                }
            }
        }
        // The same of every body a trusted fn runs without having chosen it
        // ([`Self::chosen`]): a trait impl's method (the `Drop` impl of a
        // dependency's guard under a trusted `mem::drop`, its `Iterator`
        // impl under a trusted `for_each`), a trait's provided method that
        // the type's impl did not override, or a closure, of a crate outside
        // the standard library. A trust speaks for the fn it names and for
        // what that fn calls by name beneath it; of such a body it says only
        // what the `trusts` naming fns of the BODY'S crate on the way say.
        // (Review 14: a guard that swapped two values in its `Drop` was
        // hidden by the trust of the `mem::drop` it was handed to. Review 1
        // of the review-14 build: a provided method was not stripped.)
        let mut from = from;
        // A fn as a VALUE (a fn pointer, a vtable's method) made in a body
        // of a crate outside the standard library runs wherever the pointer
        // is called, on what its caller hands it: for the seals that its
        // inputs can reach, nothing that covered the way to that body covers
        // it, only a trust that names it. The check does not follow a fn
        // pointer to its calls, and judges the fn where it is made instead.
        // (Review 2 of the review-14 build: a trusted fn, and a trusted
        // constant, handed out `mem::swap::<T>`, and this crate swapped two
        // holders through it.) What the value holds itself (a closure's
        // captures, behind a `dyn`) the code that made it put there: that is
        // the hand-on a trust of that code covers, and says. A value the
        // standard library's own code makes stays on its way.
        if matches!(how, Handed::Pointer | Handed::Vtable)
            && from.through.is_some()
            && matches!(from.instance.def, InstanceKind::Item(made) if self.third_party(made))
        {
            let caller = self.caller_reach(instance, how == Handed::Vtable, mode);
            if caller != 0 {
                if let Some(mut way) = from.through {
                    way.trusted &= !caller;
                    way.own = self.own_and(way.own, !caller);
                    way.cover = None;
                    way.valued = true;
                    from.through = Some(way);
                }
            }
        }
        if let (Some(def), InstanceKind::Item(_)) = (def, instance.def) {
            if self.third_party(def) && !self.chosen(def) {
                if let Some(way) = from.through.as_mut() {
                    way.trusted = self.own_get(way.own, def.krate);
                    way.cover = None;
                }
            }
        }
        let mut way = self.way(from, instance.def_id(), span, def.is_some());
        if let Some(def) = def {
            // S4b: a fn of another crate at a type that owns a sealed type.
            let (owned, owner) = self.handed(instance, how, mode);
            if let Some(owner) = owner {
                self.trusted_at(def, owner, owned);
                let reported = owned & !way.trusted;
                let value = matches!(how, Handed::Pointer | Handed::Vtable) || way.valued;
                let site = Site::Foreign { def, ty: owner, value };
                self.found_each(reported, way.root, way.at, site);
                // (Said once: what it runs underneath, at the same type, is
                // not said again for these seals. Of what its own crate runs
                // that it did not choose, only for the seals refused here:
                // a seal this fn is covered for by a trust of ANOTHER crate's
                // fn is no word about this crate's impls.)
                way.trusted |= owned;
                if self.third_party(def) {
                    way.own = self.own_with(way.own, def.krate, reported);
                }
            } else if self.names_local_in(instance.args, mode) {
                // (A trust that covers what the fn runs beneath is in use.)
                self.trust_used(def);
            }
            if matches!(instance.def, InstanceKind::Intrinsic(..)) {
                return;
            }
            // S4e: a fn of a crate outside the standard library that does
            // what only `unsafe` code can, at an instance where it handles a
            // value through which a sealed value can be written.
            if self.third_party(def) && self.names_local_in(instance.args, mode) {
                if let Some((reached, ty, op)) = self.works_on(instance, mode) {
                    self.trusted_at(def, ty, reached);
                    let site = Site::Works { def, ty, op };
                    let reported = reached & !way.trusted;
                    self.found_each(reported, way.root, way.at, site);
                    // (As for S4b: said once, and of what its crate runs that
                    // it did not choose only where refused here.)
                    way.trusted |= reached;
                    way.own = self.own_with(way.own, def.krate, reported);
                }
            }
        }
        // A fn of another crate can reach this crate's code or types only
        // through a type of this crate among its arguments. (Read also when
        // the fn is refused or trusted: a generic body of THIS crate that
        // only it reaches is judged like any other.) A shim the compiler
        // writes AROUND a fn or closure of this crate reaches it whatever
        // the arguments are (the vtable entry of a `#[track_caller]` method
        // of `impl<T: Has> Flip for T`, at `u8`).
        let around_local = match instance.def {
            InstanceKind::Shim(
                ShimKind::VTable(def) | ShimKind::Reify(def, _) | ShimKind::ThreadLocal(def),
            ) => def.is_local(),
            InstanceKind::Shim(ShimKind::ClosureOnce { closure, .. }) => closure.is_local(),
            InstanceKind::Shim(ShimKind::ConstructCoroutineInClosure {
                coroutine_closure_def_id,
                ..
            }) => coroutine_closure_def_id.is_local(),
            _ => false,
        };
        if around_local || self.names_local_in(instance.args, mode) {
            // (Its trust covers the body read beneath it, at every seal.)
            if let Some(def) = def {
                self.relied_on.insert(def);
                if self.trusting(def) != 0 {
                    self.trust_used(def);
                }
            }
            self.enqueue(Work { instance, through: Some(way), open: mode });
        }
    }

    /// A shim in an open reading, at a type that names a parameter of the
    /// item `scope`: what the compiler would write for it, read off the type
    /// (the compiler builds shims for concrete types only). Drop glue drops
    /// what [`Self::drops_open`] says; the shim around a fn, a vtable's
    /// method or a closure called once runs that fn, and so does the shim
    /// through which a fn ITEM is called by the `Fn` traits; a clone the
    /// compiler writes clones each part ([`Self::clones_open`]); a call
    /// through a fn pointer is not followed, as at any instance. A shim whose
    /// body the compiler builds once, at its item's identity, for its users
    /// to make concrete (`has_polymorphic_mir_body`: an `async` closure that
    /// is `Fn` called once) is read from its own MIR, as an instance is. Any
    /// other is not read, and no seal is said to hold.
    fn open_shim(
        &mut self,
        from: Work<'tcx>,
        instance: ty::Instance<'tcx>,
        span: Span,
        how: Handed,
        scope: DefId,
    ) {
        let item = |def: DefId| ty::Instance { def: InstanceKind::Item(def), args: instance.args };
        match instance.def {
            InstanceKind::Shim(ShimKind::DropGlue(_, None)) => {}
            InstanceKind::Shim(ShimKind::DropGlue(_, Some(ty))) => {
                self.drops_open(from, ty, span, scope)
            }
            InstanceKind::Shim(ShimKind::VTable(def) | ShimKind::Reify(def, _)) => {
                self.reach(from, item(def), span, how)
            }
            // (Its arguments are the trait method's: `Self`, the closure's
            // own type with the closure's arguments, and the inputs.)
            InstanceKind::Shim(ShimKind::ClosureOnce { .. }) => {
                if let ty::Closure(closure, args) = *instance.args.type_at(0).kind() {
                    let called = ty::Instance { def: InstanceKind::Item(closure), args };
                    self.reach(from, called, span, how)
                }
            }
            InstanceKind::Shim(ShimKind::FnPtr(_, ty)) => {
                if let ty::FnDef(callee, args) = *ty.kind() {
                    match self.resolve(from, callee, args.skip_binder(), Some(scope)) {
                        Resolved::Item(called) => self.reach(from, called, span, how),
                        Resolved::Open => {
                            self.unresolved(from, callee, args.skip_binder(), span, scope)
                        }
                        Resolved::None => {}
                    }
                }
            }
            InstanceKind::Shim(ShimKind::FnPtrAsPtr(..)) => {}
            InstanceKind::Shim(ShimKind::Clone(_, ty)) => self.clones_open(from, ty, span, scope),
            // A shim whose body the compiler builds once, at the identity of
            // its item, for its users to make concrete (`has_polymorphic_mir_
            // body`: what an `async` closure that is `Fn` or `FnMut` runs when
            // called once, `ConstructCoroutineInClosure`, which moves the
            // captures into a new coroutine). Its MIR is no less the
            // compiler's at these arguments than at concrete ones: it is read
            // as an instance is. (Review 4 of the review-14 build: every seal
            // was refused for such a closure in generic code, the shim
            // unread.)
            InstanceKind::Shim(shim)
                if shim.has_polymorphic_mir_body() && Self::shim_is_read(shim) =>
            {
                let way = self.way(from, instance.def_id(), span, false);
                self.enqueue(Work { instance, through: Some(way), open: Some(scope) });
            }
            _ => self.unread(
                from,
                format!(
                    "`{instance}`, a body the compiler writes, at a type that names a type \
                     parameter of `{}` (read where it stands)",
                    self.tcx.def_path_str(scope)
                ),
            ),
        }
    }

    /// A value of type `ty`, which names a type parameter of the item
    /// `scope`, dropped in an open reading: what its drop glue would run,
    /// read off the type, whatever the parameters stand for. The glue of a
    /// type runs the type's `Drop` impl (resolved as the compiler resolves
    /// it, in the item's typing environment), then drops each field (every
    /// variant's: more than runs), a `Box`'s contents, a closure's captures,
    /// a coroutine's captures and what it keeps across a suspension; not the
    /// contents of a `ManuallyDrop` or of a union; nothing behind a pointer
    /// or a `dyn` (whose drop is read where the `dyn` is made). A type
    /// parameter drops what a crate that depends on this one makes it; a part
    /// that is concrete is dropped as at any instance ([`Self::drops`]).
    fn drops_open(&mut self, work: Work<'tcx>, ty: Ty<'tcx>, span: Span, scope: DefId) {
        let mut visited: FxHashSet<Ty<'tcx>> = FxHashSet::default();
        self.drops_open_in(work, ty, span, scope, &mut visited);
    }

    fn drops_open_in(
        &mut self,
        work: Work<'tcx>,
        ty: Ty<'tcx>,
        span: Span,
        scope: DefId,
        visited: &mut FxHashSet<Ty<'tcx>>,
    ) {
        let tcx = self.tcx;
        let ty = seen_from(tcx, scope, ty);
        if owns_nothing(ty) {
            return;
        }
        if !ty.has_non_region_param() && !ty.has_aliases() {
            self.drops(Work { open: None, ..work }, ty, span);
            return;
        }
        if !visited.insert(ty) {
            return;
        }
        if visited.len() > PLAIN_BOUND {
            self.unread(work, format!("the drop of a value of type `{ty}`"));
            return;
        }
        let mut parts: Vec<Ty<'tcx>> = Vec::new();
        match *ty.kind() {
            ty::Tuple(fields) => parts.extend(fields.iter()),
            ty::Array(inner, _) | ty::Slice(inner) | ty::Pat(inner, _) => parts.push(inner),
            ty::Adt(adt, args) => {
                if adt.has_dtor(tcx) {
                    match self.drop_method() {
                        Some(method) => {
                            let args = tcx.mk_args(&[ty.into()]);
                            match self.resolve(work, method, args, Some(scope)) {
                                Resolved::Item(dropped) => {
                                    self.reach(work, dropped, span, Handed::Named)
                                }
                                Resolved::Open => self.unresolved(work, method, args, span, scope),
                                Resolved::None => {}
                            }
                        }
                        None => self.unread(work, format!("the `Drop` impl of `{ty}`")),
                    }
                }
                if adt.is_box() {
                    parts.push(args.type_at(0));
                }
                if !adt.is_manually_drop() && !adt.is_union() {
                    for field in adt.all_fields() {
                        parts.push(field.ty(tcx, args).skip_norm_wip());
                    }
                }
            }
            ty::Closure(_, args) => parts.extend(args.as_closure().upvar_tys().iter()),
            ty::CoroutineClosure(_, args) => {
                parts.extend(args.as_coroutine_closure().upvar_tys().iter())
            }
            ty::Coroutine(def, args) => {
                parts.extend(args.as_coroutine().upvar_tys().iter());
                let kept = tcx.coroutine_hidden_types(def).instantiate(tcx, args).skip_norm_wip();
                parts.extend(tcx.instantiate_bound_regions_with_erased(kept).types.iter());
            }
            // A rigid projection that may hold one (`Self::alias_mask`):
            // what its drop runs is some impl's, unknown code at that type.
            ty::Alias(..) => match self.alias_read(ty, scope) {
                AliasRead::Is(normalized) => parts.push(normalized),
                AliasRead::Rigid if self.alias_mask(ty, scope) != 0 => match self.drop_method() {
                    Some(method) => {
                        self.unresolved(work, method, tcx.mk_args(&[ty.into()]), span, scope)
                    }
                    None => self.unread(work, format!("the drop of a value of type `{ty}`")),
                },
                _ => {}
            },
            // (A type parameter, a `dyn`: see above.)
            _ => {}
        }
        for part in parts {
            rustc_data_structures::stack::ensure_sufficient_stack(|| {
                self.drops_open_in(work, part, span, scope, visited)
            });
        }
    }

    /// `Drop::drop`, the trait's method.
    fn drop_method(&self) -> Option<DefId> {
        let tcx = self.tcx;
        tcx.lang_items().drop_trait().and_then(|drop_trait| {
            tcx.associated_item_def_ids(drop_trait)
                .iter()
                .copied()
                .find(|method| tcx.item_name(*method) == sym::drop)
        })
    }

    /// A clone the compiler writes (of a tuple, an array, a closure), at a
    /// type that names a type parameter of the item `scope`: it clones each
    /// part, by the part's own `Clone` impl as the compiler resolves it in the
    /// item's typing environment (one a parameter picks is that parameter's).
    fn clones_open(&mut self, work: Work<'tcx>, ty: Ty<'tcx>, span: Span, scope: DefId) {
        let tcx = self.tcx;
        let Some(clone) = tcx.lang_items().clone_fn() else { return };
        let parts: Vec<Ty<'tcx>> = match *ty.kind() {
            ty::Tuple(fields) => fields.iter().collect(),
            ty::Array(inner, _) => vec![inner],
            ty::Closure(_, args) => args.as_closure().upvar_tys().iter().collect(),
            ty::CoroutineClosure(_, args) => {
                args.as_coroutine_closure().upvar_tys().iter().collect()
            }
            ty::Coroutine(_, args) => args.as_coroutine().upvar_tys().iter().collect(),
            _ => Vec::new(),
        };
        for part in parts {
            let part = seen_from(tcx, scope, part);
            let args = tcx.mk_args(&[part.into()]);
            match self.resolve(work, clone, args, Some(scope)) {
                Resolved::Item(cloned) => self.reach(work, cloned, span, Handed::Named),
                // (One a parameter picks: an abstract impl, at the part's
                // type. Review 4 of the review-14 build: it was skipped.)
                Resolved::Open => self.unresolved(work, clone, args, span, scope),
                Resolved::None => {}
            }
        }
    }

    /// An ABSTRACT impl, in an open reading: `def` at `args` (which name a
    /// parameter of the item `scope`) where the compiler names no one body
    /// ([`Resolved::Open`]): a method or a constant of a trait whose impl
    /// the instance picks (a where-clause or a projection bound says only
    /// that one exists), or an item at arguments the item's environment
    /// cannot normalize. Which body runs is not read, so it is UNKNOWN CODE
    /// at every type its signature names ([`Self::abstract_reach`]): its
    /// type arguments, its inputs, what it hands back, a constant's own
    /// type, and what a fn pointer or a `dyn` among them may be handed. A
    /// seal such a type owns, or lets be written, is refused at the item,
    /// whatever led to it (no trust of the way it was met on covers it: the
    /// fn that ran it did not choose it):
    ///
    /// - an item of another crate's trait that this crate does not
    ///   implement (its impls are that crate's or a third's, any of which
    ///   may run), unless a `trusts` entry names that item itself;
    /// - an item of THIS crate, or of a trait of another crate that this
    ///   crate implements: what runs may be this crate's own impl, read where
    ///   it stands at its own parameters, which says nothing of what they
    ///   stand for here. No `trusts` entry answers it (an entry speaks for
    ///   code of another crate).
    ///
    /// (Review 4 of the review-14 build: an item of a trait of this crate
    /// whose impl a where-clause picked was skipped, and a dependency's
    /// trait item was judged by its type arguments alone. Review 5: the
    /// round-4 rule took off what the trait's own declaration names from
    /// every type handed, seal by seal, so an unused `&mut App` input made
    /// `Self = (T, App)` pass; it hid the item behind the trust of the way;
    /// it read a constant's type and a fn's inputs but not what a method
    /// hands back (`fn op() -> fn(&mut Self::Item, ..)`, a `Box<dyn Fn>`, an
    /// `impl Fn`), nor what a `&dyn Fn(&mut Self::Item, ..)` is handed; and
    /// an entry for another crate's trait item covered this crate's impl of
    /// it. Each swapped two holders under a seal that held.)
    ///
    /// But a call through the `Fn` traits of a callee whose type is a type
    /// PARAMETER (`f(app)` of an `F: FnOnce(&mut App)`): what runs is the
    /// callee value's own body, a closure, fn item or fn pointer that the
    /// crate instantiating the parameter chose and handed in (the standard
    /// library's impls of these traits for `&F`, `&mut F` and `Box<F>` call
    /// `F`; closures, fn items and fn pointers implement them built in; no
    /// other crate can implement them in stable Rust), so it is read where an
    /// instance of this crate makes the parameter concrete, and one only a
    /// crate that depends on this one makes is that crate's. (The first open
    /// build refused aterm-gui's `App::set_font_px_with`.) A callee whose
    /// type is a projection (`K::Op`, an `impl Fn` a trait method hands
    /// back) is a value an impl chose: judged as any abstract impl.
    fn unresolved(
        &mut self,
        work: Work<'tcx>,
        def: DefId,
        args: GenericArgs<'tcx>,
        span: Span,
        scope: DefId,
    ) {
        let tcx = self.tcx;
        if let Some(of) = tcx.trait_of_assoc(def) {
            if (tcx.fn_trait_kind_from_def_id(of).is_some()
                || tcx.async_fn_trait_kind_from_def_id(of).is_some())
                && args.types().next().is_some_and(|callee| matches!(callee.kind(), ty::Param(_)))
            {
                return;
            }
        }
        let (root, at) = match work.through {
            Some(way) => (way.root, way.at),
            None => (tcx.typeck_root_def_id(work.instance.def_id()), span),
        };
        let handed = self.abstract_reach(def, args, scope);
        let placed = handed.iter().fold(0, |mask, (_, bits)| mask | bits);
        let Some(&(ty, _)) = handed.first() else { return };
        let ours =
            def.is_local() || tcx.trait_of_assoc(def).is_some_and(|of| self.implemented_here(of));
        if ours {
            self.found_each(placed, root, at, Site::Picked { def, ty });
            return;
        }
        let trusted = self.trusting(def);
        self.trusted_at(def, ty, placed);
        self.found_each(placed & !trusted, root, at, Site::Foreign { def, ty, value: false });
    }

    /// Whether this crate has an impl of the trait `of` (of another crate):
    /// an abstract impl of it may be this crate's own.
    fn implemented_here(&self, of: DefId) -> bool {
        self.tcx.all_local_trait_impls(()).get(&of).is_some_and(|impls| !impls.is_empty())
    }

    /// What an abstract impl ([`Self::unresolved`]) of `def` at `args` is
    /// handed, read whatever the parameters of the item `scope` stand for:
    /// each type its signature names (its type arguments; a fn's inputs and
    /// what it hands back, which its caller may call; a constant's own type)
    /// that owns or lets be written a sealed value (with a writer; a rigid
    /// projection as [`Self::alias_mask`] says; through a `dyn` of another
    /// crate's trait, [`Self::dyn_handed`]; and what a fn pointer or a `dyn`
    /// in it may be handed: a `&dyn Fn(&mut Self::Item, ..)` is handed two
    /// `&mut (T, App)`), with those seals.
    fn abstract_reach(
        &mut self,
        def: DefId,
        args: GenericArgs<'tcx>,
        scope: DefId,
    ) -> Vec<(Ty<'tcx>, u64)> {
        let tcx = self.tcx;
        let mut handed: Vec<Ty<'tcx>> = args.types().collect();
        match tcx.def_kind(def) {
            DefKind::Fn | DefKind::AssocFn => {
                let sig = tcx.fn_sig(def).instantiate(tcx, args).skip_norm_wip();
                let sig = tcx.instantiate_bound_regions_with_erased(sig);
                handed.extend(sig.inputs_and_output.iter());
            }
            DefKind::Const { .. } | DefKind::AssocConst { .. } => {
                handed.push(tcx.type_of(def).instantiate(tcx, args).skip_norm_wip());
            }
            _ => {}
        }
        let mut out = Vec::new();
        for ty in handed {
            let ty = seen_from(tcx, scope, ty);
            let mut reached = self.owns_whatever(ty, scope, false)
                | self.reach_open(ty, scope, false)
                | self.dyn_handed(ty);
            // (What a `dyn` in it may be handed: its traits' arguments. A fn
            // pointer's inputs and output are what `reach_open` reads.)
            let mut given: Vec<Ty<'tcx>> = Vec::new();
            for part in ty.walk() {
                let ty::GenericArgKind::Type(part) = part.kind() else { continue };
                let ty::Dynamic(predicates, ..) = *part.kind() else { continue };
                for predicate in predicates.iter() {
                    match tcx.instantiate_bound_regions_with_erased(predicate) {
                        ty::ExistentialPredicate::Trait(bound) => given.extend(bound.args.types()),
                        ty::ExistentialPredicate::Projection(bound) => {
                            given.extend(bound.args.types());
                            given.extend(bound.term.as_type());
                        }
                        ty::ExistentialPredicate::AutoTrait(_) => {}
                    }
                }
            }
            for inner in given {
                let inner = seen_from(tcx, scope, inner);
                reached |=
                    self.owns_whatever(inner, scope, false) | self.reach_open(inner, scope, false);
            }
            let placed = self.placed(reached);
            if placed != 0 {
                out.push((ty, placed));
            }
        }
        out
    }

    /// S4e, of an instance of a fn (or closure) of a crate outside the
    /// standard library: the seals a value of which can be written through
    /// something the body handles there (the types of its locals, at the
    /// instance: [`Self::reach_of`]), one such type, and what the body does
    /// that only `unsafe` code can. `None` when it handles no such value, or
    /// does nothing of the kind: its safe operations are read like any
    /// body's.
    ///
    /// Review 14 measured what reading such code by its SHAPE is worth: a
    /// second crate's sound `unsafe` code swapped two holders through a
    /// transmuted `Option<&mut T>`, a pointer to a pointer, a union of two
    /// pointers, the address of a zero-length first field, a `*const dyn`,
    /// a fn pointer given another signature, `asm!`, and bytes kept in a
    /// container whose type names only a marker: thirteen ways, each needing
    /// a rule of its own. So no shape is read: such code, where it can reach
    /// a sealed value at all, runs on the author's word (`trusts`) or the
    /// seal is refused. The standard library's own code is still read by
    /// shape ([`Fact::Recast`]): it is one known body of code, and what it
    /// does at a type that only points to a holder was surveyed, not proved.
    /// (`mode`: an open reading's item, for an instance whose arguments name
    /// its parameters: what the locals reach whatever they stand for.)
    fn works_on(
        &mut self,
        instance: ty::Instance<'tcx>,
        mode: Option<DefId>,
    ) -> Option<(u64, Ty<'tcx>, &'static str)> {
        if let Some(known) = self.worked.get(&(instance, mode)) {
            return *known;
        }
        let worked = self.works_on_unmemoized(instance, mode);
        self.worked.insert((instance, mode), worked);
        worked
    }

    fn works_on_unmemoized(
        &mut self,
        instance: ty::Instance<'tcx>,
        mode: Option<DefId>,
    ) -> Option<(u64, Ty<'tcx>, &'static str)> {
        let facts = self.facts_at(instance.def)?;
        let op = facts.iter().find_map(|fact| match fact {
            Fact::Unsafe { what } => Some(*what),
            _ => None,
        })?;
        let mut reached = 0u64;
        let mut first = None;
        for fact in facts.iter() {
            let Fact::Holds { ty } = *fact else { continue };
            let ty = if ty.has_non_region_param() || ty.has_aliases() {
                self.sub(instance, ty, mode)
            } else {
                ty
            };
            let mask = self.reach_mode(ty, mode, false);
            let mask = self.placed(mask);
            if mask != 0 && first.is_none() {
                first = Some(ty);
            }
            reached |= mask;
        }
        first.map(|ty| (reached, ty, op))
    }

    /// A fn this crate declares in an `extern` block, named in `from`: it
    /// has no body to read, and what runs is not Rust. One that safe code
    /// can call (`unsafe extern "C" { safe fn time(to: &mut Cell) -> i64; }`)
    /// is the author's word that it is sound to call, about code held to
    /// none of Rust's rules: the check cannot read what was promised (the
    /// fn may be handed a `*mut c_void` this crate made of a sealed value in
    /// safe code), so every seal is refused unless its `trusts` name the fn.
    /// (One that only `unsafe` code can call is outside the claim.)
    fn extern_fn(&mut self, from: Work<'tcx>, def: DefId, span: Span) {
        let tcx = self.tcx;
        if !matches!(tcx.def_kind(def), DefKind::Fn)
            || tcx.fn_sig(def).skip_binder().safety().is_unsafe()
        {
            return;
        }
        let (root, at, hidden) = match from.through {
            Some(way) => (way.root, way.at, way.trusted),
            None => (tcx.typeck_root_def_id(from.instance.def_id()), span, 0),
        };
        let trusted = self.trusting(def);
        self.trust_used(def);
        let all = self.all();
        self.found_each(all & !trusted & !hidden, root, at, Site::Extern { def });
    }

    /// The drop of a coroutine of this crate (an `async` body, suspended):
    /// of what it captured, and of what it keeps across a suspension.
    fn drops_coroutine(&mut self, work: Work<'tcx>, def: DefId, args: GenericArgs<'tcx>) {
        let tcx = self.tcx;
        let span = work.through.map_or(tcx.def_span(def), |way| way.at);
        let mut parts: Vec<Ty<'tcx>> = args.as_coroutine().upvar_tys().iter().collect();
        // (What it keeps is named under a binder of the lifetimes of the
        // borrows it keeps: erased, like every lifetime here. Review 13: with
        // the binder skipped, asking the compiler for the drop of a kept
        // `slice::Iter<'_, T>` was a compiler panic.)
        let kept = tcx.coroutine_hidden_types(def).instantiate(tcx, args).skip_norm_wip();
        parts.extend(tcx.instantiate_bound_regions_with_erased(kept).types.iter());
        for part in parts {
            let part = at_instance(tcx, None, part);
            self.drops(work, part, span);
        }
    }

    /// A value of the concrete type `ty` dropped, in `work` at `span`: its
    /// drop glue, the compiler's, is read as an instance like any other.
    fn drops(&mut self, work: Work<'tcx>, ty: Ty<'tcx>, span: Span) {
        if owns_nothing(ty) {
            return;
        }
        if ty.has_non_region_param() || ty.has_aliases() {
            // (A type the compiler could not make concrete here.)
            self.unread(work, format!("the drop of a value of type `{ty}`"));
            return;
        }
        if self.oversized(work, ty, || "the drop of a value".to_owned()) {
            return;
        }
        self.reach(work, ty::Instance::resolve_drop_glue(self.tcx, ty), span, Handed::Named);
    }

    /// The parts of `value` as a walk that does not share them counts them
    /// ([`TREE_BOUND`]).
    fn tree<T: TypeVisitable<TyCtxt<'tcx>>>(&mut self, value: T) -> (u64, u32) {
        let mut size = TreeSize { memo: &mut self.tree, total: 0, depth: 0 };
        value.visit_with(&mut size);
        (size.total, size.depth)
    }

    /// Whether `value` (a type, an instance's arguments) is too large to
    /// ask the compiler about: [`TREE_BOUND`]. Then the walk stops there,
    /// and no seal is said to hold.
    fn oversized<T: TypeVisitable<TyCtxt<'tcx>>>(
        &mut self,
        work: Work<'tcx>,
        value: T,
        what: impl FnOnce() -> String,
    ) -> bool {
        let (size, depth) = self.tree(value);
        // (The deepest a type handed to the compiler may nest: its trait
        // solver takes one level of an obligation per level of the type,
        // `Option<Option<T>>: Clone` asks `Option<T>: Clone`, and stops the
        // build at an obligation nested deeper than the recursion limit,
        // with no span and no word of the seal. Review 4 of the review-14
        // build: dead polymorphic recursion that grows two levels a step
        // reached that before the walk cut at its 128th re-entry.)
        let limit = u32::try_from(self.tcx.recursion_limit().0).unwrap_or(u32::MAX);
        let cap = DEPTH_BOUND.min(limit);
        if size <= TREE_BOUND && depth <= cap {
            return false;
        }
        let tcx = self.tcx;
        let root = work
            .through
            .map_or_else(|| tcx.typeck_root_def_id(work.instance.def_id()), |way| way.root);
        let span = work.through.map_or_else(|| tcx.def_span(root), |way| way.at);
        let all = self.all();
        self.cut = true;
        let why = if size > TREE_BOUND {
            format!(
                "the crate names {}, at a type of more than {TREE_BOUND} parts as the compiler \
                 walks it (as a type that doubles at each step does, a polymorphic recursion \
                 over `(T, T)`): the check stopped reading there. (The compiler makes such an \
                 instance only where code that runs names it; this check reads every body, also \
                 one nothing calls.)",
                what()
            )
        } else if cap < DEPTH_BOUND {
            format!(
                "the crate names {}, at a type nested more than {cap} deep, the recursion limit \
                 (as polymorphic recursion makes, `grow(Some(x))`): the check stopped reading \
                 there, before the compiler's trait solver, which stops at an obligation nested \
                 deeper than that limit, is asked about it. (The compiler makes such an instance \
                 only where code that runs names it; this check reads every body, also one \
                 nothing calls.)",
                what()
            )
        } else {
            format!(
                "the crate names {}, at a type nested more than {DEPTH_BOUND} deep (as \
                 polymorphic recursion makes, `grow(Some(x))`, at a raised recursion limit): the \
                 check stopped reading there, before the compiler's own walks of so deep a type \
                 run out of stack. (The compiler makes such an instance only where code that \
                 runs names it; this check reads every body, also one nothing calls.)",
                what()
            )
        };
        self.found_each(all, root, span, Site::Shape(why));
        true
    }

    /// Whether the compiler's trait solver, asked to select the impl of the
    /// trait of the trait item `def` at `args` in `typing_env` (as resolving
    /// the item asks it: a selection, then the selection of each obligation
    /// that leaves, to the end), overflows its recursion limit. Asked the
    /// same way of the solver's CANONICAL query mode, which answers an
    /// overflow rather than stopping the build (and of each obligation once:
    /// a type that shares its parts is not walked part by part). Kept for
    /// each trait reference asked. (A canonical EVALUATION of the trait ref
    /// does not do: its cache answers each level from the level below, where
    /// the selection `try_resolve` makes walks down to the bottom.)
    fn solver_overflows(
        &mut self,
        typing_env: ty::TypingEnv<'tcx>,
        def: DefId,
        args: GenericArgs<'tcx>,
    ) -> bool {
        use rustc_infer::infer::TyCtxtInferExt;
        use rustc_trait_selection::traits::{
            Obligation, ObligationCause, OverflowError, PredicateObligation, SelectionContext,
            TraitQueryMode,
        };
        let tcx = self.tcx;
        let Some(of) = tcx.trait_of_assoc(def) else { return false };
        if args.len() < tcx.generics_of(of).count() {
            return false;
        }
        // (Its regions are erased, as `try_resolve`'s are.)
        let trait_args = args.truncate_to(tcx, tcx.generics_of(of));
        let key = (typing_env, of, trait_args);
        if let Some(&known) = self.overflows.get(&key) {
            return known;
        }
        let (infcx, param_env) =
            tcx.infer_ctxt().ignoring_regions().build_with_typing_env(typing_env);
        if infcx.next_trait_solver() {
            return false;
        }
        let trait_ref = ty::TraitRef::new_from_args(tcx, of, trait_args);
        let mut selcx = SelectionContext::with_query_mode(&infcx, TraitQueryMode::Canonical);
        let mut work: Vec<PredicateObligation<'tcx>> =
            vec![Obligation::new(tcx, ObligationCause::dummy(), param_env, trait_ref)];
        let mut asked: FxHashSet<ty::Predicate<'tcx>> = FxHashSet::default();
        let mut overflowed = false;
        let mut steps = 0usize;
        while let Some(obligation) = work.pop() {
            steps += 1;
            if steps > PLAIN_BOUND * 16 {
                break;
            }
            let predicate = infcx.deeply_resolve_via_unification_table(obligation.predicate);
            if !asked.insert(predicate) {
                continue;
            }
            let kind = predicate.kind();
            let ty::PredicateKind::Clause(ty::ClauseKind::Trait(trait_pred)) = kind.skip_binder()
            else {
                continue;
            };
            if trait_pred.polarity != ty::ClausePolarity::Positive {
                continue;
            }
            let trait_pred = infcx.enter_forall_and_leak_universe(kind.rebind(trait_pred));
            match selcx.select(&obligation.with(tcx, trait_pred)) {
                Ok(Some(source)) => work.extend(source.nested_obligations()),
                Ok(None) => {}
                Err(rustc_middle::traits::SelectionError::Overflow(OverflowError::Canonical)) => {
                    overflowed = true;
                    break;
                }
                Err(_) => {}
            }
        }
        self.overflows.insert(key, overflowed);
        overflowed
    }

    /// The trait solver would overflow asked about `what` ([`Self::
    /// solver_overflows`]): the walk stops there, and no seal is said to
    /// hold.
    fn overflowed(&mut self, work: Work<'tcx>, what: impl FnOnce() -> String) {
        let tcx = self.tcx;
        let root = work
            .through
            .map_or_else(|| tcx.typeck_root_def_id(work.instance.def_id()), |way| way.root);
        let span = work.through.map_or_else(|| tcx.def_span(root), |way| way.at);
        let limit = tcx.recursion_limit().0;
        let all = self.all();
        self.cut = true;
        self.found_each(
            all,
            root,
            span,
            Site::Shape(format!(
                "the crate names {}, at types the compiler's trait solver cannot settle within \
                 the recursion limit ({limit}) (as polymorphic recursion makes, `grow(W(x))`, \
                 where each level of the type costs the solver more than one level of an \
                 obligation): the check stopped reading there, before asking which impl runs, \
                 which would stop the build. (The compiler makes such an instance only where \
                 code that runs names it; this check reads every body, also one nothing calls.)",
                what()
            )),
        );
    }

    /// Something `work` runs could not be read: no seal is said to hold.
    fn unread(&mut self, work: Work<'tcx>, what: String) {
        let tcx = self.tcx;
        let root = work
            .through
            .map_or_else(|| tcx.typeck_root_def_id(work.instance.def_id()), |way| way.root);
        let span = work.through.map_or_else(|| tcx.def_span(root), |way| way.at);
        let all = self.all();
        self.cut = true;
        self.found_each(
            all,
            root,
            span,
            Site::Shape(format!(
                "the check could not read {what}: it says nothing of what runs there"
            )),
        );
    }

    /// An unsizing coercion from `source` to `target`. Each `dyn` it makes
    /// of a concrete type puts every method of the trait for that type, and
    /// the type's drop, where anything handed the `dyn` can run them: they
    /// are read from here (the vtable is the compiler's).
    ///
    /// And when the pointer has a GRIP on what it points to (it owns it, a
    /// `Box` or an `Rc`; or the value can be written through it: a `&mut`, a
    /// raw pointer, a `&` to something with a cell on the way or in it), the
    /// `dyn` holds what the value holds from now on. Of a trait of this
    /// crate, by [`Self::owns`]. Of any other (S4d), it is a holder that
    /// code of other crates can take, and write, with no type of this crate
    /// in sight: a fn of another crate that is not generic is never read.
    /// That is refused unless a `trusts` entry names the trait. (A plain
    /// `&App` as a `&dyn Debug` has no grip: sound code cannot write through
    /// it.)
    ///
    /// Where a crate OUTSIDE THE STANDARD LIBRARY may know what is behind
    /// the `dyn`, more is asked: a value that only POINTS to a holder (a
    /// `&mut App`, a closure that captured one) is refused too. That is a
    /// `dyn` of a trait of such a crate, wherever it is made (the crate can
    /// know what every value behind its trait is, a trait it alone
    /// implements, and read the pointer back out in code that names no
    /// type); and any `dyn` made IN A BODY of such a crate (the body and
    /// the fn it hands the `dyn` to can agree on what is behind it). Nothing
    /// can know that of a `dyn FnMut()` this crate or the standard library
    /// makes: a std trait is implemented by anything.
    fn unsizes(
        &mut self,
        work: Work<'tcx>,
        source: Ty<'tcx>,
        target: Ty<'tcx>,
        span: Span,
        mode: Option<DefId>,
    ) {
        let tcx = self.tcx;
        if self.oversized(work, (source, target), || "a `dyn` made of a value".to_owned()) {
            return;
        }
        // (A concrete reading whose types are not concrete: nothing here can
        // be asked of the compiler. Never skipped.)
        if mode.is_none()
            && (source.has_non_region_param()
                || target.has_non_region_param()
                || source.has_aliases()
                || target.has_aliases())
        {
            self.unread(work, format!("a `dyn` made of a value of type `{source}` as `{target}`"));
            return;
        }
        let root = work
            .through
            .map_or_else(|| tcx.typeck_root_def_id(work.instance.def_id()), |way| way.root);
        let through = work.through.map(|way| way.named);
        let hidden = work.through.map_or(0, |way| way.trusted);
        let cover = work.through.and_then(|way| way.cover);
        let at = work.through.map_or(span, |way| way.at);
        let in_third =
            matches!(work.instance.def, InstanceKind::Item(def) if self.third_party(def));
        // (Logged, for `settle_erasures`.)
        if self.unsize_seen.insert((source, target, in_third, mode)) {
            self.unsize_log.push((source, target, in_third, mode));
        }
        for erasure in self.erasures_of(source, target, in_third, mode) {
            self.record_erasure(&erasure);
            let Erasure { concrete, to, predicates, principal, held, mode, .. } = erasure;
            if held != 0 && !principal.is_some_and(|principal| principal.is_local()) {
                let trusted = principal.map_or(0, |principal| self.trusting(principal));
                let shown = held & !hidden & !trusted;
                if shown != 0 {
                    self.found_each(
                        shown,
                        root,
                        at,
                        Site::Erased { ty: concrete, to, through, cover },
                    );
                }
                // What the author's word covers here is said when the seal
                // holds.
                if let Some(principal) = principal {
                    self.trusted_at(principal, concrete, held & trusted & !hidden);
                }
                let covered = held & hidden;
                for seal in 0..self.seals.len() {
                    if covered & (1 << seal) != 0 {
                        let said = self.handed_on.entry(seal).or_default();
                        if said.len() < LISTED {
                            said.insert(format!("a `{concrete}` as a `{to}`"));
                        }
                    }
                }
            }
            if matches!(concrete.kind(), ty::Dynamic(..)) {
                continue;
            }
            if let Some(principal) = predicates.principal() {
                let trait_ref = tcx.instantiate_bound_regions_with_erased(
                    principal.map_bound(|principal| principal.with_self_ty(tcx, concrete)),
                );
                match mode {
                    None => {
                        let trait_ref = at_instance(tcx, None, trait_ref);
                        // (`vtable_entries` takes a concrete trait ref only:
                        // `erasures_of` reads one that names a parameter
                        // open. One it could not make concrete is unread.)
                        if trait_ref.has_non_region_param() || trait_ref.has_aliases() {
                            self.unread(work, format!("the vtable of `{concrete}` as a `{to}`"));
                            continue;
                        }
                        // (What a `dyn` runs, it runs wherever it is used:
                        // values.)
                        for entry in tcx.vtable_entries(trait_ref) {
                            if let ty::VtblEntry::Method(method) = entry {
                                self.reach(work, *method, span, Handed::Vtable);
                            }
                        }
                    }
                    Some(scope) => self.vtable_open(work, trait_ref, span, scope),
                }
            }
            if !owns_nothing(concrete) {
                match mode {
                    None => self.reach(
                        work,
                        ty::Instance::resolve_drop_glue(tcx, concrete),
                        span,
                        Handed::Vtable,
                    ),
                    Some(scope) => self.drops_open(work, concrete, span, scope),
                }
            }
        }
    }

    /// What an unsizing coercion from `source` to `target` hands to each
    /// `dyn` it makes ([`Self::unsizes`]): a question about the two types
    /// alone (`in_third`: made in a body of a crate outside the standard
    /// library; `open`: an open reading's item, for types that name its
    /// parameters, read whatever they stand for).
    fn erasures_of(
        &mut self,
        source: Ty<'tcx>,
        target: Ty<'tcx>,
        in_third: bool,
        open: Option<DefId>,
    ) -> Vec<Erasure<'tcx>> {
        let tcx = self.tcx;
        let mut out = Vec::new();
        let owned_by_pointer = {
            let mode = open.filter(|_| source.has_non_region_param() || source.has_aliases());
            let owned = self.owns_mode(source, mode);
            self.placed(owned)
        };
        // (Whether the pointer OWNS what it points to, a `Box`, an `Rc`: a
        // `dyn` behind one owns what the value owns from then on. Behind a
        // `&` or a `&mut` the value is only reached through it.)
        let owning = !matches!(source.kind(), ty::Ref(..) | ty::RawPtr(..));
        for (concrete, to, predicates, read_only) in unsize_pairs(tcx, source, target) {
            // (Read open where the value's type OR the `dyn`'s own bounds
            // name a parameter: `&P as &dyn Show<X>` makes a vtable of `P:
            // Show<X>`, which the compiler can make for concrete trait refs
            // only. Review 4 of the review-14 build: the mode was the
            // value's type's alone, and `vtable_entries` was asked of `P:
            // Show<X>`: a compiler panic, at any seal.)
            let open_pair = concrete.has_non_region_param()
                || concrete.has_aliases()
                || predicates.has_non_region_param()
                || predicates.has_aliases();
            let mode = open.filter(|_| open_pair);
            if mode.is_none() && open_pair {
                continue;
            }
            // (Behind `&` all the way: what a `&` to the value can write,
            // `&Cell<App>`; review 14: only a cell ON THE WAY was looked
            // for.)
            let grip = if read_only {
                let lent = self.reach_mode(concrete, mode, true);
                owned_by_pointer | self.placed(lent)
            } else {
                u64::MAX
            };
            let held = match *concrete.kind() {
                // (An upcast: the vtable was made where the first `dyn` was;
                // what it holds is what was handed to it, a `dyn` of a trait
                // of another crate too, on its entry in `trusts`.)
                ty::Dynamic(from, ..) => self.dyn_owns(from.principal_def_id()),
                _ => {
                    let owned = self.owns_mode(concrete, mode);
                    self.placed(owned)
                }
            } & grip;
            let owned = if owning { held } else { 0 };
            // What can be written through the value, owned or not.
            let reached = match *concrete.kind() {
                ty::Dynamic(from, ..) => match from.principal_def_id() {
                    Some(from) if from.is_local() => {
                        self.erased_reach.get(&from).copied().unwrap_or(0)
                    }
                    from => {
                        self.erased_foreign.get(&from).copied().unwrap_or(0) | self.dyn_owns(from)
                    }
                },
                _ => {
                    let reached = self.reach_mode(concrete, mode, read_only);
                    self.placed(reached)
                }
            } | held;
            let principal = predicates.principal_def_id();
            let held = match principal {
                Some(principal) if self.third_party(principal) => reached,
                Some(principal) if principal.is_local() => held,
                _ if in_third => reached,
                _ => held,
            };
            out.push(Erasure { concrete, to, predicates, principal, held, reached, owned, mode });
        }
        out
    }

    /// Note what a coercion handed to a `dyn` ([`Self::erasures_of`]): of a
    /// trait of this crate, what the `dyn` owns and reaches from then on; of
    /// another crate's (or of none), what it reaches.
    fn record_erasure(&mut self, erasure: &Erasure<'tcx>) {
        match erasure.principal {
            Some(principal) if principal.is_local() => {
                if erasure.reached != 0 {
                    *self.erased_reach.entry(principal).or_insert(0) |= erasure.reached;
                }
                if erasure.held != 0 {
                    *self.erased.entry(principal).or_insert(0) |= erasure.held;
                }
            }
            principal => {
                if erasure.reached != 0 {
                    *self.erased_foreign.entry(principal).or_insert(0) |= erasure.reached;
                }
                if erasure.owned != 0 {
                    *self.erased_foreign_held.entry(principal).or_insert(0) |= erasure.owned;
                }
            }
        }
    }

    /// The methods a vtable of `trait_ref` holds, for a self type that names
    /// a type parameter of the item `scope` (an open reading): those of the
    /// trait and of each supertrait that a `dyn` can call, as the compiler
    /// lists them (`own_existential_vtable_entries`), each resolved in the
    /// item's typing environment. One whose impl a parameter picks is
    /// [`Self::unresolved`].
    fn vtable_open(
        &mut self,
        work: Work<'tcx>,
        trait_ref: ty::TraitRef<'tcx>,
        span: Span,
        scope: DefId,
    ) {
        let tcx = self.tcx;
        let typing_env = ty::TypingEnv::post_analysis(tcx, scope);
        let trait_ref = tcx
            .try_normalize_erasing_regions(typing_env, ty::Unnormalized::new_wip(trait_ref))
            .unwrap_or(trait_ref);
        let supers: Vec<ty::TraitRef<'tcx>> =
            rustc_type_ir::elaborate::supertraits(tcx, ty::Binder::dummy(trait_ref))
                .map(|super_ref| tcx.instantiate_bound_regions_with_erased(super_ref))
                .collect();
        for super_ref in supers {
            for &method in tcx.own_existential_vtable_entries(super_ref.def_id) {
                let mut fits = true;
                let args = GenericArgs::for_item(tcx, method, |param, _| match param.kind {
                    ty::GenericParamDefKind::Lifetime => tcx.lifetimes.re_erased.into(),
                    _ => match super_ref.args.get(param.index as usize) {
                        Some(arg) => arg,
                        None => {
                            fits = false;
                            tcx.lifetimes.re_erased.into()
                        }
                    },
                });
                if !fits || tcx.instantiate_and_check_impossible_clauses((method, args)) {
                    continue;
                }
                // (A method whose own where-clauses the item's environment
                // does not prove, `fn m(&self) where X: Tr2` of a `dyn Tr<T>`,
                // is in the vtable of each instance where they hold: it is read
                // here, in the item's environment, and what it names that the
                // environment cannot settle is an abstract impl, `resolve`.)
                match self.resolve(work, method, args, Some(scope)) {
                    Resolved::Item(instance) => self.reach(work, instance, span, Handed::Vtable),
                    Resolved::Open => self.unresolved(work, method, args, span, scope),
                    Resolved::None => {}
                }
            }
        }
    }

    // ----- what S1 and S5 say of the crate ---------------------------------

    fn judge_shape(&mut self) {
        let tcx = self.tcx;
        let all = self.all();
        // S5.
        for seal in 0..self.seals.len() {
            let adt = self.seals[seal].adt;
            for field in adt.all_fields() {
                let ty = at_instance(
                    tcx,
                    None,
                    tcx.type_of(field.did).instantiate_identity().skip_norm_wip(),
                );
                if !self.plain(ty) {
                    let site = Site::Shape(format!(
                        "its field `{}` is of type `{ty}`, which is not plain data: a `&` of \
                         it may write it, or its data is shared, or it is written with no \
                         borrow of the field (a `Box`, a pointer, a cell, a lock, a `dyn`)",
                        field.name
                    ));
                    self.fixed(seal, adt.did(), tcx.def_span(field.did), site);
                }
            }
        }
        // S1: a macro-2.0 item is expanded in other crates with this crate's
        // privacy.
        if tcx.features().decl_macro() {
            for seal in 0..self.seals.len() {
                let (did, span) = (self.seals[seal].adt.did(), self.seals[seal].decl.span);
                self.fixed(
                    seal,
                    did,
                    span,
                    Site::Shape(
                        "the crate enables `decl_macro`: a `macro` item names private fields \
                         where it is expanded, in another crate too"
                            .to_owned(),
                    ),
                );
            }
        }
        // Assembly is no code this check reads, and it needs no `unsafe` at
        // the crate's top level: `global_asm!` can name a fn of the crate
        // (`sym`) for the loader to run, or write memory itself.
        let assembly: Vec<LocalDefId> = tcx
            .hir_crate_items(())
            .definitions()
            // (A `clean { }` island is a `GlobalAsm` item to the compiler:
            // not that.)
            .filter(|def| {
                matches!(tcx.def_kind(*def), DefKind::GlobalAsm)
                    && !tcx.trust_def_is_clean_island(def.to_def_id())
            })
            .collect();
        if let Some(first) = assembly.first() {
            for seal in 0..self.seals.len() {
                let did = self.seals[seal].adt.did();
                self.fixed(
                    seal,
                    did,
                    tcx.def_span(*first),
                    Site::Shape(
                        "the crate has a `global_asm!` item: what assembly runs or writes is \
                         not read"
                            .to_owned(),
                    ),
                );
            }
        }
        // S1: a static this crate declares in an `extern` block as `safe`
        // to use is a value no Rust code built, which code outside Rust can
        // write: the author's word again.
        let statics: Vec<LocalDefId> = tcx
            .hir_crate_items(())
            .foreign_items()
            .map(|item| item.owner_id.def_id)
            .filter(|def| {
                matches!(
                    tcx.def_kind(*def),
                    DefKind::Static { safety: rustc_hir::Safety::Safe, .. }
                )
            })
            .collect();
        for def in statics {
            let trusted = self.trusting(def.to_def_id());
            self.trust_used(def.to_def_id());
            for seal in 0..self.seals.len() {
                if trusted & (1 << seal) == 0 {
                    let did = self.seals[seal].adt.did();
                    let site = Site::Shape(format!(
                        "the crate declares `{}` in an `extern` block as `safe` to use: a \
                         value no Rust code built, which code outside Rust can write (on \
                         your word that it is no sealed value and points to none, name it in \
                         the seal's `trusts`: {})",
                        tcx.item_name(def.to_def_id()),
                        self.entry_shown(def.to_def_id()),
                    ));
                    self.fixed(seal, did, tcx.def_span(def), site);
                }
            }
        }
        // S1: an `unsafe impl` for a type that owns a sealed type promises
        // code of another crate something about its bytes.
        let impls: Vec<(DefId, LocalDefId)> = tcx
            .all_local_trait_impls(())
            .iter()
            .flat_map(|(of, impls)| impls.iter().map(move |implementation| (*of, *implementation)))
            .collect();
        for (of, implementation) in impls {
            if !tcx.impl_trait_header(implementation.to_def_id()).safety.is_unsafe() {
                continue;
            }
            if tcx.is_lang_item(of, LangItem::Sync) || tcx.is_diagnostic_item(sym::Send, of) {
                continue;
            }
            // (What `derive(Clone, Copy)` writes for the compiler's own use:
            // of a type that is `Copy`, which no holder of a sealed type is.)
            if crate::def_is_in_sysroot_resident_crate(tcx, of)
                && tcx.item_name(of).as_str() == "TrivialClone"
            {
                continue;
            }
            let self_ty = tcx.type_of(implementation).instantiate_identity().skip_norm_wip();
            // An `unsafe impl` of a trait of ANOTHER crate is the author's
            // word to that crate's `unsafe` code, and what was promised is
            // in the trait's documentation, not in the impl: it can be
            // about the self type, a type argument of the trait, an
            // associated type, or a value the self type only points to
            // (review 14: `unsafe impl Bytes for View<'_>` over a `&mut` of
            // the sealed value; `unsafe impl Wraps<Tok> for Raw`; `type
            // Target = Tok`; a self type that keeps only a `*mut u8`). So
            // no position is read: the seal holds only on a second word,
            // the trait's name in `trusts`.
            if !of.is_local() && !tcx.trait_is_auto(of) {
                let trusted = self.trusting(of);
                self.trusted_at(of, self_ty, trusted);
                for seal in 0..self.seals.len() {
                    if trusted & (1 << seal) == 0 {
                        let did = self.seals[seal].adt.did();
                        let site = Site::Shape(format!(
                            "this is an `unsafe impl` of `{}`, a trait of another crate, for \
                             `{self_ty}`: it promises that crate's `unsafe` code something the \
                             check cannot read, and code of that crate may build or change a \
                             value on the strength of it (on your word that what it promises \
                             lets no code build or change a sealed value, name the trait in the \
                             seal's `trusts`: {})",
                            self.trust_path(of).join("::"),
                            self.entry_shown(of),
                        ));
                        self.fixed(seal, did, tcx.def_span(implementation), site);
                    }
                }
                // (And nothing more is asked of it. What the rule below
                // refuses, an `unsafe impl` for a type that holds one, on the
                // strength of which code of another crate may build or change
                // the value, is what this one already asks a word for, whatever
                // the impl is for: the trait's name in `trusts` is the author's
                // word that what the trait promises lets no code build or
                // change a sealed value, which is the whole of what the impl
                // can lend another crate's code. Every fn of that crate this
                // crate runs at a holder's type is still asked for its own
                // entry (S4b, S4e). Review 4 of the review-14 build: the rule
                // below ran too, and refused `unsafe impl dep::RawOk for App`
                // with the trait trusted and no entry to answer it, where the
                // documented conditions ask the trait's name alone.)
                continue;
            }
            // What the type owns whatever its parameters stand for; and a
            // parameter can stand for a type that owns one unless the impl
            // bounds it by `Copy` (no holder is) or by an unsafe trait that
            // is not an auto trait (a holder meets it only by an `unsafe
            // impl` of this crate, which is judged here like this one).
            // (A projection in it that nothing settles is some impl's to
            // say: it is taken to hold one. `T: Copy` says nothing of
            // `T::Out`.)
            let mut owned = if self_ty.has_non_region_param() {
                self.owns_whatever(self_ty, implementation.to_def_id(), true)
            } else {
                let self_ty = at_instance(tcx, None, self_ty);
                self.owns(self_ty)
            };
            if self_ty.has_aliases() && self_ty.has_non_region_param() {
                owned = all;
            }
            if owned != all && self_ty.has_non_region_param() {
                let bounds = tcx.clauses_of(implementation).instantiate_identity(tcx);
                let unbounded = self_ty.walk().any(|part| {
                    let ty::GenericArgKind::Type(part) = part.kind() else { return false };
                    if !matches!(part.kind(), ty::Param(_)) {
                        return false;
                    }
                    !bounds.clauses.iter().any(|clause| {
                        let clause = clause.skip_norm_wip();
                        let Some(bound) = clause.as_trait_clause() else { return false };
                        let bound = bound.skip_binder();
                        bound.self_ty() == part
                            && rustc_type_ir::elaborate::supertrait_def_ids(tcx, bound.def_id())
                                .any(|supertrait| {
                                    // (Not `Send` or `Sync`: a holder is
                                    // either with no impl written.)
                                    // (Nor an unsafe trait of another
                                    // crate: that crate may implement
                                    // it for every type. Review 14.)
                                    tcx.is_lang_item(supertrait, LangItem::Copy)
                                        || (tcx.trait_def(supertrait).safety.is_unsafe()
                                            && !tcx.trait_is_auto(supertrait)
                                            && supertrait.is_local())
                                })
                    })
                });
                if unbounded {
                    owned = all;
                }
            }
            for seal in 0..self.seals.len() {
                if owned & (1 << seal) != 0 {
                    let did = self.seals[seal].adt.did();
                    let site = Site::Shape(format!(
                        "this is an `unsafe impl` of `{}` for `{self_ty}`, which holds one (or \
                         may: a type parameter of it is bounded neither by `Copy` nor by an \
                         unsafe trait): code of another crate may build or change the value on \
                         the strength of it",
                        tcx.item_name(of)
                    ));
                    self.fixed(seal, did, tcx.def_span(implementation), site);
                }
            }
        }
    }

    // ----- the verdict ------------------------------------------------------

    /// One error per seal that does not hold, with a note at each site; a
    /// note at each seal that does.
    fn report(&mut self) {
        let tcx = self.tcx;
        let name = |def: DefId| item_path(tcx, def)[1..].join("::");
        // (An item of another crate, as `trusts` names it: where it is
        // defined, with its crate's name in front.)
        let far = |def: DefId| self.trust_path(def).join("::");
        // (A body of another crate as a note names it: a fn by its path, the
        // body of an `async fn` by its fn's, a closure by the fn it is in.)
        let what = |def: DefId, of: &str| match self.trust_item(def) {
            Some(item) => format!("`{}`, a fn of {of}", far(item)),
            None if tcx.is_closure_like(def)
                || matches!(tcx.def_kind(def), DefKind::SyntheticCoroutineBody) =>
            {
                format!("a closure (or an `async` block) in `{}`, of {of}", far(def))
            }
            None => format!("`{}`, of {of}", far(def)),
        };
        // (What a `trusts` entry for it would be. `value`: reached as a fn
        // pointer or a vtable's method, which only a trust that names it
        // covers.)
        let remedy = |def: DefId, value: bool| match self.trust_item(def) {
            Some(item) => format!("in `trusts`: {}", self.entry_shown(item)),
            None if matches!(
                tcx.def_kind(def),
                DefKind::Const { .. } | DefKind::AssocConst { .. }
            ) =>
            {
                "a `trusts` entry names no constant, and which impl's constant this is turns on a \
                 type parameter: what its value runs is not read"
                    .to_owned()
            }
            // (Review 3 of the review-14 build: this promised that a trust of
            // the fn that made it covers it, and that fn was trusted.)
            None if value => {
                "no `trusts` entry covers it: an entry names no closure, and one made \
                     a fn pointer or a `dyn` runs wherever that is called, on what its caller \
                     hands it, which the check does not follow, so no trust of the code that \
                     made it covers what its inputs reach"
                    .to_owned()
            }
            None => "a `trusts` entry names no closure: a trust of a fn of its own crate that \
                     runs it covers it"
                .to_owned(),
        };
        // (The word that would cover a site in code of another crate: on the
        // fn the way last named, `Through::cover`.)
        let word = |cover: Option<DefId>| match cover {
            Some(cover) => format!(
                " (on your word that `{}` puts no value over another, and hands none on with \
                 its type hidden, name it in the seal's `trusts`: {})",
                far(cover),
                self.entry_shown(cover)
            ),
            None => String::new(),
        };
        // The first few of a list, and how many more there are.
        let some = |all: &BTreeSet<String>, shown: usize| {
            let mut first: Vec<String> = all.iter().take(shown).cloned().collect();
            if all.len() > shown {
                first.push(format!(
                    "{}{} more",
                    if all.len() >= LISTED { "at least " } else { "" },
                    all.len() - shown
                ));
            }
            and_list(&first)
        };
        // (Whether a body is a static's initializer: it does not run, and is
        // evaluated once.)
        let in_static = |root: DefId| matches!(tcx.def_kind(root), DefKind::Static { .. });
        let found: Vec<&Found<'tcx>> = self.fixed.iter().chain(self.found.iter()).collect();
        for (index, seal) in self.seals.iter().enumerate() {
            let shown = tcx.item_name(seal.adt.did());
            let is = |fns: &[DefId], root: DefId| fns.contains(&root);
            let mut broken: Vec<(Span, String)> = Vec::new();
            let mut foreign = false;
            let mut writes = 0usize;
            let mut builds = 0usize;
            let mut calls = 0usize;
            for found in found.iter().filter(|found| found.seal == index) {
                let root = found.root;
                let at = format!("`{}`", name(root));
                let text = match &found.site {
                    Site::Field { what, refused } => {
                        writes += 1;
                        match refused {
                            None if is(&seal.writers, root) => continue,
                            None => format!(
                                "this {what} a field of `{shown}` in {at}, which is not one \
                                 of its writers"
                            ),
                            Some(why) if is(&seal.writers, root) => format!(
                                "this {what} a field of `{shown}` in its writer {at}, but \
                                 {why}"
                            ),
                            Some(why) => format!(
                                "this {what} a field of `{shown}` in {at}, which is not one \
                                 of its writers (and {why})"
                            ),
                        }
                    }
                    Site::Build { own } => {
                        builds += 1;
                        if is(&seal.makers, root) && *own != Own::Closure && *own != Own::Const {
                            continue;
                        }
                        if is(&seal.makers, root) && *own == Own::Const {
                            // (Review 2 of the review-14 build: this was said
                            // of a closure.)
                            format!(
                                "this builds a `{shown}` in an inline `const` in its maker \
                                 {at}: it is built once, when the program is compiled, and \
                                 each run of the maker copies that one value, which no run of \
                                 a maker built (build it in the maker's own body)"
                            )
                        } else if is(&seal.makers, root) {
                            format!(
                                "this builds a `{shown}` in a closure (or an `async` block) in \
                                 its maker {at}: it can be handed on and run anywhere, any \
                                 number of times"
                            )
                        } else {
                            format!(
                                "this builds a `{shown}` in {at}, which is not one of its makers"
                            )
                        }
                    }
                    Site::Ctor => format!(
                        "this names `{shown}`'s constructor as a fn in {at}: whatever is \
                         handed it can build one"
                    ),
                    // (Review 3 of the review-14 build: said of an inline
                    // `const` in a static's initializer, whose one value the
                    // static already keeps.)
                    Site::Constant { maker, .. } if in_static(root) => format!(
                        "this inline `const` in the static {at} runs `{}`, which makes a \
                         `{shown}` (or may): it is evaluated once, when the program is compiled, \
                         and its one value becomes the static's; but an inline `const` that runs \
                         a maker is refused wherever it is (drop the `const {{ }}`: the static's \
                         own initializer is evaluated once too, and its value is no copy)",
                        name(*maker),
                    ),
                    Site::Constant { maker, holds: true, .. } => format!(
                        "this constant's initializer runs `{}`, which makes a `{shown}` (or \
                         may): each use of the constant, anywhere, is a new value that no \
                         maker built there (keep it in a `static`, or build it where it is \
                         needed)",
                        name(*maker)
                    ),
                    // (Review 2 of the review-14 build: the note said each
                    // use of a `u64` constant is a new sealed value.)
                    Site::Constant { maker, holds: false, ty } => format!(
                        "this constant's initializer runs `{}`, which makes a `{shown}` (or \
                         may), when the program is compiled: the constant's type `{ty}` holds \
                         none, but a constant is judged by what its initializer runs, not by \
                         its type (make the value at run time, in a fn the seal names)",
                        name(*maker)
                    ),
                    Site::Maker { maker, callee, own } => {
                        calls += 1;
                        let allowed = is(&seal.made_by, root) || is(&seal.makers, root);
                        if !callee {
                            format!(
                                "this takes the maker `{}` as a fn value in {at}: whatever is \
                                 handed it can call it",
                                name(*maker)
                            )
                        } else if allowed && *own != Own::Closure && *own != Own::Const {
                            continue;
                        } else if allowed && *own == Own::Const && in_static(root) {
                            format!(
                                "this calls the maker `{}` in an inline `const` in the static \
                                 {at}: the call runs once, when the program is compiled, and its \
                                 value becomes the static's; but an inline `const` that runs a \
                                 maker is refused wherever it is (drop the `const {{ }}` and call \
                                 the maker in the static's own initializer, which runs once too)",
                                name(*maker)
                            )
                        } else if allowed && *own == Own::Const {
                            format!(
                                "this calls the maker `{}` in an inline `const` in {at}: the \
                                 call runs once, when the program is compiled, and each run of \
                                 {at} copies the value it made, which no call at run time made \
                                 (call the maker in the fn's own body)",
                                name(*maker)
                            )
                        } else if is(&seal.makers, root) {
                            format!(
                                "this calls the maker `{}` in a closure in the maker {at}: the \
                                 closure can be handed on and run anywhere",
                                name(*maker)
                            )
                        } else if is(&seal.made_by, root) {
                            // (Review 1 of the review-14 build: `watcher`
                            // handed out `|g| mint(g)`, a fn pointer and a
                            // boxed `dyn Fn`, and a fn the seal does not
                            // name minted with them: `.map(mint)` spelt
                            // another way.)
                            format!(
                                "this calls the maker `{}` in a closure (or an `async` block) in \
                                 {at}: a fn the seal says may call it, but the closure can be \
                                 handed on and run anywhere, by code the seal does not name \
                                 (call the maker in the fn's own body, or in a fn of its own, \
                                 named in `madeBy`, that the closure calls)",
                                name(*maker)
                            )
                        } else {
                            format!(
                                "this calls the maker `{}` in {at}, which is not a fn the seal \
                                 says may",
                                name(*maker)
                            )
                        }
                    }
                    Site::Over { ty, through: None, kept: false, .. } => format!(
                        "this puts a value of type `{ty}`, which holds a `{shown}`, where one \
                         may already be, in {at}"
                    ),
                    Site::Over { ty, through: None, kept: true, .. } => format!(
                        "this gives a value of type `{ty}`, which holds a `{shown}`, to a \
                         place that {at} keeps across an `.await` (or a `yield`): the check \
                         cannot tell the first value of such a place from a second (keep the \
                         value outside, and hand the body a `&mut`)"
                    ),
                    Site::Over { ty, through: Some(through), cover, .. } => {
                        foreign |= cover.is_some();
                        format!(
                            "`{}`, named here in {at}, runs code of another crate that puts a \
                             value of type `{ty}`, which holds a `{shown}`, where one may \
                             already be{}",
                            name(*through),
                            word(*cover),
                        )
                    }
                    Site::Union { ty, through, cover } => {
                        foreign |= through.is_some() && cover.is_some();
                        format!(
                            "{} a field of the union `{ty}`, another field of which holds a \
                             `{shown}`, in {at}{}",
                            match through {
                                None => "this writes".to_owned(),
                                Some(through) => format!(
                                    "`{}`, named here, runs code of another crate that writes",
                                    name(*through)
                                ),
                            },
                            if through.is_some() { word(*cover) } else { String::new() },
                        )
                    }
                    Site::Foreign { def, ty, value } => {
                        foreign = true;
                        format!(
                            "this runs {}, at the type `{ty}`, which holds a `{shown}`, in \
                             {at}: it may put one value over another ({})",
                            what(*def, "another crate"),
                            remedy(*def, *value),
                        )
                    }
                    // (Review 4 of the review-14 build: this was skipped, on
                    // the word that an impl of a trait of this crate is read
                    // where it stands. Review 5: an entry for another crate's
                    // trait item was asked for, and covered this crate's own
                    // impl of it; and the note promised a remedy where the
                    // item is no trait's.)
                    Site::Picked { def, ty } => {
                        let (what, remedy) = match tcx.trait_of_assoc(*def) {
                            Some(of) if of.is_local() => (
                                format!(
                                    "an impl of `{}`, a trait of this crate, that a where-clause \
                                     or a type parameter picks: what runs is an impl of this \
                                     crate read where it stands, at its own parameters, which \
                                     says nothing of `{ty}` (or an impl of a crate that \
                                     instantiates this one)",
                                    name(of)
                                ),
                                "drop a where-clause the compiler does not need, so that it \
                                 picks the impl here and it is read at these types; call it \
                                 through a `dyn` of the trait, whose methods are read where \
                                 the `dyn` is made; or hand it no holder",
                            ),
                            Some(of) => (
                                format!(
                                    "an impl of `{}`, a trait of another crate that this crate \
                                     implements, that a where-clause or a type parameter picks: \
                                     what runs may be this crate's own impl, read where it stands, \
                                     which an entry for the trait's item does not speak for",
                                    far(of)
                                ),
                                "drop a where-clause the compiler does not need, so that it \
                                 picks the impl here and it is read at these types; call it \
                                 through a `dyn` of the trait; or hand it no holder",
                            ),
                            None => (
                                "types the bounds there cannot settle: a projection that a \
                                 bound the item lacks would settle, so which body runs is not \
                                 read"
                                    .to_owned(),
                                "give the item whose body names it the bound that settles the \
                                 projection, or hand it no holder",
                            ),
                        };
                        format!(
                            "this names `{}` at the type `{ty}`, which holds a `{shown}`, in {at}, \
                             where the compiler names no one body for it ({what}): no \
                             `trusts` entry answers it ({remedy})",
                            if def.is_local() { name(*def) } else { far(*def) },
                        )
                    }
                    Site::Works { def, ty, op } => {
                        foreign = true;
                        format!(
                            "this runs {}, which {op} and handles a value of type `{ty}`, \
                             through which a `{shown}` can be written, in {at}: what `unsafe` \
                             code of such a crate does is not read ({})",
                            what(*def, "a crate outside the standard library"),
                            remedy(*def, false),
                        )
                    }
                    Site::Extern { def } => format!(
                        "this names `{}`, which the crate declares in an `extern` block as \
                         `safe` to call, in {at}: it has no body to read, what runs is not \
                         Rust, and what makes it safe is the author's word (on your word \
                         that it neither builds nor changes a `{shown}`, name it in the \
                         seal's `trusts`: {})",
                        name(*def),
                        self.entry_shown(*def)
                    ),
                    Site::Erased { ty, to, through, cover } => {
                        foreign |= through.is_some() && cover.is_some();
                        format!(
                            "{} a value of type `{ty}`, which holds a `{shown}` or points to \
                             one, to a `{to}`, in {at}, behind a pointer that owns it or can \
                             write it: code of other crates can take such a value, and put one \
                             over another, with no type of this crate in sight (hand out a `&`, \
                             or a `dyn` of a trait of this crate; or, on your word that no code \
                             replaces one, name the trait in the seal's `trusts`{}{})",
                            match through {
                                None => "this hands".to_owned(),
                                Some(through) => format!(
                                    "`{}`, named here, runs code of another crate that hands",
                                    name(*through)
                                ),
                            },
                            match *to.kind() {
                                ty::Dynamic(predicates, ..) => predicates
                                    .principal_def_id()
                                    .map_or(String::new(), |principal| {
                                        format!(": {}", self.entry_shown(principal))
                                    }),
                                _ => String::new(),
                            },
                            match (through, cover) {
                                (Some(_), Some(cover)) => format!(
                                    "; or the fn on whose word it is handed on: {}",
                                    self.entry_shown(*cover)
                                ),
                                _ => String::new(),
                            },
                        )
                    }
                    // (Review 2 of the review-14 build: this asked for no
                    // entry, and a trust of the fn this crate named answers
                    // it.)
                    Site::Recast { ty, to, through, cover } => {
                        foreign |= cover.is_some();
                        format!(
                            "`{}`, named here in {at}, runs code of another crate that gives a \
                             pointer of type `{ty}`, to a value that holds a `{shown}`, the type \
                             `{to}`: what it writes through that is not seen{}",
                            name(*through),
                            word(*cover),
                        )
                    }
                    Site::Shape(why) => why.clone(),
                };
                broken.push((found.span, text));
            }
            // (An entry that matched only a constant names nothing, and is
            // said so: review 2 of the review-14 build.)
            let unused: Vec<String> = seal
                .decl
                .trusts
                .iter()
                .enumerate()
                .filter(|(entry, _)| !self.used_trusts.contains(&(index, *entry)))
                .map(|(entry, trusted)| match self.misnamed.get(&(index, entry)) {
                    Some(constant) => format!(
                        "`{trusted}` (it names the constant `{}`: an entry names a fn or a \
                         trait, and a constant runs nothing; what it hands out, a fn pointer \
                         or a closure, runs where it is called and is judged there)",
                        far(*constant)
                    ),
                    None => format!("`{trusted}`"),
                })
                .collect();
            if broken.is_empty() {
                let list = |fns: &[DefId]| {
                    if fns.is_empty() {
                        "no fn".to_owned()
                    } else {
                        and_list(
                            &fns.iter().map(|def| format!("`{}`", name(*def))).collect::<Vec<_>>(),
                        )
                    }
                };
                let mut text = format!(
                    "seal `{}` holds: in safe code a field of a `{shown}` is changed only in \
                     {} ({writes} use(s)), and a `{shown}` is built only in {} ({builds} \
                     expression(s)), called only from {} ({calls} call(s))",
                    seal.decl.name,
                    list(&seal.writers),
                    list(&seal.makers),
                    list(&seal.made_by),
                );
                if seal.writers.is_empty() {
                    text.push_str(
                        ". It has no writer, so its values never change, and where one sits \
                         was not asked",
                    );
                } else {
                    text.push_str(&format!(
                        "; no place that holds one is given a second value ({} body(ies), {} \
                         instance(s) read)",
                        self.bodies, self.instances
                    ));
                }
                let used: Vec<String> = seal
                    .decl
                    .trusts
                    .iter()
                    .enumerate()
                    .filter(|(entry, _)| self.used_trusts.contains(&(index, *entry)))
                    .map(|(entry, trusted)| {
                        // (Which item it named, where it is defined: the
                        // word is about that one.)
                        let item = match self.entry_items.get(&(index, entry)) {
                            Some(named) if named.len() == 1 => named
                                .keys()
                                .next()
                                .map_or(String::new(), |(path, _, _)| format!("`{path}`")),
                            _ => String::new(),
                        };
                        let at = match self.trusted_at.get(&(index, entry)) {
                            Some(at) if !at.is_empty() => format!("at {}", some(at, 4)),
                            _ => String::new(),
                        };
                        match (item.is_empty(), at.is_empty()) {
                            (true, true) => format!("`{trusted}`"),
                            (false, true) => format!("`{trusted}` ({item})"),
                            (true, false) => format!("`{trusted}` ({at})"),
                            (false, false) => format!("`{trusted}` ({item}, {at})"),
                        }
                    })
                    .collect();
                if !used.is_empty() {
                    text.push_str(&format!(
                        ". On the author's word, each of these (a fn of another crate, at \
                         every type it is run at, with what its own crate and the standard \
                         library run beneath it; or a trait of another crate, for every \
                         boxed `dyn` of it and every `unsafe impl` of it here) is handed a \
                         value holding one or a pointer to one, puts no value over another, \
                         and hands none on in a form whose type no longer shows it (a `dyn`, \
                         a raw pointer, a `Waker`): {}",
                        and_list(&used)
                    ));
                }
                // (What is handed to a `dyn` first: review 14 found those
                // crowded out of a list of six by an allocator's casts.)
                let hidden = self.handed_on.get(&index);
                let recast = self.recast_on.get(&index);
                if hidden.is_some() || recast.is_some() {
                    let mut said: Vec<String> = Vec::new();
                    if let Some(hidden) = hidden {
                        said.push(some(hidden, 12));
                    }
                    if let Some(recast) = recast {
                        said.push(format!(
                            "{} pointer(s) given another type, such as {}",
                            if recast.len() >= LISTED {
                                format!("at least {}", recast.len())
                            } else {
                                recast.len().to_string()
                            },
                            some(recast, 2)
                        ));
                    }
                    text.push_str(&format!(
                        ". Beneath those fns a value holding one IS handed on with its type \
                         hidden ({}): that it is not put over another afterwards is part of \
                         the author's word",
                        said.join("; ")
                    ));
                }
                if !unused.is_empty() {
                    text.push_str(&format!(
                        ". Named in `trusts`, and met nowhere at a type holding one (a name \
                         misspelt, or no longer needed): {}",
                        and_list(&unused)
                    ));
                }
                if !seal.absent.is_empty() {
                    text.push_str(&format!(
                        ". Named as a fn that may call a maker, and no fn of this build: {}",
                        and_list(&seal.absent.iter().map(|t| format!("`{t}`")).collect::<Vec<_>>())
                    ));
                }
                if self.cut {
                    text.push_str(
                        ". A type too large to read was taken to hold one (the check erred on \
                         the side of failing)",
                    );
                }
                tcx.dcx().struct_span_note(seal.decl.span, text).emit();
                continue;
            }
            broken.sort_by_key(|(span, text)| (span.lo(), span.hi(), text.clone()));
            broken.dedup();
            // One note for each thing said, at the first place it is said of.
            let mut said: Vec<(Span, String, usize)> = Vec::new();
            for (span, text) in broken.iter() {
                match said.iter_mut().find(|(_, earlier, _)| earlier == text) {
                    Some((_, _, more)) => *more += 1,
                    None => said.push((*span, text.clone(), 0)),
                }
            }
            let mut diag = tcx.dcx().struct_span_err(
                seal.decl.span,
                format!(
                    "seal `{}` on `{shown}` does not hold: {} statement(s) break it",
                    seal.decl.name,
                    broken.len()
                ),
            );
            for (span, text, more) in said.iter().take(24) {
                if *more == 0 {
                    diag.span_note(*span, text.clone());
                } else {
                    diag.span_note(*span, format!("{text} (and at {more} more place(s))"));
                }
            }
            if said.len() > 24 {
                diag.note(format!("and {} more", said.len() - 24));
            }
            if foreign {
                diag.help(
                    "a fn of another crate that is handed a value holding one, and replaces \
                     none, is named in the seal's `trusts` by the end of its path where it \
                     is defined, two parts or more (`Box::new`, `mutex::Mutex::lock`; each \
                     note above gives one that works): the seal then holds on that word, for \
                     the fn and for what its own crate and the standard library run beneath \
                     it",
                );
            }
            if !unused.is_empty() {
                diag.note(format!(
                    "named in `trusts`, and met nowhere at a type holding one (a name \
                     misspelt?): {}",
                    and_list(&unused)
                ));
            }
            if self.cut {
                diag.note(
                    "a type too large to read, or an instance the compiler could not make, was \
                     taken to hold one (the check erred on the side of failing)",
                );
            }
            diag.emit();
        }
    }
}

/// The `(concrete type, dyn type, its predicates, read-only)` an unsizing
/// coercion from `source` to `target` makes: through references, raw
/// pointers and `CoerceUnsized` smart pointers (each field that differs)
/// down to the unsized tail (a struct's last field, a tuple's last element).
/// READ-ONLY: every pointer on the way is a `&`, and no `UnsafeCell` lies
/// between it and the value (`&App`, not `&mut App`, not `&RefCell<App>`).
/// A raw pointer never is: a `*const` made from a `*mut` writes once it is
/// cast back (review 14).
fn unsize_pairs<'tcx>(
    tcx: TyCtxt<'tcx>,
    source: Ty<'tcx>,
    target: Ty<'tcx>,
) -> Vec<(Ty<'tcx>, Ty<'tcx>, &'tcx ty::List<ty::PolyExistentialPredicate<'tcx>>, bool)> {
    let typing_env = ty::TypingEnv::fully_monomorphized();
    let mut out = Vec::new();
    // (source, target, behind a pointer already, read-only so far)
    let mut stack = vec![(source, target, false, true)];
    let mut seen: FxHashSet<(Ty<'tcx>, Ty<'tcx>, bool, bool)> = FxHashSet::default();
    while let Some((source, target, pointee, read_only)) = stack.pop() {
        let source = normalize(tcx, typing_env, source).unwrap_or(source);
        let target = normalize(tcx, typing_env, target).unwrap_or(target);
        if source == target || !seen.insert((source, target, pointee, read_only)) {
            continue;
        }
        if let (true, ty::Dynamic(predicates, ..)) = (pointee, *target.kind()) {
            out.push((source, target, predicates, read_only));
            continue;
        }
        match (*source.kind(), *target.kind()) {
            (ty::Ref(_, s, mutability), ty::Ref(_, t, _) | ty::RawPtr(t, _)) if !pointee => {
                stack.push((s, t, true, read_only && mutability.is_not()))
            }
            (ty::RawPtr(s, _), ty::RawPtr(t, _)) if !pointee => stack.push((s, t, true, false)),
            (ty::Pat(s, _), ty::Pat(t, _)) => stack.push((s, t, pointee, read_only)),
            (ty::Tuple(s), ty::Tuple(t)) if pointee && s.len() == t.len() => {
                if let (Some(&s), Some(&t)) = (s.last(), t.last()) {
                    stack.push((s, t, true, read_only));
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
                            read_only && !source_adt.is_unsafe_cell(),
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
                            read_only,
                        ));
                    }
                }
            }
            _ => {}
        }
    }
    out
}

/// A set of a body's watched locals.
#[derive(Clone, PartialEq, Eq)]
struct Locals(Vec<u64>);

impl Locals {
    fn none(watched: usize) -> Self {
        Locals(vec![0; watched.div_ceil(64)])
    }
    fn set(&mut self, index: usize, to: bool) {
        let (word, bit) = (index / 64, 1u64 << (index % 64));
        if to {
            self.0[word] |= bit;
        } else {
            self.0[word] &= !bit;
        }
    }
    fn has(&self, index: usize) -> bool {
        self.0[index / 64] & (1 << (index % 64)) != 0
    }
    /// Add `other`'s; whether any was new.
    fn join(&mut self, other: &Locals) -> bool {
        let mut grew = false;
        for (mine, theirs) in self.0.iter_mut().zip(&other.0) {
            let joined = *mine | *theirs;
            grew |= joined != *mine;
            *mine = joined;
        }
        grew
    }
}

/// For each block, the watched locals that MAY have been assigned since
/// their storage began, at the block's start (S4a). Forward, join by union;
/// an assignment to a local or to any part of it sets it, `StorageLive` and
/// `StorageDead` clear it, a move out does not. Arguments start assigned.
fn assigned_since_live<'tcx>(
    body: &mir::Body<'tcx>,
    watched: &FxHashMap<mir::Local, usize>,
) -> Vec<Locals> {
    let blocks = body.basic_blocks.len();
    let mut at_start: Vec<Locals> = vec![Locals::none(watched.len()); blocks];
    if watched.is_empty() {
        return at_start;
    }
    for arg in body.args_iter() {
        if let Some(&index) = watched.get(&arg) {
            at_start[mir::START_BLOCK.as_usize()].set(index, true);
        }
    }
    let mut work: Vec<mir::BasicBlock> = body.basic_blocks.indices().collect();
    work.reverse();
    let mut queued = vec![true; blocks];
    while let Some(block) = work.pop() {
        queued[block.as_usize()] = false;
        let mut state = at_start[block.as_usize()].clone();
        let data = &body.basic_blocks[block];
        for statement in &data.statements {
            step_statement(statement, watched, &mut state);
        }
        if let Some(terminator) = &data.terminator {
            step_terminator(terminator, watched, &mut state);
            for successor in terminator.successors() {
                if at_start[successor.as_usize()].join(&state) && !queued[successor.as_usize()] {
                    queued[successor.as_usize()] = true;
                    work.push(successor);
                }
            }
        }
    }
    at_start
}

fn step_statement<'tcx>(
    statement: &mir::Statement<'tcx>,
    watched: &FxHashMap<mir::Local, usize>,
    state: &mut Locals,
) {
    let mut set = |local: mir::Local, to: bool| {
        if let Some(&index) = watched.get(&local) {
            state.set(index, to);
        }
    };
    match &statement.kind {
        mir::StatementKind::Assign(assign) => set(assign.0.local, true),
        mir::StatementKind::SetDiscriminant { place, .. } => set(place.local, true),
        mir::StatementKind::StorageLive(local) | mir::StatementKind::StorageDead(local) => {
            set(*local, false)
        }
        _ => {}
    }
}

fn step_terminator<'tcx>(
    terminator: &mir::Terminator<'tcx>,
    watched: &FxHashMap<mir::Local, usize>,
    state: &mut Locals,
) {
    let mut set = |local: mir::Local| {
        if let Some(&index) = watched.get(&local) {
            state.set(index, true);
        }
    };
    match &terminator.kind {
        TerminatorKind::Call { destination, .. } => set(destination.local),
        TerminatorKind::Yield { resume_arg, .. } => set(resume_arg.local),
        TerminatorKind::InlineAsm { operands, .. } => {
            for operand in operands.iter() {
                match operand {
                    mir::InlineAsmOperand::Out { place: Some(place), .. }
                    | mir::InlineAsmOperand::InOut { out_place: Some(place), .. } => {
                        set(place.local)
                    }
                    _ => {}
                }
            }
        }
        _ => {}
    }
}

/// For each source scope of a body: the fns the code in it was inlined
/// through, outermost first (none: the body's own code). The code of a scope
/// is that of the innermost fn inlined around it ([`Checker::crate_code`]).
fn inline_chains<'tcx>(tcx: TyCtxt<'tcx>, body: &mir::Body<'tcx>) -> Vec<Rc<[ty::Instance<'tcx>]>> {
    let empty: Rc<[ty::Instance<'tcx>]> = Rc::from(Vec::new());
    let mut chains: Vec<Rc<[ty::Instance<'tcx>]>> = Vec::with_capacity(body.source_scopes.len());
    for data in body.source_scopes.iter() {
        let mut start = if data.inlined.is_some() { Some(data) } else { None };
        if start.is_none() {
            start = data.inlined_parent_scope.map(|parent| &body.source_scopes[parent]);
        }
        let mut chain = Vec::new();
        while let Some(at) = start {
            if let Some((callee, _)) = at.inlined {
                chain.push(tcx.erase_and_anonymize_regions(callee));
            }
            start = at.inlined_parent_scope.map(|parent| &body.source_scopes[parent]);
            if chain.len() > 64 {
                break;
            }
        }
        if chain.is_empty() {
            chains.push(empty.clone());
        } else {
            chain.reverse();
            chains.push(chain.into());
        }
    }
    chains
}

/// One body, read statement by statement.
struct Reader<'r, 'a, 'tcx> {
    checker: &'r mut Checker<'a, 'tcx>,
    body: &'r mir::Body<'tcx>,
    /// A body of this crate: what S2, S3 and S3' ask is asked of it.
    local: bool,
    /// A body of a crate outside the standard library (S4e),
    third: bool,
    /// and the first thing in it that only `unsafe` code can do.
    unsafe_op: Option<&'static str>,
    /// In such a body, by source scope: whether what only `unsafe` code
    /// can do, done there, counts as that crate's ([`Checker::crate_code`]);
    /// and the same for the body's own code (a scope with no fn inlined
    /// around it).
    crate_code: Vec<bool>,
    own_code: bool,
    /// In a body of another crate, by source scope: what the code there was
    /// inlined through ([`inline_chains`]), and the chain the last
    /// [`Fact::At`] said (an index of a scope with that chain).
    chains: Option<Vec<Rc<[ty::Instance<'tcx>]>>>,
    chain_said: Option<Rc<[ty::Instance<'tcx>]>>,
    root: DefId,
    /// Whether the body is the root fn's own, or a closure's in it.
    own: Own,
    /// A coroutine's body, in its state-machine form.
    coroutine: bool,
    /// The root's `&mut` parameters with a lifetime of their own (S2).
    fresh: Rc<[mir::Local]>,
    watched: FxHashMap<mir::Local, usize>,
    assigned: Vec<Locals>,
    /// The watched locals that may have been assigned, at the statement
    /// being read.
    now: Locals,
    facts: &'r mut Vec<Fact<'tcx>>,
}

impl<'r, 'a, 'tcx> Reader<'r, 'a, 'tcx> {
    fn span(&self, location: Location) -> Span {
        self.body.source_info(location).span
    }

    fn erased(&self, ty: Ty<'tcx>) -> Ty<'tcx> {
        self.checker.tcx.erase_and_anonymize_regions(ty)
    }

    /// Record what the statement at `location` does at its instance. In a
    /// body of another crate, what the code it is in was inlined through is
    /// said first ([`Fact::At`]) for a fact that is reached beneath it.
    fn fact(&mut self, location: Location, fact: Fact<'tcx>) {
        let beneath = matches!(
            fact,
            Fact::Fn { .. }
                | Fact::Drop { .. }
                | Fact::Unsize { .. }
                | Fact::Closure { .. }
                | Fact::Const { .. }
        );
        if let (true, Some(chains)) = (beneath, &self.chains) {
            let scope = self.body.source_info(location).scope.as_usize();
            if let Some(chain) = chains.get(scope) {
                let said = self.chain_said.as_ref().is_some_and(|said| **said == **chain);
                if !said {
                    let chain = chain.clone();
                    self.chain_said = Some(chain.clone());
                    self.facts.push(Fact::At { outer: chain });
                }
            }
        }
        self.facts.push(fact);
    }

    /// S4e, in a body of a crate outside the standard library: something
    /// only `unsafe` code can do, or that makes a pointer whose type no
    /// longer says what it points to. The whole list: a dereference of a
    /// raw pointer; a pointer cast to another pointee, a transmute, an
    /// address made a number or a number made an address; the address of a
    /// part of a value taken as a raw pointer; raw pointer arithmetic; a
    /// field of a union; a raw copy; assembly; a call of an `unsafe fn` or
    /// of a fn with no Rust body. A body with none of these acts through
    /// the references it is handed, by operations the compiler types.
    ///
    /// Not a statement of the STANDARD LIBRARY's code that the optimizer
    /// inlined here: that is std's, read by its shape as it is when the body
    /// calls the std fn instead (a build without optimization), and the call
    /// that brought it here is asked about itself (`unsafe_calls_inlined`).
    /// (Review 1 of the review-14 build: `v.iter().count()` in a crate that
    /// forbids `unsafe` was refused for the pointer cast of std's
    /// `slice::iter`.) Not a statement of a fn whose source has no user
    /// `unsafe` ([`Checker::crate_code`]).
    fn only_unsafe(&mut self, location: Location, what: &'static str) {
        if !self.third || self.unsafe_op.is_some() {
            return;
        }
        let info = self.body.source_info(location);
        let counts = self.crate_code.get(info.scope.as_usize()).copied().unwrap_or(self.own_code);
        if counts && !self.checker.compiler_written(info.span) {
            self.unsafe_op = Some(what);
        }
    }

    /// S4e, in an optimized body of a crate outside the standard library: a
    /// call the optimizer inlined away, made by the crate's own code (the
    /// body's, or a fn of a crate outside the standard library inlined into
    /// it), of an `unsafe fn`, or of a drop's glue (which an explicit
    /// `ptr::drop_in_place` and a plain drop both become). Where the call
    /// stood, the body did what only `unsafe` code can: the statements it
    /// left are std's ([`Self::only_unsafe`]), but calling it was the
    /// crate's.
    fn unsafe_calls_inlined(&mut self) -> Option<&'static str> {
        let tcx = self.checker.tcx;
        for data in self.body.source_scopes.iter() {
            let Some((callee, call)) = data.inlined else { continue };
            // (The code where it was called: the body's own, or that of the
            // inlined fn the call stood in; and not a macro of std's.)
            let by_crate = match data.inlined_parent_scope {
                None => self.own_code,
                Some(parent) => self.crate_code.get(parent.as_usize()).copied().unwrap_or(false),
            };
            if !by_crate || self.checker.std_macro(call) {
                continue;
            }
            let unchecked = match callee.def {
                InstanceKind::Item(def) | InstanceKind::Intrinsic(def) => {
                    matches!(tcx.def_kind(def), DefKind::Fn | DefKind::AssocFn)
                        && (tcx.is_foreign_item(def)
                            || tcx.fn_sig(def).skip_binder().safety().is_unsafe())
                }
                InstanceKind::Shim(ShimKind::DropGlue(..)) => true,
                _ => false,
            };
            if unchecked {
                return Some("calls an `unsafe fn`, or a fn with no Rust body");
            }
        }
        None
    }

    /// S4a for a write of the whole of `place`.
    fn stored(&mut self, place: &mir::Place<'tcx>, location: Location) {
        let ty = self.erased(place.ty(self.body, self.checker.tcx).ty);
        if owns_nothing(ty) {
            return;
        }
        // A bare local not assigned since its storage began is given its
        // first value.
        let first = place.projection.is_empty()
            && self.watched.get(&place.local).is_some_and(|&index| !self.now.has(index));
        if !first {
            // What a coroutine keeps across a suspension is a field of its
            // state (reached through its first argument, or a copy of the
            // pointer in it), written like any other field: its first value
            // cannot be told from a second.
            let tcx = self.checker.tcx;
            let kept = self.coroutine
                && place
                    .iter_projections()
                    .any(|(base, _)| base.ty(self.body, tcx).ty.is_coroutine());
            self.fact(location, Fact::Store { ty, kept, span: self.span(location) });
        }
    }

    /// A fn item named at `location` (written at `span`): its callee, or a
    /// value.
    fn mention(&mut self, ty: Ty<'tcx>, location: Location, span: Span, callee: bool) {
        let ty = self.erased(ty);
        let ty::FnDef(def, _) = *ty.kind() else { return };
        self.fact(location, Fact::Fn { ty, called: callee, span });
        if !self.local {
            return;
        }
        let tcx = self.checker.tcx;
        // S3: the sealed type's constructor fn.
        if let DefKind::Ctor(..) = tcx.def_kind(def) {
            let of = tcx.parent(def);
            let of = if matches!(tcx.def_kind(of), DefKind::Variant) { tcx.parent(of) } else { of };
            if let Some(seal) = self.checker.sealed(of) {
                self.checker.fixed(seal, self.root, span, Site::Ctor);
            }
        }
        // S3': a maker.
        for seal in 0..self.checker.seals.len() {
            if self.checker.seals[seal].makers.contains(&def) {
                let site = Site::Maker { maker: def, callee, own: self.own };
                self.checker.fixed(seal, self.root, span, site);
            }
        }
    }

    /// The callee of a call: a fn item, by the TYPE of what is called. (A
    /// fn item is a value of no size: where it was named may be gone from
    /// an optimized body, and its type is all that is left.)
    fn callee(&mut self, func: &mir::Operand<'tcx>, location: Location) {
        if self.third {
            let tcx = self.checker.tcx;
            let ty = func.ty(self.body, tcx);
            let unchecked = match *ty.kind() {
                ty::FnDef(def, _) => {
                    tcx.is_foreign_item(def) || tcx.fn_sig(def).skip_binder().safety().is_unsafe()
                }
                ty::FnPtr(..) => ty.fn_sig(tcx).safety().is_unsafe(),
                _ => false,
            };
            // (A call a macro of std wrote, `pin!`'s `Pin::new_unchecked` of
            // its own local, is std's: `Checker::std_macro`. Only a call: a
            // place a macro of std names, `addr_of_mut!((*p).f)`, is the
            // author's to have made.)
            if unchecked && !self.checker.std_macro(self.span(location)) {
                self.only_unsafe(location, "calls an `unsafe fn`, or a fn with no Rust body");
            }
        }
        match func {
            mir::Operand::Constant(constant) => {
                self.mention(constant.const_.ty(), location, constant.span, true)
            }
            _ => {
                let ty = self.erased(func.ty(self.body, self.checker.tcx));
                if matches!(ty.kind(), ty::FnDef(..)) {
                    self.fact(location, Fact::Fn { ty, called: true, span: self.span(location) });
                }
                self.visit_operand(func, location);
            }
        }
    }
}

impl<'r, 'a, 'tcx> Visitor<'tcx> for Reader<'r, 'a, 'tcx> {
    fn visit_basic_block_data(&mut self, block: mir::BasicBlock, data: &mir::BasicBlockData<'tcx>) {
        self.now = self.assigned[block.as_usize()].clone();
        self.super_basic_block_data(block, data);
    }

    fn visit_statement(&mut self, statement: &mir::Statement<'tcx>, location: Location) {
        // A raw copy: whole values written through a pointer. (An optimized
        // body of another crate keeps `ptr::copy_nonoverlapping` as a
        // statement once the call is inlined: no assignment, and no call.)
        if let mir::StatementKind::Intrinsic(intrinsic) = &statement.kind {
            if let mir::NonDivergingIntrinsic::CopyNonOverlapping(copy) = &**intrinsic {
                self.only_unsafe(location, "copies raw memory");
                let pointer = copy.dst.ty(self.body, self.checker.tcx);
                if let Some(pointee) = pointer.builtin_deref(true) {
                    let ty = self.erased(pointee);
                    if !owns_nothing(ty) {
                        let span = self.span(location);
                        self.fact(location, Fact::Store { ty, kept: false, span });
                    }
                }
            }
        }
        self.super_statement(statement, location);
        step_statement(statement, &self.watched, &mut self.now);
    }

    fn visit_terminator(&mut self, terminator: &mir::Terminator<'tcx>, location: Location) {
        match &terminator.kind {
            // The callee of a direct call is a mention of its own kind.
            TerminatorKind::Call { func, args, destination, .. } => {
                self.callee(func, location);
                for arg in args.iter() {
                    self.visit_operand(&arg.node, location);
                }
                self.visit_place(
                    destination,
                    PlaceContext::MutatingUse(MutatingUseContext::Call),
                    location,
                );
            }
            TerminatorKind::TailCall { func, args, .. } => {
                self.callee(func, location);
                for arg in args.iter() {
                    self.visit_operand(&arg.node, location);
                }
            }
            TerminatorKind::Drop { place, .. } => {
                let ty = self.erased(place.ty(self.body, self.checker.tcx).ty);
                if !owns_nothing(ty) {
                    self.fact(location, Fact::Drop { ty, span: self.span(location) });
                }
                self.super_terminator(terminator, location);
            }
            TerminatorKind::InlineAsm { .. } => {
                self.only_unsafe(location, "runs assembly");
                self.super_terminator(terminator, location);
            }
            _ => self.super_terminator(terminator, location),
        }
        step_terminator(terminator, &self.watched, &mut self.now);
    }

    fn visit_const_operand(&mut self, constant: &mir::ConstOperand<'tcx>, location: Location) {
        // (Where the constant is written, not where the statement it is in
        // starts: the body's required constants are visited at its first
        // statement. Review 2 of the review-14 build: a note was laid to a
        // `let` two lines above the use.)
        let ty = constant.const_.ty();
        if matches!(ty.kind(), ty::FnDef(..)) {
            // A fn item used as a value.
            self.mention(ty, location, constant.span, false);
            return;
        }
        // A `const` item's value (not a promoted constant of this body,
        // which is read with it; one another body promoted, which an
        // optimized body of another crate may name, is the collector's to
        // read). A constant that is CALLED comes by here too: the visitor
        // walks the body's required constants.
        if let mir::Const::Unevaluated(unevaluated, _) = constant.const_ {
            if unevaluated.promoted.is_none() {
                let args = self.checker.tcx.erase_and_anonymize_regions(unevaluated.args);
                let fact = Fact::Const { def: unevaluated.def, args, span: constant.span };
                self.fact(location, fact);
            }
        }
    }

    fn visit_rvalue(&mut self, rvalue: &mir::Rvalue<'tcx>, location: Location) {
        let tcx = self.checker.tcx;
        if self.third {
            match rvalue {
                mir::Rvalue::Cast(kind, operand, target) => {
                    let retyped = match kind {
                        mir::CastKind::Transmute
                        | mir::CastKind::BoxDerefTransmute
                        | mir::CastKind::PointerExposeProvenance
                        | mir::CastKind::PointerWithExposedProvenance
                        | mir::CastKind::FnPtrToPtr => true,
                        mir::CastKind::PtrToPtr => {
                            let source = operand.ty(self.body, tcx);
                            source.builtin_deref(true) != target.builtin_deref(true)
                        }
                        _ => false,
                    };
                    if retyped {
                        self.only_unsafe(location, "gives a pointer, or a value, another type");
                    }
                }
                mir::Rvalue::RawPtr(_, place)
                    if place
                        .projection
                        .iter()
                        .any(|elem| !matches!(elem, mir::ProjectionElem::Deref)) =>
                {
                    self.only_unsafe(location, "takes a raw pointer to a part of a value");
                }
                mir::Rvalue::BinaryOp(mir::BinOp::Offset, _) => {
                    self.only_unsafe(location, "moves a raw pointer");
                }
                _ => {}
            }
        }
        match rvalue {
            mir::Rvalue::Aggregate(kind, _) => match **kind {
                mir::AggregateKind::Adt(def, ..) => {
                    if self.local {
                        if let Some(seal) = self.checker.sealed(def) {
                            let span = self.span(location);
                            let site = Site::Build { own: self.own };
                            self.checker.fixed(seal, self.root, span, site);
                        }
                    }
                }
                // (A closure or a coroutine MADE is no use of its body: it
                // runs where it is called or polled, which names it, as the
                // compiler has it. What its body says whatever its
                // parameters stand for is read where it stands.)
                _ => {}
            },
            mir::Rvalue::Cast(
                mir::CastKind::PointerCoercion(PointerCoercion::Unsize, _),
                operand,
                target,
            ) => {
                let source = self.erased(operand.ty(self.body, tcx));
                let target = self.erased(*target);
                self.fact(location, Fact::Unsize { source, target, span: self.span(location) });
            }
            // In a body of another crate (where `unsafe` is within the
            // claim): a pointer given another type.
            mir::Rvalue::Cast(
                mir::CastKind::PtrToPtr
                | mir::CastKind::Transmute
                | mir::CastKind::PointerExposeProvenance,
                operand,
                target,
            ) if !self.local => {
                let source = self.erased(operand.ty(self.body, tcx));
                let target = self.erased(*target);
                if source != target {
                    self.fact(location, Fact::Recast { source, target, span: self.span(location) });
                }
            }
            // A closure made a fn pointer runs like any fn made one.
            mir::Rvalue::Cast(
                mir::CastKind::PointerCoercion(PointerCoercion::ClosureFnPointer(_), _),
                operand,
                _,
            ) => {
                let ty = self.erased(operand.ty(self.body, tcx));
                self.fact(location, Fact::Closure { ty, span: self.span(location) });
            }
            _ => {}
        }
        self.super_rvalue(rvalue, location);
    }

    fn visit_place(&mut self, place: &mir::Place<'tcx>, context: PlaceContext, location: Location) {
        let tcx = self.checker.tcx;
        if self.third && !matches!(context, PlaceContext::NonUse(_)) {
            for (base, elem) in place.iter_projections() {
                let base = base.ty(self.body, tcx).ty;
                match elem {
                    mir::ProjectionElem::Deref if base.is_raw_ptr() => {
                        self.only_unsafe(location, "reads or writes through a raw pointer")
                    }
                    mir::ProjectionElem::Field(..) if base.is_union() => {
                        self.only_unsafe(location, "reads or writes a field of a union")
                    }
                    _ => {}
                }
            }
        }
        // The whole place written (S4a).
        let written = matches!(
            context,
            PlaceContext::MutatingUse(
                MutatingUseContext::Store
                    | MutatingUseContext::Call
                    | MutatingUseContext::Yield
                    | MutatingUseContext::AsmOutput
                    | MutatingUseContext::SetDiscriminant
            )
        );
        // (A coroutine's own state is no variant of a value: the number of
        // the suspension it is at, which its state machine sets.)
        let state =
            matches!(context, PlaceContext::MutatingUse(MutatingUseContext::SetDiscriminant))
                && place.ty(self.body, tcx).ty.is_coroutine();
        if written && !state {
            self.stored(place, location);
        }
        let raw = matches!(
            context,
            PlaceContext::MutatingUse(MutatingUseContext::RawBorrow)
                | PlaceContext::NonMutatingUse(NonMutatingUseContext::RawBorrow)
        );
        let mutable = written
            || raw
            || matches!(context, PlaceContext::MutatingUse(MutatingUseContext::Borrow));
        let moved = matches!(context, PlaceContext::NonMutatingUse(NonMutatingUseContext::Move));
        if !mutable && !moved {
            return;
        }
        let what = match context {
            PlaceContext::MutatingUse(MutatingUseContext::Borrow) => "takes a `&mut` of",
            _ if raw => "takes a raw pointer to",
            PlaceContext::NonMutatingUse(NonMutatingUseContext::Move) => "moves out of",
            _ => "writes",
        };
        let first_is_deref = matches!(place.projection.first(), Some(mir::ProjectionElem::Deref));
        let mut derefs = 0usize;
        for (base, elem) in place.iter_projections() {
            match elem {
                mir::ProjectionElem::Deref => derefs += 1,
                mir::ProjectionElem::Field(field, _) => {
                    let base_ty = base.ty(self.body, tcx).ty;
                    let ty::Adt(adt, _) = *base_ty.kind() else { continue };
                    // A union's fields share their bytes (S4a). (In this
                    // crate's bodies: what another crate does with a union
                    // of its own, behind its own `unsafe`, is not judged.)
                    if adt.is_union() && mutable && self.local {
                        self.facts.push(Fact::Union {
                            ty: self.erased(base_ty),
                            field: field.as_usize(),
                            span: self.span(location),
                        });
                    }
                    if !self.local {
                        continue;
                    }
                    // S2: through a field of a sealed type. (Of each one the
                    // place goes through.)
                    let Some(seal) = self.checker.sealed(adt.did()) else { continue };
                    // Moving a field out of a value the body owns ends that
                    // value: nothing anyone can see changes.
                    if moved && derefs == 0 {
                        continue;
                    }
                    let refused = if raw {
                        Some("a raw pointer to a sealed field is made nowhere")
                    } else if self.own == Own::Const {
                        Some(
                            "it is in an inline `const`, evaluated once when the program is \
                             compiled, and its value copied at each run: no writer runs there",
                        )
                    } else if self.own != Own::Body {
                        Some(
                            "it is in a closure (or an `async` body), which can be handed on \
                             and run when the writer is not",
                        )
                    } else if derefs == 0
                        || (derefs == 1 && first_is_deref && self.fresh.contains(&place.local))
                    {
                        None
                    } else {
                        Some(
                            "the place does not start at a `&mut` parameter whose lifetime is \
                             named nowhere else in the fn's signature, nor at a value the \
                             body owns: a borrow made here could be kept past the call",
                        )
                    };
                    let span = self.span(location);
                    self.checker.fixed(seal, self.root, span, Site::Field { what, refused });
                }
                _ => {}
            }
        }
    }
}
