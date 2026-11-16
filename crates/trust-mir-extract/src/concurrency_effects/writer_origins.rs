// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: MIT OR Apache-2.0

//! The writer census's pointer origins: one analysis per body, read at an
//! instance, that says for every local what the pointers in it may point to,
//! and from that every site that may write a bound field
//! ([`scan_writes`]: what [`super::written_fields`] reports).
//!
//! # The claim
//!
//! Let W be a write, at run time, of memory inside the bound field of a value
//! a message consumer runs on. Then one of these is a site:
//!
//! * (S1) the assignment or call destination, in a body of this crate, that
//!   performs W;
//! * (S2) a place in a body of this crate where a pointer, from which the
//!   pointer W writes through was derived, LEFT the code the census reads
//!   with full knowledge of it: was handed to a call, stored in memory or
//!   returned;
//! * (S3) the assignment that gives a variable holding a consumer's value a
//!   whole new one.
//!
//! Not claimed (each is listed in `docs/USING_TRUST.md`): pointers laundered
//! through integers, or moved by arithmetic from outside the field onto it
//! or past what a pointer's type says it points to; another crate's generic
//! code where [`super::writes_through`] loses the pointer; async consumers; a
//! generic `self`'s uninstantiated writes; a pointer kept inside the
//! consumer's own value that points back into it; a consumer's value moved or
//! overwritten by the std collection that owns it; unsafe copies through a
//! `&` of a value that keeps a `&mut`.
//!
//! The claim was attacked on paper before the module was written (51 issues),
//! its first build was reviewed by reproduction (42 more, 22 of them
//! bindings that held falsely), and a recheck of the fixed build found 30
//! more. The count did not fall while anything here was INFERRED. So the
//! rules that decide soundness infer nothing:
//!
//! * which values are a consumer's is decided by TYPE, with no exemption
//!   ([`super::owned_locals`]): every value of the consumer's type, or of a
//!   type that holds it by value, wherever it is;
//! * what a pointer can do is read off its type in one place
//!   ([`Frame::view_writes`], [`Frame::takes`], [`Frame::carries`],
//!   [`Frame::stores`], [`Frame::has_inside`]), each walk answering yes
//!   when in doubt;
//! * a std fn handed a pointer to a value that may hold the field is a site
//!   unless it is one of the accessors [`super::std_passes_on`] NAMES; and a
//!   call the census cannot resolve is a site when any fn not the crate's
//!   own is used as a value with a matching argument ([`scan_writes`]).
//!
//! What is left of precision (a pointer that is provably the body's own, a
//! sibling by the path, what a std accessor hands back) can refuse a true
//! binding when it is wrong about a type; the three rules above cannot pass
//! a false one by being wrong, since each only ever adds sites.
//!
//! # The domain
//!
//! Every local has two [`Origin`]s ([`Val`]): `p`, what it points to when it
//! is a reference, a raw pointer or a `Box`; and `i`, the pointers INSIDE its
//! value (a tuple, a struct, an `Option`, a closure the census does not read;
//! for a `Box`, inside what it holds), field-insensitively. An origin is a
//! set of facts, joined by union over every assignment of the local, to the
//! fixpoint, with no regard for order:
//!
//! * `whole` / `part`: it may point to the bound field, or to part of it
//!   (also to the value of a `Box` in the field);
//! * `lent`: it is of unknown origin, or points to a value that may hold the
//!   field: what a place through it is, is JUDGED where it is used, by the
//!   path and the type of the place ([`super::overlap`]);
//! * `reaching`: it may point to a value that holds the field (borrowed from
//!   one, or of unknown origin and of a type that can): handing it to code
//!   the census does not read is a site;
//! * `recast`: `reaching`, and cast to another pointee type, so that no type
//!   says what a write through it is;
//! * `outside`: it may point into memory the body does not own that no path
//!   says is beside the field;
//! * `slots`: the storage it may point into, of a local of this body or of
//!   the value a local `Box` holds. A pointer to an `R` points INTO a
//!   variable only where the variable's type has an `R` in it
//!   ([`Frame::has_inside`]): a guard holds none of what it names.
//!
//! No fact is APART: provably the body's own value, a sibling's, or no
//! pointer. A pointer is apart only when every assignment of it is.
//!
//! Unknown origins are judged by TYPE: a parameter, a call's result, a
//! constant, what is read out of memory or out of a value of the consumer's
//! type. A `&` with which nothing is written, and out of which no pointer
//! that writes can be copied, is no pointer to follow at all. A closure of
//! the crate reads what its captures are off its PARENT's solution at the
//! same instance ([`Solved::closures`]), so the two cannot disagree.

use super::*;

/// The storage a pointer may point into.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
enum Slot {
    /// The variable itself.
    Local(mir::Local),
    /// What a `Box` in the variable holds.
    Boxed(mir::Local),
}

impl Slot {
    fn local(self) -> mir::Local {
        match self {
            Slot::Local(local) | Slot::Boxed(local) => local,
        }
    }
}

/// What a pointer, or the pointers in a value, may point to (module docs).
#[derive(Clone, Default, PartialEq, Eq, Debug)]
pub(super) struct Origin {
    whole: bool,
    part: bool,
    lent: bool,
    reaching: bool,
    recast: bool,
    /// It may point into memory the body does not own and that no PATH says
    /// is beside the field (a place where no type matched): what std hands
    /// back from there is judged by type.
    outside: bool,
    slots: Vec<Slot>,
}

impl Origin {
    /// To the bound field or part of it.
    fn field(&self) -> bool {
        self.whole || self.part
    }

    /// Any fact but the slots: it may point outside the body's own storage.
    fn facts(&self) -> bool {
        self.field() || self.lent || self.reaching || self.recast
    }

    /// Handing it to code the census does not read may hand over the field.
    fn reaches(&self) -> bool {
        self.reaching || self.recast
    }

    fn of_field(part: bool) -> Origin {
        Origin { whole: !part, part, ..Origin::default() }
    }

    fn holder() -> Origin {
        Origin { lent: true, reaching: true, ..Origin::default() }
    }

    fn add_slot(&mut self, slot: Slot) -> bool {
        match self.slots.binary_search(&slot) {
            Ok(_) => false,
            Err(at) => {
                self.slots.insert(at, slot);
                true
            }
        }
    }

    fn join(&mut self, other: &Origin) -> bool {
        let before = (self.whole, self.part, self.lent, self.reaching, self.recast, self.outside);
        self.whole |= other.whole;
        self.part |= other.part;
        self.lent |= other.lent;
        self.reaching |= other.reaching;
        self.recast |= other.recast;
        self.outside |= other.outside;
        let mut grew =
            before != (self.whole, self.part, self.lent, self.reaching, self.recast, self.outside);
        for slot in &other.slots {
            grew |= self.add_slot(*slot);
        }
        grew
    }

    /// The facts without the slots, which mean nothing in another body.
    fn stripped(&self) -> Origin {
        Origin { slots: Vec::new(), ..self.clone() }
    }
}

/// A value's two origins: what it points to, and the pointers inside it.
#[derive(Clone, Default, PartialEq, Eq, Debug)]
pub(super) struct Val {
    p: Origin,
    i: Origin,
}

impl Val {
    fn join(&mut self, other: &Val) -> bool {
        let p = self.p.join(&other.p);
        let i = self.i.join(&other.i);
        p || i
    }

    /// Every pointer in the value: itself, and those inside it.
    fn all(&self) -> Origin {
        let mut all = self.p.clone();
        all.join(&self.i);
        all
    }

    fn pointing(p: Origin) -> Val {
        Val { p, i: Origin::default() }
    }

    fn holding(i: Origin) -> Val {
        Val { p: Origin::default(), i }
    }
}

/// What a place is to the bound field.
#[derive(Clone, PartialEq, Eq, Debug)]
enum Region {
    /// Not the field, and no value that holds it: the body's own value, or
    /// a place the path says is beside the field.
    Apart,
    /// In memory the body does not own, where no type matched: not the
    /// field for a write, but nothing says what a std container there owns.
    Unmatched,
    /// The field, or part of it.
    Field { part: bool },
    /// A value that may hold the field, or the field by type alone: the verb
    /// a write to it is reported with.
    Holder(String),
}

impl Region {
    fn join(self, other: Region) -> Region {
        match (self, other) {
            (Region::Field { part: a }, Region::Field { part: b }) => {
                Region::Field { part: a && b }
            }
            (field @ Region::Field { .. }, _) | (_, field @ Region::Field { .. }) => field,
            (holder @ Region::Holder(_), _) | (_, holder @ Region::Holder(_)) => holder,
            (Region::Unmatched, _) | (_, Region::Unmatched) => Region::Unmatched,
            (Region::Apart, Region::Apart) => Region::Apart,
        }
    }
}

/// What a closure's parent says of one capture ([`Solved::closures`]).
#[derive(Clone)]
struct CaptureFact {
    /// The pointers in the captured value, without slots.
    val: Val,
    /// For a value moved or copied in out of a place with a projection: what
    /// that place is in the parent.
    region: Option<Region>,
}

/// One body's solution, kept for the closures written in it.
pub(super) struct Solved {
    facts: Vec<Val>,
    /// What each capture of the body's own environment held at the fixpoint.
    captures: Vec<Val>,
    closures: FxHashMap<DefId, Vec<CaptureFact>>,
}

/// The solutions of one field's scan, by body and instance.
pub(super) type Solutions<'tcx> = FxHashMap<(LocalDefId, Option<GenericArgs<'tcx>>), Rc<Solved>>;

/// What one field's scan is given.
pub(super) struct Scan<'a, 'tcx> {
    pub(super) tcx: TyCtxt<'tcx>,
    pub(super) hooks: &'a dyn CensusHooks<'tcx>,
    pub(super) bound: &'a BoundPlace<'tcx>,
    pub(super) runnable: &'a FxHashSet<LocalDefId>,
    /// What every fn that is not the crate's own, and is used as a VALUE
    /// somewhere in it, takes (`None`: a type still to be instantiated).
    pub(super) foreign_inputs: &'a FxHashSet<Option<Ty<'tcx>>>,
    /// The consumer's own by-value argument (or the variable it runs on) in a
    /// body that is a consumer of the field.
    pub(super) owner_of: &'a dyn Fn(LocalDefId) -> Option<mir::Local>,
    /// Whether a consumer of the field runs in the body: it is one, or one is
    /// a closure written inside it.
    pub(super) consumes: &'a dyn Fn(LocalDefId) -> bool,
    /// Whether a fn is a consumer of the field.
    pub(super) consumer: &'a dyn Fn(DefId) -> bool,
    /// The type walks' answers, kept for the whole scan.
    pub(super) walks: std::cell::RefCell<Walks<'tcx>>,
}

/// The answers of the walks over types ("can a value of this type have a
/// pointer in it", "does it reach", ..): one per question and type, kept for
/// the whole scan, so that a walk asks each type once (an expression tree
/// with a dozen fields of its own type is a dozen questions, not twelve to
/// the eighth). A type met again on its own way round answers no, since the
/// rest of the walk decides; an answer that leaned on that is not kept.
#[derive(Default)]
pub(super) struct Walks<'tcx> {
    known: FxHashMap<(u8, Ty<'tcx>, Option<Ty<'tcx>>), bool>,
    /// The questions being answered, each with its depth.
    open: FxHashMap<(u8, Ty<'tcx>, Option<Ty<'tcx>>), usize>,
    /// How many instances of each of the program's own types are being
    /// asked about at once: one that holds its next instantiation
    /// (`Nest<T>` with a `Box<Nest<(T, T)>>`) has no last one.
    grown: FxHashMap<(u8, DefId), usize>,
    /// The shallowest open question an answer has leaned on.
    low: usize,
}

const ASK_POINTS: u8 = 0;
const ASK_REACHES: u8 = 1;
const ASK_WRITES: u8 = 2;
const ASK_VIEW_WRITES: u8 = 3;
const ASK_TAKES: u8 = 4;
const ASK_OWNS: u8 = 5;
const ASK_INSIDE: u8 = 6;
const ASK_STORES: u8 = 7;
const ASK_DROPS: u8 = 8;
const ASK_FOREIGN_DROPS: u8 = 9;

/// What a capture is in the closure's environment.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Class {
    /// A pointer (or a value the closure owns that has pointers inside).
    Carried,
    /// The bound field itself, or part of it, held by value.
    Held { part: bool },
    /// A value that holds the field, held by value.
    Holder,
    /// The closure's own value.
    Own,
}

struct Capture {
    val: Val,
    class: Class,
}

struct Env {
    /// An `FnMut` or `Fn` closure is given a reference to its environment.
    by_ref: bool,
    captures: Vec<Capture>,
}

const ENV: mir::Local = mir::Local::from_u32(1);

fn derefs(elems: &[mir::PlaceElem<'_>]) -> bool {
    elems.iter().any(|elem| matches!(elem, mir::ProjectionElem::Deref))
}

/// One body, read at one instance, with its solution.
struct Frame<'a, 'b, 'tcx> {
    cx: &'a Scan<'a, 'tcx>,
    body: &'b mir::Body<'tcx>,
    subst: Option<GenericArgs<'tcx>>,
    /// The variables a consumer may run on ([`lent_owners`]).
    owners: FxHashSet<mir::Local>,
    env: Option<Env>,
    facts: Vec<Val>,
}

impl<'a, 'b, 'tcx> Frame<'a, 'b, 'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.cx.tcx
    }

    fn bound(&self) -> &'a BoundPlace<'tcx> {
        self.cx.bound
    }

    fn local_ty(&self, local: mir::Local) -> Ty<'tcx> {
        at_instance(self.tcx(), self.subst, self.body.local_decls[local].ty)
    }

    fn place_ty(&self, place: mir::Place<'tcx>) -> Ty<'tcx> {
        at_instance(self.tcx(), self.subst, place.ty(self.body, self.tcx()).ty)
    }

    fn is_env(&self, local: mir::Local) -> bool {
        self.env.is_some() && local == ENV
    }

    /// `place` as a capture of the environment and what follows it:
    /// `_1.i.rest`, or `(*_1).i.rest` behind the environment's reference.
    fn env_split(&self, place: mir::Place<'tcx>) -> Option<(usize, &'tcx [mir::PlaceElem<'tcx>])> {
        let env = self.env.as_ref()?;
        if place.local != ENV {
            return None;
        }
        let projection: &'tcx [mir::PlaceElem<'tcx>] = place.projection.as_slice();
        let (index, rest) = match (env.by_ref, projection) {
            (
                true,
                [mir::ProjectionElem::Deref, mir::ProjectionElem::Field(index, _), rest @ ..],
            )
            | (false, [mir::ProjectionElem::Field(index, _), rest @ ..]) => (index, rest),
            _ => return None,
        };
        (index.as_usize() < env.captures.len()).then_some((index.as_usize(), rest))
    }

    /// One question of a walk over types ([`Walks`]): each type is asked
    /// once, however deep the program's types nest. Only a type that grows
    /// as it is walked is cut short (below).
    fn asked(
        &self,
        question: u8,
        ty: Ty<'tcx>,
        other: Option<Ty<'tcx>>,
        ask: impl FnOnce(&Self) -> bool,
    ) -> bool {
        let key = (question, ty, other);
        // (std's types do not grow; an application's state nests its own a
        // hundred deep, each a different one.)
        let own = match *ty.kind() {
            ty::Adt(adt, args)
                if args.non_erasable_generics().next().is_some()
                    && !crate::def_is_in_sysroot_resident_crate(self.tcx(), adt.did()) =>
            {
                Some((question, adt.did()))
            }
            _ => None,
        };
        let (at, outer) = {
            let mut walks = self.cx.walks.borrow_mut();
            if let Some(&known) = walks.known.get(&key) {
                return known;
            }
            if let Some(&at) = walks.open.get(&key) {
                walks.low = walks.low.min(at);
                return false;
            }
            // A type that GROWS as it is walked (it holds its next
            // instantiation: `Nest<T>` with a `&Nest<Option<T>>`) is read
            // six instantiations down, and what is below is taken to be
            // more of the same: no new pointer to the consumer's value
            // (the two questions that would otherwise answer yes for every
            // such type, and refuse any program that has one), and anything
            // else a pointer could do.
            let growing =
                own.is_some_and(|own| walks.grown.get(&own).is_some_and(|open| *open >= 6));
            if growing || walks.open.len() > 600 || ty.has_escaping_bound_vars() {
                return !matches!(question, ASK_REACHES | ASK_OWNS);
            }
            if let Some(own) = own {
                *walks.grown.entry(own).or_default() += 1;
            }
            let at = walks.open.len();
            walks.open.insert(key, at);
            (at, std::mem::replace(&mut walks.low, usize::MAX))
        };
        let answer = rustc_data_structures::stack::ensure_sufficient_stack(|| ask(self));
        let mut walks = self.cx.walks.borrow_mut();
        walks.open.remove(&key);
        if let Some(own) = own {
            *walks.grown.entry(own).or_default() -= 1;
        }
        let low = walks.low;
        // (A no that leaned on a question still open above this one is that
        // question's to give.)
        if answer || low >= at {
            walks.known.insert(key, answer);
        }
        walks.low = outer.min(if low < at { low } else { usize::MAX });
        answer
    }

    /// Whether a value of type `ty` can have a pointer in it at all. Only
    /// what plainly cannot answers no.
    fn may_point(&self, ty: Ty<'tcx>) -> bool {
        self.asked(ASK_POINTS, ty, None, |this| this.may_point_in(ty))
    }

    fn may_point_in(&self, ty: Ty<'tcx>) -> bool {
        let tcx = self.tcx();
        match *ty.kind() {
            ty::Bool
            | ty::Char
            | ty::Int(_)
            | ty::Uint(_)
            | ty::Float(_)
            | ty::Str
            | ty::Never
            | ty::FnDef(..) => false,
            ty::Tuple(fields) => fields.iter().any(|field| self.may_point(field)),
            ty::Array(inner, _) | ty::Slice(inner) | ty::Pat(inner, _) => self.may_point(inner),
            ty::Adt(adt, args) => {
                if ty.is_box() || ty.has_escaping_bound_vars() {
                    return true;
                }
                if crate::def_is_in_sysroot_resident_crate(tcx, adt.did()) {
                    // A std type keeps what it holds behind pointers of its
                    // own. It has a pointer of the PROGRAM's when it names a
                    // lifetime (`IterMut<'_, T>`), is one of std's pointer
                    // types, or holds a type that has one (`Vec<&mut T>`):
                    // a `String`, a `Vec<u8>`, an `Option<Config>` have none.
                    args.regions().next().is_some()
                        || matches!(
                            tcx.item_name(adt.did()).as_str(),
                            "NonNull" | "Unique" | "Rc" | "Arc" | "Weak" | "Pin"
                        )
                        || args.types().any(|inner| self.may_point(inner))
                } else {
                    adt.all_fields().any(|field| {
                        let field = at_instance(tcx, None, field.ty(tcx, args).skip_norm_wip());
                        self.may_point(field)
                    })
                }
            }
            _ => true,
        }
    }

    /// Whether a pointer to a `pointee` may be one to a value that holds the
    /// field (or to the field, by type).
    fn pointee_holds(&self, pointee: Ty<'tcx>) -> bool {
        let bound = self.bound();
        bound.containers.contains(&pointee)
            || bound
                .containers
                .iter()
                .any(|container| container.has_non_region_param() && could_be(*container, pointee))
            || pointee == bound.field_ty
            || bound.boxed.contains(&pointee)
            || bound.is_root(pointee)
            || bound.holds(self.tcx(), pointee)
    }

    /// Whether a value of type `ty`, of unknown origin, may be or carry a
    /// pointer to a value that holds the field: `&mut Config`, an
    /// `Option<&mut Config>`, a struct with one in a field, an iterator over
    /// them. A `&T` counts where the field has interior mutability. A `Box`
    /// owns its value and is no pointer INTO another.
    fn reaches_by_type(&self, ty: Ty<'tcx>) -> bool {
        self.asked(ASK_REACHES, ty, None, |this| this.reaches_in(ty))
    }

    fn reaches_in(&self, ty: Ty<'tcx>) -> bool {
        let tcx = self.tcx();
        // (A thread-local's key is a `&` of what it keeps.)
        if let ty::Ref(_, pointee, _) = *ty.kind() {
            if let ty::Adt(adt, args) = *pointee.kind() {
                if crate::def_is_in_sysroot_resident_crate(tcx, adt.did())
                    && tcx.item_name(adt.did()).as_str() == "LocalKey"
                {
                    return args.types().any(|kept| {
                        self.reaches_by_type(Ty::new_imm_ref(tcx, tcx.lifetimes.re_erased, kept))
                    });
                }
            }
        }
        match *ty.kind() {
            // (A `&` reaches a holder with interior mutability; one of the
            // field's own type alone is not known to be the field.)
            ty::Ref(_, pointee, mutability) if mutability.is_mut() => {
                self.pointee_holds(pointee) || self.reaches_by_type(pointee)
            }
            // (Through a `&`, only what can be copied out of the pointee
            // and still write: a `&Wrapper { c: &mut Config }` writes
            // nothing.)
            ty::Ref(_, pointee, _) => {
                (self.bound().shared_writes(tcx, pointee)
                    && pointee != self.bound().field_ty
                    && self.pointee_holds(pointee))
                    || (self.view_writes(pointee) && self.reaches_by_type(pointee))
            }
            ty::RawPtr(pointee, _) => self.pointee_holds(pointee) || self.reaches_by_type(pointee),
            ty::Tuple(fields) => fields.iter().any(|field| self.reaches_by_type(field)),
            ty::Array(inner, _) | ty::Slice(inner) | ty::Pat(inner, _) => {
                self.reaches_by_type(inner)
            }
            ty::Adt(_, args) if ty.is_box() => {
                args.types().next().is_some_and(|inner| self.reaches_by_type(inner))
            }
            ty::Adt(adt, args) if crate::def_is_in_sysroot_resident_crate(tcx, adt.did()) => {
                // A std type with a lifetime keeps a pointer to what it
                // names (`IterMut<'_, Config>`, `RefMut<'_, Config>`); so do
                // std's own pointer types.
                let points = args.regions().next().is_some()
                    || matches!(tcx.item_name(adt.did()).as_str(), "NonNull" | "Unique" | "Pin");
                args.types().any(|inner| {
                    (points && self.pointee_holds(inner)) || self.reaches_by_type(inner)
                })
            }
            ty::Adt(adt, args) => adt.all_fields().any(|field| {
                let field = at_instance(tcx, None, field.ty(tcx, args).skip_norm_wip());
                self.reaches_by_type(field)
            }),
            ty::Closure(_, args) => {
                args.as_closure().upvar_tys().iter().any(|upvar| self.reaches_by_type(upvar))
            }
            // (What a `dyn` hides is not known; what its trait NAMES is: a
            // `dyn Iterator<Item = &mut Config>` hands out pointers that
            // reach, a `dyn Write` names none.)
            // What a `dyn` hides is not known; what its trait HANDS OUT is
            // named: a `dyn Iterator<Item = &mut Config>` yields pointers
            // that reach, a `dyn Write` names none, and a
            // `dyn FnOnce(&mut App)` names what it is GIVEN (the call that
            // hands it a pointer is where that is judged), with what it
            // returns.
            ty::Dynamic(predicates, _) => {
                let lang = tcx.lang_items();
                let named = |args: GenericArgs<'tcx>| {
                    args.types().any(|named| {
                        named.walk().any(|part| {
                            matches!(part.kind(), GenericArgKind::Type(part)
                                if !part.has_escaping_bound_vars()
                                    && self.reaches_by_type(part))
                        })
                    })
                };
                predicates.principal().is_some_and(|principal| {
                    let called = [lang.fn_trait(), lang.fn_mut_trait(), lang.fn_once_trait()]
                        .contains(&Some(principal.def_id()));
                    !called && named(tcx.instantiate_bound_regions_with_erased(principal).args)
                }) || predicates.projection_bounds().any(|bound| {
                    let bound = tcx.instantiate_bound_regions_with_erased(bound);
                    bound.term.as_type().is_some_and(|term| {
                        !term.has_escaping_bound_vars() && self.reaches_by_type(term)
                    })
                })
            }
            _ => false,
        }
    }

    /// Whether `ty` is the type the path starts on, or one that holds it by
    /// value.
    fn names(&self, ty: Ty<'tcx>) -> bool {
        self.bound().is_root(ty) || self.bound().holds(self.tcx(), ty)
    }

    /// Whether a value of type `ty` holds, or OWNS in memory of its own (a
    /// std collection, a box), a value of the type the path starts on:
    /// `Vec<App>`, `HashMap<K, App>`, `Option<Box<App>>`. What std hands back
    /// from one is a pointer to a value a consumer may run on.
    fn owns_root(&self, ty: Ty<'tcx>) -> bool {
        self.asked(ASK_OWNS, ty, None, |this| this.owns_root_in(ty))
    }

    fn owns_root_in(&self, ty: Ty<'tcx>) -> bool {
        let tcx = self.tcx();
        if self.names(ty) {
            return true;
        }
        match *ty.kind() {
            ty::Tuple(fields) => fields.iter().any(|field| self.owns_root(field)),
            ty::Array(inner, _) | ty::Slice(inner) | ty::Pat(inner, _) => self.owns_root(inner),
            ty::Adt(adt, args) if crate::def_is_in_sysroot_resident_crate(tcx, adt.did()) => {
                !adt.is_phantom_data() && args.types().any(|inner| self.owns_root(inner))
            }
            ty::Adt(adt, args) if !ty.has_escaping_bound_vars() => adt.all_fields().any(|field| {
                let field = at_instance(tcx, None, field.ty(tcx, args).skip_norm_wip());
                self.owns_root(field)
            }),
            _ => false,
        }
    }

    /// Whether a value of type `ty`, in hand by value or through a `&mut`,
    /// has in it a pointer that can write: a `&mut`, a raw pointer, or a `&`
    /// that can ([`Self::view_writes`]). A `&'static str`, a `Cow<str>`, an
    /// `Arc<str>`, a `Box<[u8]>` have none.
    fn owned_writes(&self, ty: Ty<'tcx>) -> bool {
        self.writes(ty, false)
    }

    /// Whether whoever holds a `&` of a value of type `ty` can get out of it
    /// a pointer that can write: a raw pointer or a `&` of a cell, which it
    /// copies out; what a cell or a channel in it hands out. Not a `&mut`
    /// kept there, which a `&` of it only reads through.
    fn view_writes(&self, ty: Ty<'tcx>) -> bool {
        self.writes(ty, true)
    }

    fn writes(&self, ty: Ty<'tcx>, view: bool) -> bool {
        let question = if view { ASK_VIEW_WRITES } else { ASK_WRITES };
        self.asked(question, ty, None, |this| this.writes_in(ty, view))
    }

    fn writes_in(&self, ty: Ty<'tcx>, view: bool) -> bool {
        let tcx = self.tcx();
        if !self.may_point(ty) {
            return false;
        }
        let bound = self.bound();
        // What a `&` of an `inner` gives: a write of it, or what is in it.
        let seen = |inner: Ty<'tcx>| bound.shared_writes(tcx, inner) || self.writes(inner, true);
        match *ty.kind() {
            ty::RawPtr(..) => true,
            ty::Ref(_, inner, mutability) => (!view && mutability.is_mut()) || seen(inner),
            ty::Tuple(fields) => fields.iter().any(|field| self.writes(field, view)),
            ty::Array(inner, _) | ty::Slice(inner) | ty::Pat(inner, _) => self.writes(inner, view),
            // (A box of what the path keeps in a box may be that box, made
            // twice by `ptr::read`: a pointer that writes the field.)
            ty::Adt(_, args) if ty.is_box() => args.types().next().is_some_and(|inner| {
                (!view && bound.boxed.contains(&inner)) || self.writes(inner, view)
            }),
            ty::Adt(adt, args) if crate::def_is_in_sysroot_resident_crate(tcx, adt.did()) => {
                let name = tcx.item_name(adt.did());
                let path = tcx.def_path_str(adt.did());
                if matches!(name.as_str(), "NonNull" | "Unique") {
                    true
                } else if matches!(name.as_str(), "Arguments" | "Argument") && path.contains("fmt")
                {
                    // What `format_args!` builds holds `&`s for the `fmt`
                    // impl of each value's type: an impl of the crate is
                    // read on its own, and std's write nothing.
                    false
                } else if self.channel(ty) {
                    // A channel hands out, to a `&` of its end, what was put
                    // in it.
                    args.types().any(|inner| self.writes(inner, false))
                } else if matches!(name.as_str(), "Rc" | "Arc" | "Weak") {
                    args.types().any(seen)
                } else if ty.has_param() || !ty.is_freeze(tcx, ty::TypingEnv::fully_monomorphized())
                {
                    // A cell, a lock: what it holds comes out whole.
                    args.types().any(|inner| self.writes(inner, false))
                } else if args.regions().next().is_some() {
                    // A std type that borrows (a guard, an iterator): by
                    // value it may hand out `&mut`s; a `&` of it shows what
                    // it borrows.
                    if view { args.types().any(seen) } else { true }
                } else {
                    args.types().any(|inner| self.writes(inner, view))
                }
            }
            ty::Adt(adt, args) => adt.all_fields().any(|field| {
                let field = at_instance(tcx, None, field.ty(tcx, args).skip_norm_wip());
                self.writes(field, view)
            }),
            ty::Closure(_, args) => {
                args.as_closure().upvar_tys().iter().any(|upvar| self.writes(upvar, view))
            }
            ty::FnDef(..) | ty::FnPtr(..) => false,
            _ => true,
        }
    }

    /// Whether whoever is handed a value of type `ty` can get at the pointers
    /// kept in the storage its pointers point into. Through a `&mut` or a
    /// raw pointer: whatever the pointee can hold (a `&mut Vec<u8>` into a
    /// variable that also keeps a `&mut Config` takes none of it). Through a
    /// `&`: only what can be copied out and still write. In a value that
    /// carries pointers: as each of them does.
    fn takes(&self, ty: Ty<'tcx>) -> bool {
        self.asked(ASK_TAKES, ty, None, |this| this.takes_in(ty))
    }

    fn takes_in(&self, ty: Ty<'tcx>) -> bool {
        let tcx = self.tcx();
        if !self.may_point(ty) {
            return false;
        }
        match *ty.kind() {
            ty::RawPtr(pointee, _) => self.may_point(pointee),
            ty::Ref(_, pointee, mutability) if mutability.is_mut() => self.may_point(pointee),
            ty::Ref(_, pointee, _) => {
                self.may_point(pointee) && (self.bound().interior || self.view_writes(pointee))
            }
            ty::Tuple(fields) => fields.iter().any(|field| self.takes(field)),
            ty::Array(inner, _) | ty::Slice(inner) | ty::Pat(inner, _) => self.takes(inner),
            ty::Adt(_, args) if ty.is_box() => {
                args.types().next().is_some_and(|inner| self.takes(inner))
            }
            ty::Adt(adt, args) if crate::def_is_in_sysroot_resident_crate(tcx, adt.did()) => {
                let name = tcx.item_name(adt.did());
                if matches!(name.as_str(), "Arguments" | "Argument")
                    && tcx.def_path_str(adt.did()).contains("fmt")
                {
                    false
                } else if args.regions().next().is_some()
                    || matches!(name.as_str(), "NonNull" | "Unique")
                {
                    // (A pointer to each of what it names.)
                    args.types().next().is_none() || args.types().any(|inner| self.may_point(inner))
                } else {
                    args.types().any(|inner| self.takes(inner))
                }
            }
            ty::Adt(adt, args) => adt.all_fields().any(|field| {
                let field = at_instance(tcx, None, field.ty(tcx, args).skip_norm_wip());
                self.takes(field)
            }),
            ty::Closure(_, args) => {
                args.as_closure().upvar_tys().iter().any(|upvar| self.takes(upvar))
            }
            ty::FnDef(..) | ty::FnPtr(..) => false,
            _ => true,
        }
    }

    /// Whether `ty` is an end of one of std's channels, or an iterator over
    /// one: what it holds is shared with whoever holds the other end.
    fn channel(&self, ty: Ty<'tcx>) -> bool {
        let tcx = self.tcx();
        matches!(*ty.kind(), ty::Adt(adt, _)
        if crate::def_is_in_sysroot_resident_crate(tcx, adt.did()) && {
            let path = tcx.def_path_str(adt.did());
            path.contains("mpsc::") || path.contains("mpmc::")
        })
    }

    /// Whether a value of type `ty` handed to code LEAVES with it: not a `&`
    /// with which that code can neither write nor take out a pointer that
    /// can.
    fn carries(&self, ty: Ty<'tcx>) -> bool {
        match *ty.kind() {
            ty::Ref(_, pointee, mutability) if !mutability.is_mut() => {
                self.bound().interior
                    || self.bound().shared_writes(self.tcx(), pointee)
                    || self.view_writes(pointee)
            }
            _ => true,
        }
    }

    /// Whether `ty` is one of std's guards: it BORROWS what it names. A
    /// variable of it holds, and owns, none of that, and its drop drops none
    /// of it.
    fn guard(&self, ty: Ty<'tcx>) -> bool {
        let tcx = self.tcx();
        matches!(*ty.kind(), ty::Adt(adt, _)
        if crate::def_is_in_sysroot_resident_crate(tcx, adt.did())
            && matches!(
                tcx.item_name(adt.did()).as_str(),
                "MutexGuard"
                    | "MappedMutexGuard"
                    | "RwLockReadGuard"
                    | "RwLockWriteGuard"
                    | "MappedRwLockReadGuard"
                    | "MappedRwLockWriteGuard"
                    | "ReentrantLockGuard"
                    | "Ref"
                    | "RefMut"
            ))
    }

    /// Whether a value of type `a` has a value of type `r` in it, by value
    /// or in memory it owns: a pointer to an `r` can point INTO a variable
    /// of type `a` only then. A guard holds no `App`, it points to one; a
    /// `&mut Config` variable holds no `Config`.
    fn has_inside(&self, a: Ty<'tcx>, r: Ty<'tcx>) -> bool {
        a == r || self.asked(ASK_INSIDE, a, Some(r), |this| this.has_inside_in(a, r))
    }

    fn has_inside_in(&self, a: Ty<'tcx>, r: Ty<'tcx>) -> bool {
        let tcx = self.tcx();
        // (A slice of them is in it where one of them is.)
        if let ty::Array(element, _) | ty::Slice(element) = *r.kind() {
            if self.has_inside(a, element) {
                return true;
            }
        }
        match *a.kind() {
            ty::Tuple(fields) => fields.iter().any(|field| self.has_inside(field, r)),
            ty::Array(inner, _) | ty::Slice(inner) | ty::Pat(inner, _) => self.has_inside(inner, r),
            ty::Adt(adt, args) if crate::def_is_in_sysroot_resident_crate(tcx, adt.did()) => {
                !self.guard(a) && args.types().any(|inner| self.has_inside(inner, r))
            }
            ty::Adt(adt, args) => adt.all_fields().any(|field| {
                let field = at_instance(tcx, None, field.ty(tcx, args).skip_norm_wip());
                self.has_inside(field, r)
            }),
            ty::Closure(_, args) => {
                args.as_closure().upvar_tys().iter().any(|upvar| self.has_inside(upvar, r))
            }
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
            | ty::FnPtr(..) => false,
            _ => true,
        }
    }

    /// What the pointers in a value of type `ty` point to, by type; `None`
    /// when a type does not say (a `dyn`, a type of another crate, a std type
    /// that erases it, a raw pointer that a struct keeps: `*mut c_void`).
    /// A struct or an enum of this crate has the pointers its fields have.
    fn pointees(
        &self,
        ty: Ty<'tcx>,
        depth: usize,
        kept: bool,
        seen: &mut FxHashSet<Ty<'tcx>>,
        into: &mut Vec<Ty<'tcx>>,
    ) -> Option<()> {
        let tcx = self.tcx();
        if !self.may_point(ty) {
            return Some(());
        }
        if depth > 8 || seen.len() > 64 || ty.has_escaping_bound_vars() {
            return None;
        }
        // (A type walked once has said all it says.)
        if !seen.insert(ty) {
            return Some(());
        }
        match *ty.kind() {
            ty::RawPtr(..) if kept => None,
            ty::Ref(_, pointee, _) | ty::RawPtr(pointee, _) => {
                if matches!(
                    pointee.kind(),
                    ty::Dynamic(..) | ty::Param(_) | ty::Alias(..) | ty::Str
                ) {
                    return None;
                }
                into.push(pointee);
                self.pointees(pointee, depth + 1, kept, seen, into)
            }
            ty::Tuple(fields) => fields
                .iter()
                .try_for_each(|field| self.pointees(field, depth + 1, kept, seen, into)),
            ty::Array(inner, _) | ty::Slice(inner) | ty::Pat(inner, _) => {
                self.pointees(inner, depth + 1, kept, seen, into)
            }
            ty::Adt(adt, args) if crate::def_is_in_sysroot_resident_crate(tcx, adt.did()) => {
                let raw = matches!(tcx.item_name(adt.did()).as_str(), "NonNull" | "Unique");
                if raw && kept {
                    return None;
                }
                let points = raw
                    || args.regions().next().is_some()
                    || matches!(tcx.item_name(adt.did()).as_str(), "Rc" | "Arc" | "Weak");
                if points && args.types().next().is_none() {
                    return None;
                }
                args.types().try_for_each(|inner| {
                    if points {
                        into.push(inner);
                    }
                    self.pointees(inner, depth + 1, kept, seen, into)
                })
            }
            ty::Adt(adt, args) if adt.did().is_local() && !adt.is_union() => {
                adt.all_fields().try_for_each(|field| {
                    let field = at_instance(tcx, None, field.ty(tcx, args).skip_norm_wip());
                    self.pointees(field, depth + 1, true, seen, into)
                })
            }
            _ => None,
        }
    }

    /// `val`, a pointer or a carrier of type `ty` that a safe std fn handed
    /// back, without the variables its type says it cannot point into.
    fn fit(&self, mut val: Val, ty: Ty<'tcx>) -> Val {
        let mut pointees = Vec::new();
        if self.pointees(ty, 0, false, &mut FxHashSet::default(), &mut pointees).is_none() {
            return val;
        }
        let keep = |slot: &Slot| {
            let held = self.local_ty(slot.local());
            pointees.iter().any(|pointee| self.has_inside(held, *pointee))
        };
        val.p.slots.retain(keep);
        val.i.slots.retain(keep);
        val
    }

    /// Every pointer kept in the storage `origin` points into, and in the
    /// storage those point into; with that storage.
    fn content(&self, origin: &Origin) -> (Origin, FxHashSet<Slot>) {
        let mut all = Origin::default();
        let mut seen: FxHashSet<Slot> = FxHashSet::default();
        let mut work: Vec<Slot> = origin.slots.clone();
        while let Some(slot) = work.pop() {
            if !seen.insert(slot) {
                continue;
            }
            let held = &self.facts[slot.local().as_usize()];
            let inside = match slot {
                Slot::Local(_) => held.all(),
                Slot::Boxed(_) => held.i.clone(),
            };
            work.extend(inside.slots.iter().copied().filter(|slot| !seen.contains(slot)));
            all.join(&inside);
        }
        (all, seen)
    }

    /// The pointers inside a value of type `ty` whose origin is not known.
    fn unknown_inside(&self, ty: Ty<'tcx>) -> Origin {
        if !self.owned_writes(ty) {
            return Origin::default();
        }
        Origin { lent: true, reaching: self.reaches_by_type(ty), ..Origin::default() }
    }

    /// A value of type `ty` whose origin the body cannot see.
    fn unknown(&self, ty: Ty<'tcx>) -> Val {
        match *ty.kind() {
            // (A `&` with which nothing is written and out of which no
            // pointer that writes is copied is no pointer to follow: a
            // `&'static str`, a `&Config` of plain fields.)
            ty::Ref(_, pointee, mutability)
                if !mutability.is_mut()
                    && !self.bound().interior
                    && !self.bound().shared_writes(self.tcx(), pointee)
                    && !self.view_writes(pointee) =>
            {
                Val::default()
            }
            ty::Ref(..) | ty::RawPtr(..) => Val::pointing(Origin {
                lent: true,
                reaching: self.reaches_by_type(ty),
                ..Origin::default()
            }),
            // A box owns what it holds: one the body was given is no pointer
            // into a consumer's value (a `Box<Config>` in hand is a `Config`
            // in hand). A box of the value a consumer runs on, or of one that
            // holds it, is a pointer to that. And where the PATH keeps the
            // pointee in a box (`config: Box<Config>`), a box of it may be
            // that one, made twice by `ptr::read`: a write through it is
            // judged by type.
            _ if ty.is_box() => Val {
                p: match ty.boxed_ty() {
                    Some(inner) if self.names(inner) => Origin::holder(),
                    Some(inner) if self.bound().boxed.contains(&inner) => {
                        Origin { lent: true, ..Origin::default() }
                    }
                    _ => Origin::default(),
                },
                i: ty.boxed_ty().map(|inner| self.unknown_inside(inner)).unwrap_or_default(),
            },
            _ => Val::holding(self.unknown_inside(ty)),
        }
    }

    /// [`overlap`]'s answer for `place`, by its path and type.
    fn judge(&self, place: mir::Place<'tcx>) -> Region {
        let mut beside = false;
        let answer = overlap(
            self.tcx(),
            self.body,
            place,
            self.bound(),
            &self.owners,
            self.subst,
            &mut beside,
        );
        match answer {
            Some((verb, true)) => Region::Field { part: verb.starts_with("writes part") },
            Some((verb, false)) => Region::Holder(verb),
            None if beside => Region::Apart,
            None => Region::Unmatched,
        }
    }

    /// What `place` is to the bound field, for a write to it or a borrow of
    /// it. MIR dereferences a pointer only at the start of a place; a place
    /// that does so elsewhere is judged by type.
    fn region(&self, place: mir::Place<'tcx>) -> Region {
        let projection = place.projection.as_slice();
        match projection.first() {
            Some(mir::ProjectionElem::Deref) if self.env_split(place).is_none() => {
                let rest = &projection[1..];
                if derefs(rest) {
                    return self.judge(place);
                }
                self.through(&self.facts[place.local.as_usize()].p, place, rest)
            }
            _ => self.in_value(place),
        }
    }

    /// `place` is `(*p).rest`, `x` what `p` points to.
    fn through(
        &self,
        x: &Origin,
        place: mir::Place<'tcx>,
        rest: &[mir::PlaceElem<'tcx>],
    ) -> Region {
        let mut region = Region::Apart;
        if x.field() {
            region = region.join(Region::Field { part: !x.whole || !rest.is_empty() });
        }
        if x.recast {
            region = region.join(Region::Holder(
                "writes, through a pointer cast to another type, into a value holding".to_owned(),
            ));
        } else if x.lent {
            region = region.join(self.judge(place));
        }
        for slot in &x.slots {
            // (What a local box holds is where the box's own facts say.)
            if let Slot::Local(local) = slot {
                let at = mir::Place { local: *local, projection: self.tcx().mk_place_elems(rest) };
                region = region.join(self.in_value(at));
            }
        }
        region
    }

    /// `place` is in a value the body holds: a variable, or a capture.
    fn in_value(&self, place: mir::Place<'tcx>) -> Region {
        if let Some((index, rest)) = self.env_split(place) {
            if derefs(rest) {
                return self.judge(place);
            }
            return match self.env.as_ref().map(|env| env.captures[index].class) {
                Some(Class::Held { part }) => Region::Field { part: part || !rest.is_empty() },
                Some(Class::Holder) => self.judge(place),
                _ => Region::Apart,
            };
        }
        if derefs(place.projection.as_slice()) {
            return self.judge(place);
        }
        if !self.owners.contains(&place.local) || self.is_env(place.local) {
            return Region::Apart;
        }
        if place.projection.is_empty() {
            let ty = self.local_ty(place.local);
            return Region::Holder(format!("writes a whole `{ty}` holding"));
        }
        self.judge(place)
    }

    /// Where a `Box` at `place` points, when the box is in memory the body
    /// does not own: by the path and the type of what it holds.
    fn boxed_by_path(&self, place: mir::Place<'tcx>) -> Origin {
        // (A box only at the instance: generic code holds a `T` and
        // dereferences none, so no place says where it points.)
        if !place.ty(self.body, self.tcx()).ty.is_box() {
            return self.unknown(self.place_ty(place)).p;
        }
        match self.judge(place.project_deeper(&[mir::ProjectionElem::Deref], self.tcx())) {
            Region::Field { part } => Origin::of_field(part),
            Region::Holder(_) => Origin::holder(),
            Region::Unmatched => Origin { outside: true, ..Origin::default() },
            Region::Apart => Origin::default(),
        }
    }

    /// A part of a carrier whose facts are `v`, as a value of type `ty`.
    fn part_of(&self, v: &Val, ty: Ty<'tcx>) -> Val {
        if ty.is_box() {
            Val { p: v.i.clone(), i: v.i.clone() }
        } else if matches!(ty.kind(), ty::Ref(..) | ty::RawPtr(..)) {
            Val::pointing(v.i.clone())
        } else {
            Val::holding(v.i.clone())
        }
    }

    /// A value read out of the consumer's own value, or out of memory a
    /// `lent` pointer points to: a pointer kept there points elsewhere; a box
    /// there owns part of the value.
    fn read_from_holder(&self, place: mir::Place<'tcx>, ty: Ty<'tcx>) -> Val {
        if ty.is_box() {
            Val {
                p: self.boxed_by_path(place),
                i: ty.boxed_ty().map(|inner| self.unknown_inside(inner)).unwrap_or_default(),
            }
        } else {
            self.unknown(ty)
        }
    }

    /// The pointers in the value at `place`.
    fn val(&self, place: mir::Place<'tcx>) -> Val {
        let ty = self.place_ty(place);
        if !self.may_point(ty) {
            return Val::default();
        }
        if let Some((index, rest)) = self.env_split(place) {
            let capture = &self.env.as_ref().expect("an environment").captures[index];
            if derefs(rest) {
                return self.unknown(ty);
            }
            return match capture.class {
                Class::Carried | Class::Own if rest.is_empty() => capture.val.clone(),
                Class::Carried | Class::Own => self.part_of(&capture.val, ty),
                Class::Held { .. } | Class::Holder => self.read_from_holder(place, ty),
            };
        }
        let projection = place.projection.as_slice();
        match projection.first() {
            None => self.facts[place.local.as_usize()].clone(),
            Some(mir::ProjectionElem::Deref) => {
                let rest = &projection[1..];
                if derefs(rest) {
                    return self.unknown(ty);
                }
                let x = &self.facts[place.local.as_usize()].p;
                let mut out = Val::default();
                for slot in &x.slots {
                    match *slot {
                        // (The whole variable only at the variable's own
                        // type: a pointer to part of it, `&mut pair.0`, has
                        // the variable as its slot too.)
                        Slot::Local(local) if rest.is_empty() && ty == self.local_ty(local) => {
                            out.join(&self.facts[local.as_usize()]);
                        }
                        Slot::Local(local) | Slot::Boxed(local) => {
                            out.join(&self.part_of(&self.facts[local.as_usize()], ty));
                        }
                    }
                }
                if x.facts() || x.slots.is_empty() {
                    // Out of memory the body does not own.
                    if ty.is_box() {
                        let p = if x.field() {
                            Origin::of_field(!(x.whole && rest.is_empty()))
                        } else if x.recast {
                            Origin { recast: true, ..Origin::holder() }
                        } else if x.lent {
                            self.boxed_by_path(place)
                        } else {
                            Origin::default()
                        };
                        let i = ty
                            .boxed_ty()
                            .map(|inner| self.unknown_inside(inner))
                            .unwrap_or_default();
                        out.join(&Val { p, i });
                    } else {
                        out.join(&self.unknown(ty));
                    }
                }
                out
            }
            Some(_) if derefs(projection) => self.unknown(ty),
            // (A variable a consumer may run on can carry pointers the body
            // put there, beside what is read out of the value by type.)
            Some(_) if self.owners.contains(&place.local) => {
                let mut val = self.read_from_holder(place, ty);
                val.join(&self.part_of(&self.facts[place.local.as_usize()], ty));
                val
            }
            Some(_) => self.part_of(&self.facts[place.local.as_usize()], ty),
        }
    }

    fn operand(&self, operand: &mir::Operand<'tcx>) -> Val {
        match operand {
            mir::Operand::Copy(place) | mir::Operand::Move(place) => self.val(*place),
            // A static's address, a promoted: of no origin the body sees.
            _ => {
                self.unknown(at_instance(self.tcx(), self.subst, operand.ty(self.body, self.tcx())))
            }
        }
    }

    /// What the pointer loaded out of the box at `holder` points to, with the
    /// storage the box owns when the box is in a value of the body's own.
    fn box_pointee(&self, holder: mir::Place<'tcx>) -> Origin {
        let mut origin = self.val(holder).p;
        let projection = holder.projection.as_slice();
        match projection.first() {
            Some(mir::ProjectionElem::Deref) if self.env_split(holder).is_none() => {
                let slots = self.facts[holder.local.as_usize()].p.slots.clone();
                for slot in slots {
                    origin.add_slot(Slot::Boxed(slot.local()));
                }
            }
            _ if derefs(projection) || self.is_env(holder.local) => {}
            _ if !self.owners.contains(&holder.local) => {
                origin.add_slot(Slot::Boxed(holder.local));
            }
            _ => {}
        }
        origin
    }

    /// Whether a borrow of `place` can write it: a `&mut` or a raw pointer;
    /// or a `&` of a place that has interior mutability, in itself or in a
    /// value it owns (a `&RefCell<App>` replaces the `App`; a `&` of an
    /// `App` whose fields are plain writes nothing).
    fn can_write(&self, place: mir::Place<'tcx>, mutable: bool) -> bool {
        mutable || self.bound().shared_writes(self.tcx(), self.place_ty(place))
    }

    /// The pointer a borrow of `place` makes.
    fn pointer_to(&self, place: mir::Place<'tcx>, mutable: bool) -> Origin {
        let mut origin = Origin::default();
        let projection = place.projection.as_slice();
        let based = match projection.first() {
            Some(mir::ProjectionElem::Deref) if self.env_split(place).is_none() => {
                Some(&self.facts[place.local.as_usize()].p)
            }
            _ => None,
        };
        if self.can_write(place, mutable) {
            match self.region(place) {
                Region::Field { part } => {
                    origin.join(&Origin::of_field(part));
                }
                // (A `&` of a cell whose type alone says it MAY be the field
                // is no pointer to it: every pointer to the field itself was
                // made by a borrow of its path, and is followed from there.
                // An `Arc<AtomicBool>` elsewhere is not a `flag: AtomicBool`.)
                Region::Holder(verb) if !mutable && !verb.starts_with("writes a whole") => {}
                Region::Holder(_) => {
                    origin.join(&Origin::holder());
                    origin.recast |= based.is_some_and(|based| based.recast);
                }
                Region::Apart | Region::Unmatched => {}
            }
            // (A reborrow of the whole pointee is the pointer again where
            // the pointee's TYPE says nothing of it: a `&mut dyn Reset` made
            // of a `&mut Config` names no `Config`. Where the type says "may
            // be the field" and a `&` is not followed on that alone, it is
            // not followed here either.)
            if let (Some(based), [mir::ProjectionElem::Deref]) = (based, projection) {
                if mutable || matches!(self.region(place), Region::Unmatched) {
                    origin.lent |= based.lent;
                    origin.reaching |= based.reaching;
                    origin.recast |= based.recast;
                }
            }
        }
        // (Whoever can write: where the pointer points is what std is asked.)
        origin.outside = matches!(self.region(place), Region::Unmatched)
            || based.is_some_and(|based| based.outside && !based.field());
        // (By `&` too: what is read through the pointer is what is there.)
        let _ = mutable;
        match based {
            Some(based) => {
                for slot in &based.slots {
                    origin.add_slot(*slot);
                }
            }
            None if !derefs(projection)
                && !self.is_env(place.local)
                && !self.owners.contains(&place.local) =>
            {
                origin.add_slot(Slot::Local(place.local));
            }
            None => {}
        }
        origin
    }

    /// Whether `def` is a closure whose body the census reads on its own,
    /// with what this body says of its captures.
    fn read_closure(&self, kind: &mir::AggregateKind<'tcx>) -> Option<DefId> {
        match *kind {
            mir::AggregateKind::Closure(def, _)
                if def.as_local().is_some_and(|def| self.cx.runnable.contains(&def)) =>
            {
                Some(def)
            }
            _ => None,
        }
    }

    /// The value an rvalue makes, for a target of type `ty`.
    fn rvalue(&self, rvalue: &mir::Rvalue<'tcx>, ty: Ty<'tcx>) -> Val {
        if !self.may_point(ty) {
            return Val::default();
        }
        match rvalue {
            mir::Rvalue::Use(operand, _) => self.operand(operand),
            mir::Rvalue::CopyForDeref(place) => self.val(*place),
            mir::Rvalue::Ref(_, kind, place) => {
                Val::pointing(self.pointer_to(*place, matches!(kind, mir::BorrowKind::Mut { .. })))
            }
            // A raw pointer can be written through whatever it was taken as.
            mir::Rvalue::RawPtr(_, place) => Val::pointing(self.pointer_to(*place, true)),
            mir::Rvalue::Cast(kind, operand, cast_ty) => {
                let Some(place) = operand.place() else { return self.unknown(ty) };
                if let Some(holder) = box_loaded_from(self.tcx(), self.body, place) {
                    return Val::pointing(self.box_pointee(holder));
                }
                let from = self.place_ty(place);
                let to = at_instance(self.tcx(), self.subst, *cast_ty);
                // A pointer made of a value that is none (an address, the
                // bytes of one) is of unknown origin, whatever the value was.
                if matches!(kind, mir::CastKind::PointerWithExposedProvenance)
                    || (matches!(kind, mir::CastKind::Transmute) && !self.may_point(from))
                {
                    return self.unknown(to);
                }
                let mut val = self.val(place);
                // A cast that changes what a pointer points to. Of a pointer
                // to a holder: no type says what a write through it is from
                // here on. Of a pointer of unknown origin TO a type that
                // reaches (`user as *mut App`, as a callback is handed its
                // state): it reaches, as one that came with that type does.
                // Any other is judged by the type it is used at, where it is
                // used (`(*buffer).data as *mut f32` reaches nothing).
                // (Not an unsizing: a `&mut App` made a `&mut dyn Handler`,
                // a `&mut [Config; 2]` made a `&mut [Config]`, points to
                // the same value, and what runs on it is still told by its
                // type.)
                let unsizes =
                    matches!(kind, mir::CastKind::PointerCoercion(PointerCoercion::Unsize, _));
                let pointee = |ty: Ty<'tcx>| ty.builtin_deref(true);
                if !unsizes && pointee(from).is_some() && pointee(from) != pointee(to) {
                    if val.p.reaching {
                        val.p.recast = true;
                    } else if val.p.lent && self.reaches_by_type(to) {
                        val.p.reaching = true;
                    }
                }
                val
            }
            mir::Rvalue::Aggregate(kind, operands) => {
                if self.read_closure(kind).is_some() {
                    return Val::default();
                }
                let mut inside = Origin::default();
                for operand in operands.iter() {
                    inside.join(&self.operand(operand).all());
                }
                Val::holding(inside)
            }
            mir::Rvalue::Repeat(operand, _) | mir::Rvalue::WrapUnsafeBinder(operand, _) => {
                Val::holding(self.operand(operand).all())
            }
            mir::Rvalue::UnaryOp(_, operand) => self.operand(operand),
            mir::Rvalue::BinaryOp(_, operands) => {
                let mut val = self.operand(&operands.0);
                val.join(&self.operand(&operands.1));
                val
            }
            _ => self.unknown(ty),
        }
    }

    /// Joins `val` into what `target` holds; whether anything grew.
    fn store(&mut self, target: mir::Place<'tcx>, val: &Val) -> bool {
        if let Some((index, rest)) = self.env_split(target) {
            let capture = &mut self.env.as_mut().expect("an environment").captures[index];
            return match capture.class {
                Class::Carried | Class::Own if rest.is_empty() => capture.val.join(val),
                Class::Carried | Class::Own if !derefs(rest) => capture.val.i.join(&val.all()),
                _ => false,
            };
        }
        let projection = target.projection.as_slice();
        match projection.first() {
            None => self.facts[target.local.as_usize()].join(val),
            Some(mir::ProjectionElem::Deref) => {
                let rest = &projection[1..];
                let slots = self.facts[target.local.as_usize()].p.slots.clone();
                let mut grew = false;
                let stored = self.place_ty(target);
                for slot in slots {
                    grew |= match slot {
                        Slot::Local(local) if rest.is_empty() && stored == self.local_ty(local) => {
                            self.facts[local.as_usize()].join(val)
                        }
                        Slot::Local(local) | Slot::Boxed(local) => {
                            self.facts[local.as_usize()].i.join(&val.all())
                        }
                    };
                }
                grew
            }
            Some(_) if derefs(projection) => false,
            Some(_) => self.facts[target.local.as_usize()].i.join(&val.all()),
        }
    }

    /// Whether a value stored at `target` goes into memory the body does not
    /// own: through a pointer that may point outside its variables, or into
    /// the value a consumer runs on.
    fn into_memory(&self, target: mir::Place<'tcx>) -> bool {
        if let Some((index, rest)) = self.env_split(target) {
            let class = self.env.as_ref().map(|env| env.captures[index].class);
            return derefs(rest) || matches!(class, Some(Class::Held { .. } | Class::Holder));
        }
        let projection = target.projection.as_slice();
        match projection.first() {
            None => false,
            Some(mir::ProjectionElem::Deref) => {
                let x = &self.facts[target.local.as_usize()].p;
                derefs(&projection[1..]) || x.facts() || x.slots.is_empty()
            }
            Some(_) => {
                derefs(projection)
                    || self.owners.contains(&target.local)
                    || self.is_env(target.local)
            }
        }
    }

    /// The variables of the body a value stored at `target` goes into.
    fn into_locals(&self, target: mir::Place<'tcx>) -> Vec<mir::Local> {
        if self.env_split(target).is_some() {
            return Vec::new();
        }
        let projection = target.projection.as_slice();
        match projection.first() {
            Some(mir::ProjectionElem::Deref) => self.facts[target.local.as_usize()]
                .p
                .slots
                .iter()
                .map(|slot| slot.local())
                .collect(),
            Some(_) if derefs(projection) || self.owners.contains(&target.local) => Vec::new(),
            _ => vec![target.local],
        }
    }

    /// Whether the code in a value of type `ty` may hand back a pointer of
    /// its own to whoever calls it: a fn item, a closure or a fn pointer
    /// whose result can hold one; or code whose result is not known here (a
    /// `dyn`, a type still to be instantiated). A predicate (`-> bool`), a
    /// `Config::default`, a `|c| c.n += 1` hand back none.
    fn hands_back_own(&self, ty: Ty<'tcx>, depth: usize) -> bool {
        let tcx = self.tcx();
        match *ty.kind() {
            ty::FnDef(..) | ty::FnPtr(..) => {
                let output = tcx.instantiate_bound_regions_with_erased(ty.fn_sig(tcx)).output();
                self.may_point(at_instance(tcx, self.subst, output))
            }
            ty::Closure(_, args) => {
                let sig = args.as_closure().sig();
                let output = tcx.instantiate_bound_regions_with_erased(sig).output();
                self.may_point(at_instance(tcx, self.subst, output))
            }
            ty::CoroutineClosure(..)
            | ty::Coroutine(..)
            | ty::Dynamic(..)
            | ty::Param(_)
            | ty::Alias(..) => true,
            ty::Ref(_, inner, _) | ty::RawPtr(inner, _) => self.hands_back_own(inner, depth + 1),
            ty::Tuple(fields) => {
                depth > 4 || fields.iter().any(|field| self.hands_back_own(field, depth + 1))
            }
            ty::Adt(_, args) => {
                depth > 4 || args.types().any(|inner| self.hands_back_own(inner, depth + 1))
            }
            _ => false,
        }
    }

    /// The code a value of type `ty` has in it: whether some of it is a fn
    /// or a closure of this crate, whose body the census reads on its own
    /// (also inside an adapter: `Filter<I, {closure}>`), and whether some is
    /// not (another crate's fn, a fn pointer, a `dyn`, a type parameter).
    fn code_in(&self, ty: Ty<'tcx>, depth: usize) -> (bool, bool) {
        let both = |tys: &mut dyn Iterator<Item = Ty<'tcx>>| {
            tys.fold((false, false), |seen, ty| {
                let (own, foreign) = self.code_in(ty, depth + 1);
                (seen.0 || own, seen.1 || foreign)
            })
        };
        match *ty.kind() {
            ty::FnDef(def, _) | ty::Closure(def, _) => {
                let own = def.as_local().is_some_and(|def| self.cx.runnable.contains(&def));
                (own, !own)
            }
            ty::FnPtr(..)
            | ty::CoroutineClosure(..)
            | ty::Coroutine(..)
            | ty::Dynamic(..)
            | ty::Param(_)
            | ty::Alias(..) => (false, true),
            _ if depth > 4 => (false, true),
            ty::Ref(_, inner, _) | ty::RawPtr(inner, _) => self.code_in(inner, depth + 1),
            ty::Tuple(fields) => both(&mut fields.iter()),
            ty::Adt(_, args) => both(&mut args.types()),
            _ => (false, false),
        }
    }

    /// The std fn a call runs, when what runs is known to be one: not a
    /// trait method whose impl is not known where it is called.
    fn std_callee(&self, func: &mir::Operand<'tcx>) -> Option<(DefId, GenericArgs<'tcx>)> {
        let tcx = self.tcx();
        let (callee, callee_args) = callee_of(tcx, self.body, func)?;
        let callee_args = at_instance(tcx, self.subst, callee_args);
        let (run, run_args) = match run_instance_by_call(tcx, self.body, callee, callee_args) {
            Some(run) => run,
            None if tcx.trait_of_assoc(callee).is_none() => (callee, callee_args),
            None => return None,
        };
        crate::def_is_in_sysroot_resident_crate(tcx, run).then_some((run, run_args))
    }

    /// Whether the fn a call runs is a safe one: what it hands back is what
    /// its type says it is.
    fn safe_callee(&self, func: &mir::Operand<'tcx>) -> bool {
        self.std_callee(func).is_some_and(|(run, _)| {
            matches!(self.tcx().def_kind(run), DefKind::Fn | DefKind::AssocFn)
                && self.tcx().fn_sig(run).skip_binder().safety().is_safe()
        })
    }

    /// What a std fn can hand back, or put in storage it is given a pointer
    /// to: only what it was GIVEN. The pointers among its arguments, and what
    /// is in the variables of this body they point into; with whether it may
    /// also read a pointer out of memory the body does not own (then what
    /// comes back is of unknown origin, by its type). `None` for any other
    /// callee, and for a call that is also given code that may hand back a
    /// pointer of its own ([`Self::hands_back_own`]).
    fn given(
        &self,
        func: &mir::Operand<'tcx>,
        args: &[rustc_span::Spanned<mir::Operand<'tcx>>],
    ) -> Option<(Origin, bool)> {
        let tcx = self.tcx();
        self.std_callee(func)?;
        let mut mix = Origin::default();
        let mut reads_memory = false;
        for arg in args {
            let ty = at_instance(tcx, self.subst, arg.node.ty(self.body, tcx));
            if self.hands_back_own(ty, 0) {
                return None;
            }
            let val = self.operand(&arg.node);
            if let Some(pointee) = ty.builtin_deref(true) {
                // Memory the body does not own: a pointer kept there that
                // can write is of no origin the body sees; and a std
                // container there may own a consumer's value
                // (`runner.apps[0]`), whatever the path says of the
                // container itself.
                // (One of std's guards borrows what it names: a pointer said
                // to point into a guard's variable, to anything but the
                // guard, points into what the guard borrows.)
                let through_guard = |slot: &Slot| {
                    let held = self.local_ty(slot.local());
                    held != pointee && self.guard(held)
                };
                let unowned = val.p.facts()
                    || val.p.outside
                    || val.p.slots.is_empty()
                    || val.p.slots.iter().any(through_guard);
                let shared = matches!(ty.kind(), ty::Ref(_, _, m) if !m.is_mut());
                let kept = if shared {
                    self.bound().interior || self.view_writes(pointee)
                } else {
                    self.owned_writes(pointee)
                };
                reads_memory |= unowned && (kept || self.owns_root(pointee));
            }
            // (What comes out of a channel is what any holder of its other
            // end put in: of no origin this body sees.)
            let end = ty.builtin_deref(true).unwrap_or(ty);
            reads_memory |= self.channel(end) && self.owned_writes(end);
            // What is IN the variables it points into comes back only as far
            // as the callee can get at it ([`Self::takes`]): `Deref::deref`
            // of a `&guard` hands back a `&App` with which nothing is
            // written.
            // (A variable that owns a consumer's value in a collection:
            // `apps[0]` of a local `Vec<App>`, `Arc::get_mut` of a local
            // `Arc<App>`. Whatever the pointer can take out of it. A guard
            // owns none: what it borrows is reached by the pointer it
            // keeps, which is in its variable for whoever takes it.)
            let owns = |slot: &Slot| {
                let held = self.local_ty(slot.local());
                !self.guard(held) && self.owns_root(held)
            };
            reads_memory |= val.all().slots.iter().any(owns);
            if self.takes(ty) {
                let (content, storage) = self.content(&val.all());
                reads_memory |= storage.iter().any(owns);
                mix.join(&content);
            }
            mix.join(&val.all());
        }
        Some((mix, reads_memory))
    }

    /// `origin` as the pointers of a value of type `ty`.
    fn as_val(&self, origin: &Origin, ty: Ty<'tcx>) -> Val {
        if !self.may_point(ty) {
            Val::default()
        } else if ty.is_box() {
            Val { p: origin.clone(), i: origin.clone() }
        } else if matches!(ty.kind(), ty::Ref(..) | ty::RawPtr(..)) {
            Val::pointing(origin.clone())
        } else {
            Val::holding(origin.clone())
        }
    }

    /// What code the body hands something to may leave in a place of type
    /// `ty`: anything (unknown, by type), or for a std fn what it was given.
    fn left_by(&self, given: &Option<(Origin, bool)>, ty: Ty<'tcx>) -> Val {
        match given {
            Some((mix, reads_memory)) => {
                let mut val = self.as_val(mix, ty);
                if *reads_memory {
                    val.join(&self.unknown(ty));
                }
                val
            }
            None => self.unknown(ty),
        }
    }

    /// The storage `origin` points into may be given, by the code the body
    /// hands the pointer to, whatever that code can leave there.
    fn hand_over(&mut self, origin: &Origin, given: &Option<(Origin, bool)>) -> bool {
        let mut grew = false;
        let mut seen: FxHashSet<Slot> = FxHashSet::default();
        let mut work: Vec<Slot> = origin.slots.clone();
        while let Some(slot) = work.pop() {
            if !seen.insert(slot) {
                continue;
            }
            let local = slot.local();
            let ty = self.local_ty(local);
            // (Only where a pointer can be left: an `Arc<Mutex<App>>` of
            // plain fields takes none.)
            grew |= match slot {
                _ if !self.stores(ty) => false,
                Slot::Local(_) => {
                    let left = self.left_by(given, ty);
                    self.facts[local.as_usize()].join(&left)
                }
                Slot::Boxed(_) => {
                    let left = self.left_by(given, ty.boxed_ty().unwrap_or(ty)).all();
                    self.facts[local.as_usize()].i.join(&left)
                }
            };
            // (And what a pointer kept there points into.)
            let inside = self.facts[local.as_usize()].all().slots;
            work.extend(inside.into_iter().filter(|slot| !seen.contains(slot)));
        }
        grew
    }

    /// Whether code handed `operand` can leave a pointer in what it points
    /// into: not through a `&` of a value with no interior mutability (a
    /// `&` of a channel's end puts in it what it is given), and not where
    /// the pointee can hold none (a `&Cell<u8>`, a `&mut Vec<u8>`).
    fn hands_over(&self, operand: &mir::Operand<'tcx>) -> bool {
        let ty = at_instance(self.tcx(), self.subst, operand.ty(self.body, self.tcx()));
        match *ty.kind() {
            ty::Ref(_, pointee, mutability) => {
                self.may_point(pointee)
                    && (mutability.is_mut()
                        || self.bound().shared_writes(self.tcx(), pointee)
                        || self.channel(pointee))
            }
            ty::RawPtr(pointee, _) => self.may_point(pointee),
            _ => true,
        }
    }

    /// Whether dropping a value of type `ty` runs a `Drop` impl of a type
    /// outside the sysroot that has the value's pointers in hand, and
    /// whether one of another crate's (std's own drop the pointers it holds
    /// and write through none; a trait object's is not known, and counts as
    /// both).
    fn dropped_by(&self, ty: Ty<'tcx>, _depth: usize) -> (bool, bool) {
        (self.drops(ty, false), self.drops(ty, true))
    }

    fn drops(&self, ty: Ty<'tcx>, foreign: bool) -> bool {
        let question = if foreign { ASK_FOREIGN_DROPS } else { ASK_DROPS };
        self.asked(question, ty, None, |this| this.drops_in(ty, foreign))
    }

    fn drops_in(&self, ty: Ty<'tcx>, foreign: bool) -> bool {
        let tcx = self.tcx();
        let any = |tys: &mut dyn Iterator<Item = Ty<'tcx>>| {
            tys.filter(|ty| self.may_point(*ty)).any(|ty| self.drops(ty, foreign))
        };
        match *ty.kind() {
            ty::Adt(adt, args) => {
                let sysroot = crate::def_is_in_sysroot_resident_crate(tcx, adt.did());
                let own = !sysroot && adt.destructor(tcx).is_some();
                if own && (!foreign || !adt.did().is_local()) {
                    return true;
                }
                if sysroot {
                    // (The drop of a guard unlocks: it runs no drop of what
                    // the guard borrows, whatever that is made of.)
                    !self.guard(ty) && any(&mut args.types())
                } else {
                    any(&mut adt
                        .all_fields()
                        .map(|field| at_instance(tcx, None, field.ty(tcx, args).skip_norm_wip())))
                }
            }
            ty::Tuple(fields) => any(&mut fields.iter()),
            ty::Array(inner, _) | ty::Slice(inner) => any(&mut std::iter::once(inner)),
            ty::Closure(_, args) => any(&mut args.as_closure().upvar_tys().iter()),
            ty::Dynamic(..) => true,
            _ => false,
        }
    }

    /// A box the callee made, as the value of a destination of type `ty`: no
    /// pointer into anything that was there. Storage still to be given a
    /// value (`Box::new_uninit()`, as `vec![..]` writes into) holds nothing a
    /// consumer runs on; a `Box::new`, a `Default` or a `Clone` of a box is
    /// the body's own, unless it is a box of the value a consumer runs on
    /// (`let mut app = Box::new(App { .. })`), which is a pointer to that.
    fn fresh_box(&self, func: &mir::Operand<'tcx>, ty: Ty<'tcx>) -> bool {
        let tcx = self.tcx();
        let Some(inner) = ty.boxed_ty() else { return false };
        let Some((callee, callee_args)) = callee_of(tcx, self.body, func) else { return false };
        let uninit = |ty: Ty<'tcx>| matches!(ty.kind(), ty::Adt(adt, _) if tcx.is_lang_item(adt.did(), LangItem::MaybeUninit));
        let storage = match *inner.kind() {
            ty::Array(element, _) | ty::Slice(element) => uninit(element),
            _ => uninit(inner),
        };
        if storage && crate::def_is_in_sysroot_resident_crate(tcx, callee) {
            return true;
        }
        if self.names(inner) {
            return false;
        }
        tcx.is_diagnostic_item(sym::box_new, callee)
            || (tcx.trait_of_assoc(callee).is_some_and(|trait_def| {
                tcx.is_diagnostic_item(sym::Default, trait_def)
                    || tcx.lang_items().clone_trait() == Some(trait_def)
            }) && callee_args.types().next().is_some_and(|this| this.is_box()))
    }

    /// One pass over the body; whether any fact grew.
    fn pass(&mut self) -> bool {
        let mut grew = false;
        let body = self.body;
        for data in body.basic_blocks.iter() {
            for statement in &data.statements {
                let mir::StatementKind::Assign(assign) = &statement.kind else { continue };
                let (target, rvalue) = &**assign;
                let val = self.rvalue(rvalue, self.place_ty(*target));
                grew |= self.store(*target, &val);
                match rvalue {
                    // A closure the census reads may store through a pointer
                    // to one of this body's variables that it captured.
                    mir::Rvalue::Aggregate(kind, operands) if self.read_closure(kind).is_some() => {
                        for operand in operands.iter() {
                            let origin = self.operand(operand).all();
                            grew |= self.hand_over(&origin, &None);
                        }
                    }
                    // The address of a captured pointer's own slot.
                    mir::Rvalue::Ref(_, mir::BorrowKind::Mut { .. }, place)
                    | mir::Rvalue::RawPtr(_, place) => {
                        if let Some((index, [])) = self.env_split(*place) {
                            let unknown = self.unknown(self.place_ty(*place));
                            let capture =
                                &mut self.env.as_mut().expect("an environment").captures[index];
                            if capture.class == Class::Carried {
                                grew |= capture.val.join(&unknown);
                            }
                        }
                    }
                    _ => {}
                }
            }
            let Some(terminator) = &data.terminator else { continue };
            match &terminator.kind {
                TerminatorKind::Call { func, args, destination, .. } => {
                    let ty = self.place_ty(*destination);
                    let given = self.given(func, args);
                    let val = match &given {
                        // (A new box points to storage of its own, and holds
                        // what it was given: `Box::new((&mut self.config,
                        // 0))`.)
                        Some((mix, _)) if self.fresh_box(func, ty) => {
                            Val { p: Origin::default(), i: mix.clone() }
                        }
                        _ => {
                            let mut val = self.left_by(&given, ty);
                            if given.is_some() {
                                if self.safe_callee(func) {
                                    val = self.fit(val, ty);
                                } else {
                                    // (An unsafe fn makes what it hands back
                                    // of what it reads: `ptr::read`.)
                                    val.join(&self.unknown(ty));
                                }
                            }
                            // (A box of the consumer's value, whatever made
                            // it.)
                            if ty.boxed_ty().is_some_and(|inner| self.names(inner)) {
                                val.p.join(&Origin::holder());
                            }
                            val
                        }
                    };
                    grew |= self.store(*destination, &val);
                    grew |= self.hand_over_args(func, args);
                }
                TerminatorKind::TailCall { func, args, .. } => {
                    grew |= self.hand_over_args(func, args);
                }
                TerminatorKind::Yield { resume_arg, .. } => {
                    let val = self.unknown(self.place_ty(*resume_arg));
                    grew |= self.store(*resume_arg, &val);
                }
                TerminatorKind::InlineAsm { operands, .. } => {
                    for operand in operands.iter() {
                        if let mir::InlineAsmOperand::Out { place: Some(place), .. }
                        | mir::InlineAsmOperand::InOut { out_place: Some(place), .. } = operand
                        {
                            let val = self.unknown(self.place_ty(*place));
                            grew |= self.store(*place, &val);
                        }
                    }
                }
                _ => {}
            }
        }
        grew
    }

    fn hand_over_args(
        &mut self,
        func: &mir::Operand<'tcx>,
        args: &[rustc_span::Spanned<mir::Operand<'tcx>>],
    ) -> bool {
        // (Not through a std parameter that only reads: `p.read()`.)
        let reads = callee_of(self.tcx(), self.body, func)
            .map(|(callee, _)| read_only_params(self.tcx(), callee))
            .unwrap_or_default();
        let given = self.given(func, args);
        let mut grew = false;
        for (index, arg) in args.iter().enumerate() {
            if reads.contains(&index) || !self.hands_over(&arg.node) {
                continue;
            }
            let origin = self.operand(&arg.node).all();
            grew |= self.hand_over(&origin, &given);
        }
        grew
    }

    /// What this body says of the captures of each closure written in it.
    fn closures(&self) -> FxHashMap<DefId, Vec<CaptureFact>> {
        let mut closures: FxHashMap<DefId, Vec<CaptureFact>> = FxHashMap::default();
        for statement in self.body.basic_blocks.iter().flat_map(|data| &data.statements) {
            let mir::StatementKind::Assign(assign) = &statement.kind else { continue };
            let mir::Rvalue::Aggregate(kind, operands) = &assign.1 else { continue };
            let Some(def) = self.read_closure(kind) else { continue };
            let facts: Vec<CaptureFact> = operands
                .iter()
                .map(|operand| {
                    let val = self.operand(operand);
                    // (A pointer to one of this body's own variables is a
                    // pointer to nothing a consumer runs on: the closure's
                    // write through it is this body's variable.)
                    let mut val = Val { p: val.p.stripped(), i: val.i.stripped() };
                    // (What a pointer points to in generic code read as
                    // written is not known to be anything: a `&mut T`.)
                    let captured =
                        at_instance(self.tcx(), self.subst, operand.ty(self.body, self.tcx()));
                    if captured
                        .builtin_deref(true)
                        .is_some_and(|inner| inner.has_non_region_param())
                    {
                        val.p.join(&Origin::holder());
                    }
                    let region = operand
                        .place()
                        .filter(|place| !place.projection.is_empty())
                        .filter(|place| {
                            !matches!(self.place_ty(*place).kind(), ty::Ref(..) | ty::RawPtr(..))
                        })
                        .map(|place| match self.region(place) {
                            // (A place whose type generic code has still to
                            // instantiate is not known to be anything.)
                            Region::Apart | Region::Unmatched
                                if self.place_ty(place).has_non_region_param() =>
                            {
                                Region::Holder(String::new())
                            }
                            region => region,
                        });
                    CaptureFact { val, region }
                })
                .collect();
            match closures.get_mut(&def) {
                // (Built in two places: what either says.)
                Some(seen) => {
                    for (seen, fact) in seen.iter_mut().zip(&facts) {
                        seen.val.join(&fact.val);
                        seen.region = match (seen.region.take(), fact.region.clone()) {
                            (Some(a), Some(b)) => Some(a.join(b)),
                            (a, b) => a.or(b),
                        };
                    }
                }
                None => {
                    closures.insert(def, facts);
                }
            }
        }
        closures
    }
}

/// What the parent of the closure `def` says of its captures: `None` when
/// `def` is no closure, or its parent is no body the census reads.
fn parent_facts<'tcx>(
    cx: &Scan<'_, 'tcx>,
    def: LocalDefId,
    subst: Option<GenericArgs<'tcx>>,
    solutions: &mut Solutions<'tcx>,
) -> Option<Vec<CaptureFact>> {
    let tcx = cx.tcx;
    let closure = tcx.type_of(def).instantiate_identity().skip_norm_wip();
    if !matches!(closure.kind(), ty::Closure(..)) {
        return None;
    }
    let parent = tcx.local_parent(def);
    if !cx.runnable.contains(&parent) {
        return None;
    }
    // The parent at this instance: the fn the closure is written in, with
    // the arguments the closure's own begin with; or the closure around it,
    // whose type at those arguments names its own.
    let parent_subst = subst.and_then(|args| {
        let root = tcx.mk_args(args.as_closure().parent_args());
        if !tcx.is_closure_like(parent.to_def_id()) {
            return Some(root);
        }
        let outer = tcx.type_of(parent).instantiate(tcx, root).skip_norm_wip();
        match *at_instance(tcx, None, outer).kind() {
            ty::Closure(_, outer_args) => Some(outer_args),
            _ => None,
        }
    });
    let key = (parent, parent_subst);
    if !solutions.contains_key(&key) {
        cx.hooks.with_local_body(parent, &mut |outer| {
            let _ = solve(cx, outer, parent, parent_subst, solutions);
        });
    }
    solutions.get(&key)?.closures.get(&def.to_def_id()).cloned()
}

/// Solves `body`, read at `subst`: the fixpoint of [`Frame::pass`], kept in
/// `solutions` for the closures written in it.
fn solve<'a, 'b, 'tcx>(
    cx: &'a Scan<'a, 'tcx>,
    body: &'b mir::Body<'tcx>,
    def: LocalDefId,
    subst: Option<GenericArgs<'tcx>>,
    solutions: &mut Solutions<'tcx>,
) -> Frame<'a, 'b, 'tcx> {
    let tcx = cx.tcx;
    let bound = cx.bound;
    let is_closure = tcx.is_closure_like(def.to_def_id()) && body.arg_count >= 1;
    let consumes = (cx.consumes)(def);
    let mut owners: FxHashSet<mir::Local> = (cx.owner_of)(def).into_iter().collect();
    owners.extend(owned_locals(tcx, body, bound, subst, is_closure));
    let mut frame = Frame {
        cx,
        body,
        subst,
        owners,
        env: None,
        facts: vec![Val::default(); body.local_decls.len()],
    };
    // The environment of a closure: each capture, as the parent made it.
    if is_closure {
        let env_ty = frame.local_ty(ENV);
        let (by_ref, env_ty) = match *env_ty.kind() {
            ty::Ref(_, pointee, _) => (true, pointee),
            _ => (false, env_ty),
        };
        if let ty::Closure(_, closure_args) = *env_ty.kind() {
            let parent = parent_facts(cx, def, subst, solutions);
            let captures = closure_args
                .as_closure()
                .upvar_tys()
                .iter()
                .enumerate()
                .map(|(index, upvar)| {
                    let upvar = tcx.erase_and_anonymize_regions(upvar);
                    let fact = parent.as_ref().and_then(|facts| facts.get(index));
                    let val = match fact {
                        Some(fact) => fact.val.clone(),
                        None => frame.unknown(upvar),
                    };
                    let pointer = matches!(upvar.kind(), ty::Ref(..) | ty::RawPtr(..));
                    let names = bound.is_root(upvar) || bound.holds(tcx, upvar);
                    let class = if pointer {
                        Class::Carried
                    } else if names {
                        // A value of the consumer's type (or of one that
                        // holds it), whole or moved in out of a place
                        // (`host.app`): a value a consumer may run on, as
                        // every value of that type is.
                        Class::Holder
                    } else {
                        match fact.map(|fact| &fact.region) {
                            // Part of a value, moved or copied in out of a
                            // place: what that place is, in a closure a
                            // consumer runs in (its environment is then
                            // where the consumer's value lives). In any
                            // other closure it is a copy, or a part nobody
                            // runs on again.
                            Some(Some(region)) if consumes => match region {
                                Region::Field { part } => Class::Held { part: *part },
                                Region::Holder(_) => Class::Holder,
                                Region::Apart | Region::Unmatched => Class::Own,
                            },
                            Some(_) => Class::Own,
                            // No parent says: by type.
                            None if consumes && upvar == bound.field_ty => {
                                Class::Held { part: false }
                            }
                            None if consumes && bound.containers.contains(&upvar) => Class::Holder,
                            None => Class::Own,
                        }
                    };
                    Capture { val, class }
                })
                .collect::<Vec<_>>();
            if captures
                .iter()
                .any(|capture| matches!(capture.class, Class::Held { .. } | Class::Holder))
            {
                frame.owners.insert(ENV);
            }
            frame.env = Some(Env { by_ref, captures });
        }
    }
    let key = (def, subst);
    if let Some(solved) = solutions.get(&key) {
        frame.facts = solved.facts.clone();
        if let Some(env) = frame.env.as_mut() {
            for (capture, val) in env.captures.iter_mut().zip(&solved.captures) {
                capture.val = val.clone();
            }
        }
        return frame;
    }
    // What the body is given is of unknown origin.
    for local in body.args_iter() {
        if frame.is_env(local) {
            continue;
        }
        frame.facts[local.as_usize()] = frame.unknown(frame.local_ty(local));
    }
    // Every fact only grows, on a finite lattice: to the fixpoint. The
    // bound is a guard against a mistake here, and fails closed: every
    // variable is then of unknown origin.
    let mut rounds = 0;
    while frame.pass() {
        rounds += 1;
        if rounds > 8 * body.local_decls.len() + 64 {
            for local in body.local_decls.indices() {
                if !frame.is_env(local) {
                    let unknown = frame.unknown(frame.local_ty(local));
                    frame.facts[local.as_usize()].join(&unknown);
                    frame.facts[local.as_usize()].p.join(&Origin::holder());
                }
            }
            break;
        }
    }
    let captures = frame
        .env
        .as_ref()
        .map(|env| env.captures.iter().map(|capture| capture.val.clone()).collect())
        .unwrap_or_default();
    let solved = Solved { facts: frame.facts.clone(), captures, closures: frame.closures() };
    solutions.insert(key, Rc::new(solved));
    frame
}

/// The locals whose value an rvalue passes on as it is: an operand that is a
/// variable or part of one, and the pointer a reborrow is made through.
fn flows_from<'tcx>(rvalue: &mir::Rvalue<'tcx>) -> Vec<mir::Local> {
    use rustc_middle::mir::visit::Visitor;
    struct Taken(Vec<mir::Local>);
    impl<'tcx> Visitor<'tcx> for Taken {
        fn visit_operand(&mut self, operand: &mir::Operand<'tcx>, _: Location) {
            if let Some(place) =
                operand.place().filter(|place| !derefs(place.projection.as_slice()))
            {
                self.0.push(place.local);
            }
        }
    }
    let mut taken = Taken(Vec::new());
    taken.visit_rvalue(rvalue, Location::START);
    if let mir::Rvalue::Ref(_, _, place) | mir::Rvalue::RawPtr(_, place) = rvalue {
        if let Some(mir::ProjectionElem::Deref) = place.projection.first() {
            taken.0.push(place.local);
        }
    }
    taken.0
}

impl<'a, 'b, 'tcx> Frame<'a, 'b, 'tcx> {
    /// The locals whose value LEAVES the body's sight: an argument or the
    /// callee of a call, what is stored through a pointer into memory the
    /// body does not own, what is returned or yielded; and what those were
    /// made from, and the variables a leaving pointer points into.
    fn leaving(&self) -> FxHashSet<mir::Local> {
        let body = self.body;
        let mut leaves: FxHashSet<mir::Local> = FxHashSet::default();
        leaves.insert(mir::RETURN_PLACE);
        // (to, from): `to` was made from `from`.
        let mut made_from: Vec<(mir::Local, mir::Local)> = Vec::new();
        for data in body.basic_blocks.iter() {
            for statement in &data.statements {
                let mir::StatementKind::Assign(assign) = &statement.kind else { continue };
                let (target, rvalue) = &**assign;
                // (What is computed from a pointer and is none takes it
                // nowhere: a comparison, its metadata, a cast to an integer.)
                if !self.may_point(self.place_ty(*target)) {
                    continue;
                }
                let from = match rvalue {
                    mir::Rvalue::Aggregate(kind, operands) if self.read_closure(kind).is_some() => {
                        // The closure knows its captures; but the variables
                        // a captured pointer points INTO are now its to read.
                        for operand in operands.iter() {
                            for slot in self.operand(operand).all().slots {
                                leaves.insert(slot.local());
                            }
                        }
                        continue;
                    }
                    // (A `&` with which nothing is written, and out of which
                    // no pointer that writes is copied, takes nothing
                    // anywhere.)
                    mir::Rvalue::Ref(_, kind, _)
                        if !matches!(kind, mir::BorrowKind::Mut { .. })
                            && !self.carries(self.place_ty(*target)) =>
                    {
                        continue;
                    }
                    _ => {
                        let mut from = flows_from(rvalue);
                        // A value loaded through a pointer to a variable was
                        // made from that variable.
                        if let mir::Rvalue::Use(
                            mir::Operand::Copy(place) | mir::Operand::Move(place),
                            _,
                        )
                        | mir::Rvalue::CopyForDeref(place) = rvalue
                        {
                            if let Some(mir::ProjectionElem::Deref) = place.projection.first() {
                                if self.env_split(*place).is_none() {
                                    let through = &self.facts[place.local.as_usize()].p;
                                    from.extend(through.slots.iter().map(|slot| slot.local()));
                                }
                            }
                        }
                        from
                    }
                };
                if self.into_memory(*target) {
                    leaves.extend(from.iter().copied());
                }
                for into in self.into_locals(*target) {
                    made_from.extend(from.iter().map(|from| (into, *from)));
                }
            }
            let base = |operand: &mir::Operand<'tcx>| {
                operand
                    .place()
                    .filter(|place| !derefs(place.projection.as_slice()))
                    .map(|place| place.local)
            };
            match data.terminator.as_ref().map(|terminator| &terminator.kind) {
                Some(
                    TerminatorKind::Call { func, args, .. }
                    | TerminatorKind::TailCall { func, args, .. },
                ) => {
                    leaves.extend(base(func));
                    // (Not into a std fn that only reads through it and
                    // hands no pointer back: `p.read()`, `ptr::eq(p, q)`.)
                    let reads = callee_of(self.tcx(), self.body, func)
                        .map(|(callee, _)| read_only_params(self.tcx(), callee))
                        .unwrap_or_default();
                    // (Nor through a `&` the callee can write nothing with.)
                    leaves.extend(
                        args.iter()
                            .enumerate()
                            .filter(|(index, _)| !reads.contains(index))
                            .filter(|(_, arg)| {
                                let ty = arg.node.ty(self.body, self.tcx());
                                self.carries(at_instance(self.tcx(), self.subst, ty))
                            })
                            .filter_map(|(_, arg)| base(&arg.node)),
                    );
                }
                Some(TerminatorKind::Yield { value, .. }) => leaves.extend(base(value)),
                // A value whose drop runs a `Drop` impl with its pointers in
                // hand (a guard around a pointer to part of the field, whose
                // `drop` writes through it: its type says nothing of that).
                Some(TerminatorKind::Drop { place, .. }) => {
                    if !derefs(place.projection.as_slice())
                        && self.dropped_by(self.place_ty(*place), 0).0
                    {
                        leaves.insert(place.local);
                    }
                }
                Some(TerminatorKind::InlineAsm { operands, .. }) => {
                    for operand in operands.iter() {
                        if let mir::InlineAsmOperand::In { value, .. }
                        | mir::InlineAsmOperand::InOut { in_value: value, .. } = operand
                        {
                            leaves.extend(base(value));
                        }
                    }
                }
                _ => {}
            }
        }
        loop {
            let mut grew = false;
            for &(to, from) in &made_from {
                if leaves.contains(&to) {
                    grew |= leaves.insert(from);
                }
            }
            let pointed: Vec<mir::Local> = leaves
                .iter()
                .flat_map(|local| self.facts[local.as_usize()].all().slots)
                .map(|slot| slot.local())
                .collect();
            for local in pointed {
                grew |= leaves.insert(local);
            }
            if !grew {
                break;
            }
        }
        leaves
    }
}

impl<'a, 'b, 'tcx> Frame<'a, 'b, 'tcx> {
    /// Whether a value of type `ty` has a place in it where code with a
    /// pointer to it could LEAVE a pointer: not the pointer an `Rc`, an
    /// `Arc` or a `Box` is itself (an `Arc<Mutex<App>>` of plain fields has
    /// none).
    fn stores(&self, ty: Ty<'tcx>) -> bool {
        self.may_point(ty) && self.asked(ASK_STORES, ty, None, |this| this.stores_in(ty))
    }

    fn stores_in(&self, ty: Ty<'tcx>) -> bool {
        let tcx = self.tcx();
        match *ty.kind() {
            ty::Tuple(fields) => fields.iter().any(|field| self.stores(field)),
            ty::Array(inner, _) | ty::Slice(inner) | ty::Pat(inner, _) => self.stores(inner),
            ty::Adt(_, args) if ty.is_box() => {
                args.types().next().is_some_and(|inner| self.stores(inner))
            }
            ty::Adt(adt, args) if crate::def_is_in_sysroot_resident_crate(tcx, adt.did()) => {
                args.regions().next().is_some()
                    || matches!(tcx.item_name(adt.did()).as_str(), "NonNull" | "Unique" | "Pin")
                    || args.types().any(|inner| self.stores(inner))
            }
            ty::Adt(adt, args) => adt.all_fields().any(|field| {
                let field = at_instance(tcx, None, field.ty(tcx, args).skip_norm_wip());
                self.stores(field)
            }),
            _ => true,
        }
    }

    /// The facts of every variable, for whoever debugs a binding
    /// (`TRUST_WRITER_ORIGINS_DUMP=<part of the body's path>`).
    fn dump(&self, def: LocalDefId, leaves: &FxHashSet<mir::Local>) {
        static DUMP_FILTER: std::sync::OnceLock<Option<String>> = std::sync::OnceLock::new();
        let Some(wanted) = DUMP_FILTER
            .get_or_init(|| {
                std::env::var_os("TRUST_WRITER_ORIGINS_DUMP")
                    .map(|v| v.to_string_lossy().into_owned())
            })
            .as_deref()
        else {
            return;
        };
        let path = self.tcx().def_path_str(def);
        if !path.contains(wanted) {
            return;
        }
        eprintln!("writer origins of `{path}` at {:?}", self.subst);
        let mut owners: Vec<_> = self.owners.iter().copied().collect();
        owners.sort();
        eprintln!("  a consumer may run on: {owners:?}");
        for (local, val) in self.facts.iter().enumerate() {
            let local = mir::Local::from_usize(local);
            if *val != Val::default() || leaves.contains(&local) {
                let leaves = if leaves.contains(&local) { " LEAVES" } else { "" };
                eprintln!(
                    "  {local:?}: {}{leaves}\n    p {:?}\n    i {:?}",
                    self.local_ty(local),
                    val.p,
                    val.i
                );
            }
        }
    }
}

/// Every site in `body`, read at the instance `subst`, that may write the
/// bound field (module docs).
///
/// A write is judged where it is by [`Frame::region`]. A pointer to the field
/// whose value leaves ([`Frame::leaving`]) is a site at the borrow that made
/// it (in a closure, where it reads the captured pointer), and where it is
/// handed on when that is elsewhere: every write through it is then someone
/// else's. A pointer that reaches a value holding the field is a site where
/// it is handed to code whose writes the census cannot find where they are
/// made: the sysroot's (but for the accessors [`std_passes_on`] names),
/// another crate's fn of the value's own type or generic code whose body
/// writes through it ([`writes_through`]), a call the census cannot resolve
/// that may run a fn not the crate's own, memory. A local callee is not one:
/// its body is read on its own, at the instance called.
pub(super) fn scan_writes<'tcx>(
    cx: &Scan<'_, 'tcx>,
    body: &mir::Body<'tcx>,
    body_def: LocalDefId,
    subst: Option<GenericArgs<'tcx>>,
    solutions: &mut Solutions<'tcx>,
    lends: &mut Lends<'tcx>,
    writes: &mut Vec<Write<'tcx>>,
) {
    let tcx = cx.tcx;
    let frame = solve(cx, body, body_def, subst, solutions);
    let leaves = frame.leaving();
    frame.dump(body_def, &leaves);
    // The pointers loaded out of a box in the field: no borrow of the body's
    // made them, so a borrow through one is the borrow that leaves.
    let loaded: FxHashSet<mir::Local> = body
        .basic_blocks
        .iter()
        .flat_map(|data| &data.statements)
        .filter_map(|statement| match &statement.kind {
            mir::StatementKind::Assign(assign) => match &assign.1 {
                mir::Rvalue::Cast(_, mir::Operand::Copy(place) | mir::Operand::Move(place), _)
                    if assign.0.projection.is_empty()
                        && box_loaded_from(tcx, body, *place).is_some() =>
                {
                    Some(assign.0.local)
                }
                _ => None,
            },
            _ => None,
        })
        .collect();
    // The variables a consumer may run on: every one of the consumer's type,
    // or of a type that holds it. `held`: which of them has a value where
    // each block begins (a whole value assigned to one that has one is a
    // whole NEW value: W2). A parameter has one on entry; storage that ends
    // or starts has none.
    let mut owned: Vec<mir::Local> =
        frame.owners.iter().copied().filter(|local| !frame.is_env(*local)).collect();
    owned.sort();
    let owned = &owned;
    let slot_of = |local: mir::Local| owned.binary_search(&local).ok();
    let whole = |place: mir::Place<'tcx>| {
        if place.projection.is_empty() { slot_of(place.local) } else { None }
    };
    // A variable whose one value is another's, moved: the temporary a method
    // call's receiver is moved into.
    let mut assigned: FxHashMap<mir::Local, (usize, Option<mir::Local>)> = FxHashMap::default();
    for data in body.basic_blocks.iter() {
        for statement in &data.statements {
            let mir::StatementKind::Assign(assign) = &statement.kind else { continue };
            let (target, rvalue) = &**assign;
            if whole(*target).is_some() {
                let entry = assigned.entry(target.local).or_default();
                entry.0 += 1;
                entry.1 = match rvalue {
                    mir::Rvalue::Use(mir::Operand::Move(from), _) => from.as_local(),
                    _ => None,
                };
            }
        }
        if let Some(mir::Terminator { kind: TerminatorKind::Call { destination, .. }, .. }) =
            &data.terminator
        {
            if whole(*destination).is_some() {
                assigned.entry(destination.local).or_default().0 += 2;
            }
        }
    }
    let assigned = &assigned;
    let moved_from = |local: mir::Local| match assigned.get(&local) {
        Some((1, from)) => *from,
        _ => None,
    };
    // A consumer of the field that is handed THIS variable's value by value
    // and hands one back (`app = app.on_wake(wake)` with `self: Box<Self>`):
    // what it does to the value is in its arms, and an arm that hands back
    // another is reported there (`same`, below).
    let handed_to_consumer = |func: &mir::Operand<'tcx>,
                              args: &[rustc_span::Spanned<mir::Operand<'tcx>>]|
     -> Vec<mir::Local> {
        let consumer = callee_of(tcx, body, func).is_some_and(|(callee, callee_args)| {
            let callee_args = at_instance(tcx, subst, callee_args);
            let run =
                run_instance_by_call(tcx, body, callee, callee_args).map_or(callee, |(run, _)| run);
            (cx.consumer)(run)
        });
        if !consumer {
            return Vec::new();
        }
        args.iter()
            .filter_map(|arg| arg.node.place())
            .filter(|place| whole(*place).is_some())
            .map(|place| moved_from(place.local).unwrap_or(place.local))
            .collect()
    };
    // (The variables whose one value is such a call's result, each with the
    // variables the consumer was handed.)
    let mut handed_back: FxHashMap<mir::Local, Vec<mir::Local>> = FxHashMap::default();
    for data in body.basic_blocks.iter() {
        if let Some(mir::Terminator {
            kind: TerminatorKind::Call { func, args, destination, .. },
            ..
        }) = &data.terminator
        {
            if whole(*destination).is_some()
                && assigned.get(&destination.local).is_some_and(|(count, _)| *count == 2)
            {
                let given = handed_to_consumer(func, args);
                if !given.is_empty() {
                    handed_back.insert(destination.local, given);
                }
            }
        }
    }
    let handed_back = &handed_back;
    // A consumer that is handed its value by value and hands one back: the
    // value handed back is the one it was handed unless an assignment on
    // the way gives another, and that assignment is a whole new value, in
    // the arm that makes it. `same`: the variables every assignment of which
    // moves the handed value on.
    let returns_value = (cx.consumer)(body_def.to_def_id())
        && slot_of(mir::RETURN_PLACE).is_some()
        && body.args_iter().any(|arg| slot_of(arg).is_some());
    let mut same: FxHashSet<mir::Local> =
        if returns_value { owned.iter().copied().collect() } else { FxHashSet::default() };
    while returns_value {
        let mut shrank = false;
        for data in body.basic_blocks.iter() {
            for statement in &data.statements {
                let mir::StatementKind::Assign(assign) = &statement.kind else { continue };
                let (target, rvalue) = &**assign;
                if !target.projection.is_empty() || !same.contains(&target.local) {
                    continue;
                }
                let moved_on = matches!(rvalue,
                    mir::Rvalue::Use(mir::Operand::Move(from) | mir::Operand::Copy(from), _)
                        if from.projection.is_empty() && same.contains(&from.local));
                if !moved_on {
                    shrank |= same.remove(&target.local);
                }
            }
            if let Some(mir::Terminator {
                kind: TerminatorKind::Call { destination, .. }, ..
            }) = &data.terminator
            {
                if destination.projection.is_empty() {
                    shrank |= same.remove(&destination.local);
                }
            }
        }
        if !shrank {
            break;
        }
    }
    let same = &same;
    let hands_back_new = |target: mir::Place<'tcx>, from: Option<mir::Local>| {
        returns_value
            && target.as_local() == Some(mir::RETURN_PLACE)
            && !from.is_some_and(|from| same.contains(&from))
    };
    // A statement's effect on `held`; whether it gives a variable that has a
    // value a whole new one.
    let flow_statement = |held: &mut [bool], statement: &mir::Statement<'tcx>| -> bool {
        match &statement.kind {
            mir::StatementKind::StorageLive(local) | mir::StatementKind::StorageDead(local) => {
                if let Some(at) = slot_of(*local) {
                    held[at] = false;
                }
                false
            }
            mir::StatementKind::Assign(assign) => {
                let (target, rvalue) = &**assign;
                let Some(at) = whole(*target) else { return false };
                let again = std::mem::replace(&mut held[at], true);
                // (A `Box` is not `Copy`: a copy of one is the pointer the
                // compiler loads to dereference it, no new value.)
                let loads = matches!(rvalue, mir::Rvalue::Use(mir::Operand::Copy(_), _))
                    && frame.local_ty(target.local).is_box();
                // (What a consumer hands back after being handed this
                // variable's value.)
                let back = matches!(rvalue, mir::Rvalue::Use(mir::Operand::Move(from), _)
                    if from.as_local().and_then(|from| handed_back.get(&from))
                        .is_some_and(|given| given.contains(&target.local)));
                again && !loads && !back
            }
            _ => false,
        }
    };
    let flow_terminator = |held: &mut [bool], terminator: &mir::Terminator<'tcx>| -> bool {
        let TerminatorKind::Call { func, args, destination, .. } = &terminator.kind else {
            return false;
        };
        let Some(at) = whole(*destination) else { return false };
        let again = std::mem::replace(&mut held[at], true);
        again && !handed_to_consumer(func, args).contains(&destination.local)
    };
    let mut entry: Vec<Option<Vec<bool>>> = vec![None; body.basic_blocks.len()];
    if !owned.is_empty() {
        entry[mir::START_BLOCK.as_usize()] = Some(
            owned
                .iter()
                .map(|local| local.as_usize() >= 1 && local.as_usize() <= body.arg_count)
                .collect(),
        );
        loop {
            let mut grew = false;
            for (block, data) in mir::traversal::reverse_postorder(body) {
                let Some(mut held) = entry[block.as_usize()].clone() else { continue };
                for statement in &data.statements {
                    flow_statement(&mut held, statement);
                }
                let Some(terminator) = &data.terminator else { continue };
                flow_terminator(&mut held, terminator);
                for successor in terminator.successors() {
                    match &mut entry[successor.as_usize()] {
                        Some(at) => {
                            for (at, out) in at.iter_mut().zip(&held) {
                                if *out && !*at {
                                    *at = true;
                                    grew = true;
                                }
                            }
                        }
                        at @ None => {
                            *at = Some(held.clone());
                            grew = true;
                        }
                    }
                }
            }
            if !grew {
                break;
            }
        }
    }
    let replaces = |place: mir::Place<'tcx>| {
        let ty = at_instance(tcx, subst, body.local_decls[place.local].ty);
        format!("writes a whole `{ty}` holding")
    };
    // What a write to `place` is.
    let written = |place: mir::Place<'tcx>| {
        if place.projection.is_empty() {
            return None;
        }
        match frame.region(place) {
            Region::Field { part: false } => Some("writes".to_owned()),
            Region::Field { part: true } => Some("writes part of".to_owned()),
            Region::Holder(verb) => Some(verb),
            Region::Apart | Region::Unmatched => None,
        }
    };
    // Every pointer in the value an operand passes on, and those the code it
    // is handed to can get at through it.
    let reachable = |operand: &mir::Operand<'tcx>| {
        let ty = at_instance(tcx, subst, operand.ty(body, tcx));
        let mut all = frame.operand(operand).all();
        if frame.takes(ty) {
            all.join(&frame.content(&all).0.stripped());
        }
        all
    };
    // What that value may reach; and whether it is itself a pointer that
    // reaches a value holding the field.
    let reach = |operand: &mir::Operand<'tcx>| {
        let ty = at_instance(tcx, subst, operand.ty(body, tcx));
        let pointer = matches!(ty.kind(), ty::Ref(..) | ty::RawPtr(..));
        (reachable(operand).reaches(), pointer && frame.operand(operand).p.reaches())
    };
    let captured_pointer = |place: mir::Place<'tcx>| {
        let (index, rest) = frame.env_split(place)?;
        let capture = &frame.env.as_ref()?.captures[index];
        (rest.is_empty() && capture.class == Class::Carried && capture.val.all().field())
            .then(|| !capture.val.all().whole)
    };
    let nothing_held = vec![true; owned.len()];
    for (block, data) in body.basic_blocks.iter_enumerated() {
        let mut site = |span: Span, verb: String| {
            writes.push(Write {
                def: body_def,
                block,
                cleanup: data.is_cleanup,
                span,
                verb,
                subst,
            });
        };
        let mut held = entry[block.as_usize()].clone().unwrap_or_else(|| nothing_held.clone());
        // Whether a pointer to the field was made, or read out of the
        // environment, in this block and reported there.
        let mut made_here = false;
        for statement in &data.statements {
            let span = statement.source_info.span;
            if let mir::StatementKind::SetDiscriminant { place, .. } = &statement.kind {
                if let Some(verb) = written(**place) {
                    site(span, verb);
                }
            }
            let again = flow_statement(&mut held, statement);
            let mir::StatementKind::Assign(assign) = &statement.kind else { continue };
            let (target, rvalue) = &**assign;
            let from = match rvalue {
                mir::Rvalue::Use(mir::Operand::Move(from) | mir::Operand::Copy(from), _) => {
                    from.as_local()
                }
                _ => None,
            };
            let again = again || hands_back_new(*target, from);
            if let Some(verb) = written(*target).or_else(|| again.then(|| replaces(*target))) {
                site(span, verb);
            }
            // Where the value goes: into a variable (and whether that leaves),
            // or through a pointer into memory the body does not own.
            let into_memory = frame.into_memory(*target);
            let target_leaves = into_memory
                || frame.into_locals(*target).iter().any(|local| leaves.contains(local));
            // A pointer to a value holding the field, stored through a
            // pointer (`vec![&mut self.config]` writes it into the vector's
            // buffer): whoever reads it back out can write through it. With
            // what it points into, as far as a reader can get at that.
            let stored_ty = frame.place_ty(*target);
            let stored = if frame.may_point(stored_ty) {
                let mut stored = frame.rvalue(rvalue, stored_ty).all();
                if frame.takes(stored_ty) {
                    stored.join(&frame.content(&stored).0.stripped());
                }
                stored
            } else {
                Origin::default()
            };
            if into_memory && stored.reaches() {
                site(span, "puts in memory a `&mut` reaching".to_owned());
            }
            // One cast to another pointee type, handed back: no type tells
            // the caller what it is.
            if target.local == mir::RETURN_PLACE && stored.recast {
                site(
                    span,
                    "hands back, cast to another type, a pointer into a value holding".to_owned(),
                );
            }
            match rvalue {
                // A captured pointer to the field that this closure hands
                // on: the borrow is its parent's, and no site there.
                mir::Rvalue::Use(mir::Operand::Copy(place) | mir::Operand::Move(place), _)
                | mir::Rvalue::CopyForDeref(place) => {
                    if let Some(part) = captured_pointer(*place) {
                        if target_leaves {
                            let of = if part { " part of" } else { "" };
                            site(span, format!("hands on a pointer it captured to{of}"));
                            made_here = true;
                        }
                    } else if (into_memory || target.local == mir::RETURN_PLACE)
                        && stored.field()
                        && !made_here
                    {
                        // A pointer to the field made elsewhere (in another
                        // arm), put where the body does not follow it.
                        let of = if stored.whole { "" } else { " part of" };
                        site(span, format!("hands on a pointer to{of}"));
                    }
                }
                mir::Rvalue::Ref(_, _, borrowed) | mir::Rvalue::RawPtr(_, borrowed) => {
                    let mutable = !matches!(
                        rvalue,
                        mir::Rvalue::Ref(_, kind, _) if !matches!(kind, mir::BorrowKind::Mut { .. })
                    );
                    // The address of the slot a captured pointer to the
                    // field sits in (`&mut h` of a captured `h`): the
                    // pointer can be read back out of it anywhere.
                    if let (true, Some(part)) = (mutable, captured_pointer(*borrowed)) {
                        let of = if part { " part of" } else { "" };
                        site(span, format!("hands on a pointer it captured to{of}"));
                        made_here = true;
                        continue;
                    }
                    if !frame.can_write(*borrowed, mutable) || !target_leaves {
                        continue;
                    }
                    // A reborrow of a pointer to the field is no new borrow:
                    // the one that made that pointer is the site. (A pointer
                    // loaded out of a box in the field has none. One that may
                    // ALSO point to a value holding the field is judged by
                    // its path: a borrow of the field through it is a borrow
                    // of the field.)
                    let through =
                        matches!(borrowed.projection.first(), Some(mir::ProjectionElem::Deref))
                            && frame.env_split(*borrowed).is_none();
                    let base = &frame.facts[borrowed.local.as_usize()].p;
                    if through && base.field() && !base.lent && !loaded.contains(&borrowed.local) {
                        continue;
                    }
                    // A `&mut` of the field or of part of it that leaves the
                    // body's sight: every write through it is made elsewhere.
                    if let Region::Field { part } = frame.region(*borrowed) {
                        let of = if part { " part of" } else { "" };
                        let verb = match rvalue {
                            mir::Rvalue::RawPtr(..) => format!("takes a raw pointer to{of}"),
                            _ if mutable => format!("takes a `&mut` of{of}"),
                            _ => format!("takes a `&` of{of} the interior-mutable"),
                        };
                        site(span, verb);
                        made_here = true;
                    }
                }
                _ => {}
            }
        }
        let Some(terminator) = &data.terminator else { continue };
        let span = terminator.source_info.span;
        let again = flow_terminator(&mut held, terminator);
        let (func, args, destination) = match &terminator.kind {
            TerminatorKind::Call { func, args, destination, .. } => {
                (func, args, Some(*destination))
            }
            TerminatorKind::TailCall { func, args, .. } => (func, args, None),
            // A value that reaches a holder, dropped by a `Drop` impl of
            // another crate's: its body is not read here.
            TerminatorKind::Drop { place, .. } => {
                let ty = frame.place_ty(*place);
                if frame.may_point(ty)
                    && frame.val(*place).all().reaches()
                    && frame.dropped_by(ty, 0).1
                {
                    site(span, format!("lends the drop of a `{ty}` a `&mut` reaching"));
                }
                continue;
            }
            _ => continue,
        };
        if let Some(destination) = destination {
            let again = again || hands_back_new(destination, None);
            if let Some(verb) =
                written(destination).or_else(|| again.then(|| replaces(destination)))
            {
                site(span, verb);
            }
        }
        let callee = callee_of(tcx, body, func);
        let reads = callee.map(|(callee, _)| read_only_params(tcx, callee)).unwrap_or_default();
        let arg_ty = |arg: &rustc_span::Spanned<mir::Operand<'tcx>>| {
            at_instance(tcx, subst, arg.node.ty(body, tcx))
        };
        // (Dropping a pointer, or forgetting it, does nothing to what it
        // points to.)
        let discards = callee.is_some_and(|(callee, _)| {
            tcx.is_diagnostic_item(sym::mem_forget, callee)
                || tcx.is_diagnostic_item(sym::mem_drop, callee)
        });
        for (index, arg) in args.iter().enumerate() {
            // A captured pointer to the field handed over as it sits in the
            // environment.
            if let Some(part) = arg.node.place().and_then(|place| captured_pointer(place)) {
                let of = if part { " part of" } else { "" };
                site(span, format!("hands on a pointer it captured to{of}"));
                made_here = true;
                continue;
            }
            // A pointer to the field made elsewhere (in another arm) and
            // handed on here, itself or in storage the callee can get at:
            // the writes through it are made from here. (What `format_args!`
            // builds shows the field by `&` to a `fmt` impl.)
            let ty = arg_ty(arg);
            let origin = reachable(&arg.node);
            let leaves = !reads.contains(&index)
                && !discards
                && frame.carries(ty)
                && (matches!(ty.kind(), ty::Ref(..) | ty::RawPtr(..)) || frame.owned_writes(ty));
            if origin.field() && !made_here && leaves {
                let of = if origin.whole { "" } else { " part of" };
                site(span, format!("hands on a pointer to{of}"));
            }
        }
        // A pointer to a value holding the field, lent to code whose writes
        // the census cannot find where they are made.
        let mut passed: Vec<usize> = Vec::new();
        // (A value built around one, or a pointer to a variable holding one.)
        let mut carried: Vec<usize> = Vec::new();
        // One cast to another pointee type: no type tells ANY callee what it
        // is given.
        let mut recast = false;
        for (index, arg) in args.iter().enumerate() {
            recast |= frame.operand(&arg.node).all().recast;
            match reach(&arg.node) {
                (_, true) => passed.push(index),
                (true, false) => carried.push(index),
                (false, false) => {}
            }
        }
        if passed.is_empty() && carried.is_empty() {
            continue;
        }
        // A call the census cannot resolve to one body (through a fn
        // pointer, a `dyn Fn`, a callable of a type still to be
        // instantiated) may run any fn the crate uses as a VALUE: it is a
        // site when one of those that is not the crate's own takes a type
        // one of the arguments has (`let take: fn(&mut Config) -> Config =
        // mem::take; take(&mut self.config)`; `apply(mem::take, ..)`).
        // Whatever kind of pointer the value was made into.
        let may_run_foreign = |tupled: bool| {
            let mut given: Vec<Ty<'tcx>> = Vec::new();
            for &index in passed.iter().chain(&carried) {
                let ty = arg_ty(&args[index]);
                match *ty.kind() {
                    // (The Fn traits take their arguments as one tuple.)
                    ty::Tuple(fields) if tupled => given.extend(fields.iter()),
                    _ => given.push(ty),
                }
            }
            cx.foreign_inputs.contains(&None)
                || given.iter().any(|ty| cx.foreign_inputs.contains(&Some(*ty)))
        };
        let Some((callee, callee_args)) = callee else {
            if recast || may_run_foreign(false) {
                site(span, "lends a call through a fn pointer a `&mut` reaching".to_owned());
            }
            continue;
        };
        let callee_args = at_instance(tcx, subst, callee_args);
        // The body that RUNS is judged. A local one is read on its own, at
        // the instance called: its writes are sites where they are.
        let resolved = run_instance_by_call(tcx, body, callee, callee_args);
        let mut run = resolved.map_or(callee, |(run, _)| run);
        let mut run_args = resolved.map_or(callee_args, |(_, run_args)| run_args);
        let of_trait = tcx.trait_of_assoc(callee);
        let lang = tcx.lang_items();
        let calls = of_trait.is_some_and(|of| {
            [lang.fn_trait(), lang.fn_mut_trait(), lang.fn_once_trait()].contains(&Some(of))
        });
        // A call through the Fn traits runs what the callee IS: a fn item
        // (the fn it names), a closure, or a value whose target is not known
        // here.
        let mut unresolved = resolved.is_none() && of_trait.is_some();
        if calls {
            let callable =
                callee_args.types().next().map(|this| this.peel_refs()).map(|this| *this.kind());
            match callable {
                // (A fn that is not the crate's own, called with the
                // pointer in hand: as handing it the pointer.)
                Some(ty::FnDef(def, _))
                    if !def.as_local().is_some_and(|def| cx.runnable.contains(&def)) =>
                {
                    site(span, format!("lends `{}` a `&mut` reaching", tcx.def_path_str(def)));
                    continue;
                }
                Some(ty::FnDef(def, def_args)) => {
                    run = def;
                    run_args = def_args.skip_binder();
                    unresolved = false;
                }
                Some(ty::Closure(def, def_args)) => {
                    run = def;
                    run_args = def_args;
                    unresolved = false;
                }
                _ => {
                    if recast || may_run_foreign(true) {
                        site(
                            span,
                            "lends a call through a fn pointer a `&mut` reaching".to_owned(),
                        );
                    }
                    continue;
                }
            }
        }
        let name = || tcx.def_path_str(run);
        // (One cast to another pointee type is a site whoever is handed it:
        // no type tells the callee what it was given.)
        if recast {
            site(span, format!("lends `{}` a `&mut` reaching", name()));
            continue;
        }
        if run.as_local().is_some_and(|run| cx.runnable.contains(&run)) {
            continue;
        }
        // A method of a trait whose impl is not known here (a `dyn`, a type
        // still to be instantiated). Of a trait of the crate: every impl is
        // a body of the crate, read on its own. Of any other trait: the
        // impl that runs may be another crate's, and no body says what it
        // writes.
        if unresolved {
            let local_trait = of_trait.is_some_and(|of| of.is_local());
            let lent = passed.iter().any(|&index| !declared_read_only(tcx, callee, index))
                || !carried.is_empty();
            if !local_trait && lent {
                site(span, format!("lends `{}` a `&mut` reaching", name()));
            }
            continue;
        }
        let sysroot = crate::def_is_in_sysroot_resident_crate(tcx, run);
        let is_fn = matches!(tcx.def_kind(run), DefKind::Fn | DefKind::AssocFn);
        // The drop of a value, called as the fn it is (the compiler's own,
        // for a box it emptied): as a drop is judged.
        if of_trait.is_some_and(|of| lang.drop_trait() == Some(of)) {
            let dropped = args.first().and_then(|arg| arg_ty(arg).builtin_deref(true));
            if let Some(dropped) = dropped.filter(|dropped| frame.dropped_by(*dropped, 0).1) {
                site(span, format!("lends the drop of a `{dropped}` a `&mut` reaching"));
            }
            continue;
        }
        // (A parameter declared `&T` or `*const T` writes nothing, unless
        // what it is given has interior mutability: `RefCell::replace`.)
        let cell = |index: usize| {
            arg_ty(&args[index])
                .builtin_deref(true)
                .is_some_and(|inner| cx.bound.shared_writes(tcx, inner))
        };
        let can_write = |index: usize| !declared_read_only(tcx, run, index) || cell(index);
        // A std fn that only hands on what it is given (`as_mut`,
        // `deref_mut`, `iter_mut`, `next`, `borrow_mut`, `lock`, `unwrap`:
        // [`std_passes_on`], a list) writes nothing: what is done with what
        // it hands back is judged where it is done. Any other std fn handed
        // the pointer may write through it.
        let std_fn = sysroot && frame.std_callee(func).is_some();
        let passes_on = std_fn && std_passes_on(tcx, run);
        // Another crate's fn that takes the value's own type (a setter of a
        // dependency's type the path passes) can write any field of it,
        // whether or not its body came with the crate. One that takes a
        // type parameter is read ([`writes_through`]).
        let lends_it = !discards
            && !passes_on
            && passed.iter().any(|&index| {
                can_write(index)
                    && !reads.contains(&index)
                    && (sysroot
                        || (is_fn && !generic_parameter(tcx, run, index))
                        || (generic_parameter(tcx, run, index)
                            && writes_through(
                                tcx,
                                cx.hooks,
                                cx.runnable,
                                lends,
                                run,
                                run_args,
                                Given::Arg(index),
                            )))
            });
        let carries_it = if carried.is_empty() {
            false
        } else if tcx.is_diagnostic_item(sym::mem_forget, run) {
            false
        } else if tcx.is_diagnostic_item(sym::mem_drop, run) {
            // As the drop it is.
            carried.iter().any(|&index| frame.dropped_by(arg_ty(&args[index]), 0).1)
        } else if sysroot {
            // std writes through a pointer inside a value with code it is
            // handed (`Some(slot).map(mem::take)`), or where it keeps the
            // value (`write!(&mut out, ..)`). A fn that only hands it on
            // ([`std_passes_on`]) or runs a closure of the crate on it (read
            // on its own) writes nothing the census does not see where it is
            // written.
            let (local_code, foreign_code) = args.iter().fold((false, false), |seen, arg| {
                let (own, foreign) = frame.code_in(arg_ty(arg), 0);
                (seen.0 || own, seen.1 || foreign)
            });
            foreign_code || !(local_code || passes_on)
        } else {
            // Another crate's fn that takes the value as it is; or its
            // generic code, read with the wrapper as its argument.
            let generic = is_fn && tcx.generics_of(run).requires_monomorphization(tcx);
            carried.iter().any(|&index| {
                !generic
                    || writes_through(
                        tcx,
                        cx.hooks,
                        cx.runnable,
                        lends,
                        run,
                        run_args,
                        Given::Arg(index),
                    )
            })
        };
        if lends_it || carries_it {
            site(span, format!("lends `{}` a `&mut` reaching", name()));
        }
    }
}
