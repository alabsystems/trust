//! Trust (r20, 2026-10-07): the TRAIT-IMPL SURFACE of a local type, for
//! `ty_reaches_foreign_user_code`.
//!
//! That walk answered `false` for a local ADT with no foreign field, and so it
//! never asked what code a sysroot callee instantiated at that type can run
//! through the type's IMPLS. A sysroot generic at `L` runs `L`'s impls of the
//! sysroot traits it is bounded by, and through them every type those impls name:
//! `Iterator::count::<L>` drops each `<L as Iterator>::Item`. MEASURED on stage 1
//! `a92f7478b6` with a verify-off dependency whose `D::drop` writes through null:
//!
//! ```text
//! pub struct L(pub u32);
//! impl Iterator for L { type Item = dep::D; fn next(&mut self) -> Option<dep::D> { .. } }
//! #[trust::assume_total] pub fn t() -> u32 { L(0).count() as u32 }
//! ```
//!
//! built rc=0 in the default, strict and memory-safe lanes with only the
//! `assumption:[assumed-total]` row, and a verify-off `main` calling `t()` died with
//! SIGSEGV (139) in `D::drop`, run by core's `Iterator::count::<L>`.
//!
//! The surface of a local ADT `L` is every LOCAL impl of a NON-LOCAL trait whose
//! header (self type or trait arguments: `impl Iterator for &L`, `impl Add<L> for
//! u32`) names `L`. Only a non-local trait's impl can be reached by code this crate
//! does not own; a local trait's impls are called only from this crate's bodies,
//! which carry their own edges. For each such impl:
//!
//! * every ASSOCIATED TYPE, instantiated at `L`'s arguments where the header lets
//!   them be read off, is walked as the type itself is (a type parameter the match
//!   could not bind answers `true`, fail-closed; so does a GENERIC associated
//!   type, whose own parameters no header binds: 2026-10-08, before which the walk
//!   crashed the compiler on one);
//! * every METHOD must be a body this crate holds (`local_item_is_held_to_this_rule`):
//!   a `#[trust::skip]` method is code nothing verified, run by the sysroot callee;
//!   and, for a GENERIC impl, its instance at the impl arguments read off the type
//!   must have no edge of its own (`unverified_edges`' instance walk, INSTANCE-WALK-1,
//!   2026-10-14: `impl<T: dep::Act2> Iterator for Lw<T>` runs the dependency's `impl
//!   Act2 for u32` inside `Iterator::count::<Lw<u32>>`).
//!
//! The impl index is built once per compilation (per thread) and keyed by the local
//! ADT, so the walk pays a hash lookup per local ADT, not a scan of every impl.

use std::cell::RefCell;

use rustc_data_structures::fx::FxHashMap;
use rustc_middle::ty::{self, Ty, TyCtxt, TypeVisitableExt};
use rustc_span::def_id::{DefId, LOCAL_CRATE};

use super::{local_item_is_held_to_this_rule, ty_reaches_foreign_user_code_on_path};

thread_local! {
    /// The local ADT -> surface impls index, per compilation (keyed by the local
    /// crate's `StableCrateId`).
    static SURFACE_INDEX: RefCell<Option<(u64, FxHashMap<DefId, Vec<DefId>>)>> =
        const { RefCell::new(None) };
}

fn surface_impls_of(tcx: TyCtxt<'_>, adt: DefId) -> Vec<DefId> {
    let key = tcx.stable_crate_id(LOCAL_CRATE).as_u64();
    SURFACE_INDEX.with(|cell| {
        let mut cell = cell.borrow_mut();
        if cell.as_ref().is_none_or(|(k, _)| *k != key) {
            *cell = Some((key, build_index(tcx)));
        }
        cell.as_ref().and_then(|(_, map)| map.get(&adt).cloned()).unwrap_or_default()
    })
}

fn build_index(tcx: TyCtxt<'_>) -> FxHashMap<DefId, Vec<DefId>> {
    let mut map: FxHashMap<DefId, Vec<DefId>> = FxHashMap::default();
    for (&trait_def_id, impls) in tcx.all_local_trait_impls(()) {
        if trait_def_id.is_local() {
            continue;
        }
        for impl_def_id in impls.iter().map(|local| local.to_def_id()) {
            let header = tcx.impl_trait_header(impl_def_id);
            if matches!(header.polarity, ty::ImplPolarity::Negative) {
                continue;
            }
            // An impl with no items adds nothing to the surface.
            if tcx.associated_items(impl_def_id).in_definition_order().next().is_none() {
                continue;
            }
            let trait_ref = header.trait_ref.instantiate_identity().skip_norm_wip();
            let mut anchors: Vec<DefId> = Vec::new();
            for arg_ty in trait_ref.args.types() {
                for inner in arg_ty.walk().filter_map(|a| a.as_type()) {
                    if let ty::Adt(def, _) = *inner.kind()
                        && def.did().is_local()
                        && !anchors.contains(&def.did())
                    {
                        anchors.push(def.did());
                    }
                }
            }
            for adt in anchors {
                map.entry(adt).or_default().push(impl_def_id);
            }
        }
    }
    map
}

/// Does the trait-impl surface of the local ADT `def` at `args` reach foreign user
/// code, or run a local method this crate does not hold? See the module doc.
pub(super) fn local_impl_surface_reaches_foreign<'tcx>(
    tcx: TyCtxt<'tcx>,
    def: ty::AdtDef<'tcx>,
    args: ty::GenericArgs<'tcx>,
    memo: &mut FxHashMap<Ty<'tcx>, bool>,
    path: &mut Vec<Ty<'tcx>>,
) -> bool {
    for impl_def_id in surface_impls_of(tcx, def.did()) {
        let impl_args = impl_args_at(tcx, impl_def_id, def, args);
        for item in tcx.associated_items(impl_def_id).in_definition_order() {
            match item.kind {
                ty::AssocKind::Fn { .. } => {
                    if !local_item_is_held_to_this_rule(tcx, item.def_id) {
                        return true;
                    }
                    if method_instance_reaches_unverified(
                        tcx,
                        impl_def_id,
                        item.def_id,
                        args,
                        impl_args,
                    ) {
                        return true;
                    }
                }
                ty::AssocKind::Type { .. } => {
                    // Trust (2026-10-08, found by the trust-open-false-accepts
                    // landing's probe round): a GENERIC associated type (`type
                    // Searcher<'a> = S<'a>`) has parameters of its own after the
                    // impl's, and instantiating it at the impl's arguments alone
                    // panics in `EarlyBinder::instantiate` ("has parameters, but
                    // no args were provided"): a compiler crash on any crate
                    // whose local type implements a non-local trait with such a
                    // type and is handed to a sysroot callee (measured on main
                    // `de6288dddf`: a `std::str::pattern::Pattern` impl driving
                    // `str::split`, rc=101; refused, rc=1, on main `bb18213379`,
                    // before this walk existed). Its own parameters cannot be
                    // read off the header either, so it is answered as an
                    // unbound parameter is: `true`, fail-closed.
                    if !tcx.generics_of(item.def_id).own_params.is_empty() {
                        return true;
                    }
                    let assoc = tcx.type_of(item.def_id).instantiate(tcx, impl_args);
                    let reaches = match tcx
                        .try_normalize_erasing_regions(ty::TypingEnv::fully_monomorphized(), assoc)
                    {
                        Ok(assoc) => ty_reaches_foreign_user_code_on_path(tcx, assoc, memo, path),
                        Err(_) => true,
                    };
                    if reaches {
                        return true;
                    }
                }
                // An associated constant's value is const-evaluated; a function
                // pointer or vtable in it is charged where a body uses it.
                ty::AssocKind::Const { .. } => {}
            }
        }
    }
    false
}

/// Trust (2026-10-14, INSTANCE-WALK-1): does the surface METHOD `method` of the
/// GENERIC impl `impl_def_id`, at the impl arguments read off the type, reach code
/// this compilation does not verify through what its instantiation adds? MEASURED
/// on stage 1 `d28d17dc2`: `impl<T: dep::Act2> Iterator for Lw<T>` whose `next`
/// calls `self.0.a2()`, driven as `Lw(5u32).take(1).count()` from an
/// `#[trust::assume_total]` body, built rc=0 (default and strict) and the binary died
/// with SIGSEGV in the dependency's `impl Act2 for u32`: `next` is a local body, so
/// this arm held it at every instantiation. The same holds a generic local `Drop`
/// impl reached through `Box<DG<u32>>` or `Vec<DG<u32>>`.
///
/// A non-generic impl adds nothing (its methods are held by induction). Asked at a
/// type that still names a parameter (`adt_args`), nothing is walked: the instance is
/// walked where it becomes concrete. At concrete `adt_args` an impl parameter the
/// header match could not bind, and a method with type or const parameters of its
/// own (no header binds them), answer `true` (fail-closed).
fn method_instance_reaches_unverified<'tcx>(
    tcx: TyCtxt<'tcx>,
    impl_def_id: DefId,
    method: DefId,
    adt_args: ty::GenericArgs<'tcx>,
    impl_args: ty::GenericArgs<'tcx>,
) -> bool {
    if !tcx.generics_of(impl_def_id).requires_monomorphization(tcx)
        || adt_args.has_non_region_param()
    {
        return false;
    }
    if tcx.generics_of(method).own_requires_monomorphization() || impl_args.has_non_region_param() {
        return true;
    }
    let method_args = ty::GenericArgs::for_item(tcx, method, |param, _| {
        match impl_args.get(param.index as usize) {
            Some(arg) => arg,
            None => tcx.lifetimes.re_erased.into(),
        }
    });
    super::unverified_edges::local_instance_unverified_reason(tcx, method, method_args).is_some()
}

/// The impl's generic arguments, read off the first occurrence of `def` in its
/// header against the concrete `args`. A parameter the match cannot bind (it is not
/// named there, or the header shape could not be matched) stays a type parameter,
/// which the walk answers `true` for; lifetimes are erased.
fn impl_args_at<'tcx>(
    tcx: TyCtxt<'tcx>,
    impl_def_id: DefId,
    def: ty::AdtDef<'tcx>,
    args: ty::GenericArgs<'tcx>,
) -> ty::GenericArgs<'tcx> {
    let trait_ref =
        tcx.impl_trait_header(impl_def_id).trait_ref.instantiate_identity().skip_norm_wip();
    let mut binds: FxHashMap<u32, ty::GenericArg<'tcx>> = FxHashMap::default();
    let occurrence = trait_ref.args.types().find_map(|t| {
        t.walk().filter_map(|a| a.as_type()).find_map(|inner| match *inner.kind() {
            ty::Adt(d, pattern) if d == def => Some(pattern),
            _ => None,
        })
    });
    // Only a full match binds; anything else (no occurrence, a shape this matcher
    // cannot take apart, another instantiation of `def`) leaves every parameter
    // unbound, which over-approximates.
    if occurrence.map(|pattern| match_args(pattern, args, &mut binds)) != Some(Match::Yes) {
        binds.clear();
    }
    ty::GenericArgs::for_item(tcx, impl_def_id, |param, _| match param.kind {
        ty::GenericParamDefKind::Lifetime => tcx.lifetimes.re_erased.into(),
        _ => binds.get(&param.index).copied().unwrap_or_else(|| tcx.mk_param_from_def(param)),
    })
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Match {
    Yes,
    No,
    Unknown,
}

fn combine(a: Match, b: Match) -> Match {
    match (a, b) {
        (Match::No, _) | (_, Match::No) => Match::No,
        (Match::Unknown, _) | (_, Match::Unknown) => Match::Unknown,
        _ => Match::Yes,
    }
}

fn match_args<'tcx>(
    pattern: ty::GenericArgs<'tcx>,
    concrete: ty::GenericArgs<'tcx>,
    binds: &mut FxHashMap<u32, ty::GenericArg<'tcx>>,
) -> Match {
    if pattern.len() != concrete.len() {
        return Match::Unknown;
    }
    let mut result = Match::Yes;
    for (p, c) in pattern.iter().zip(concrete.iter()) {
        let m = match (p.kind(), c.kind()) {
            (ty::GenericArgKind::Lifetime(_), ty::GenericArgKind::Lifetime(_)) => Match::Yes,
            (ty::GenericArgKind::Type(p), ty::GenericArgKind::Type(c)) => match_ty(p, c, binds),
            (ty::GenericArgKind::Const(p), ty::GenericArgKind::Const(c)) => {
                match_const(p, c, binds)
            }
            _ => Match::Unknown,
        };
        result = combine(result, m);
    }
    result
}

fn bind<'tcx>(
    index: u32,
    value: ty::GenericArg<'tcx>,
    binds: &mut FxHashMap<u32, ty::GenericArg<'tcx>>,
) -> Match {
    match binds.get(&index) {
        Some(prev) if *prev == value => Match::Yes,
        // The same parameter twice at two different arguments: it may still be one
        // type modulo normalization, so this is no definite mismatch.
        Some(_) => Match::Unknown,
        None => {
            binds.insert(index, value);
            Match::Yes
        }
    }
}

fn match_const<'tcx>(
    p: ty::Const<'tcx>,
    c: ty::Const<'tcx>,
    binds: &mut FxHashMap<u32, ty::GenericArg<'tcx>>,
) -> Match {
    match p.kind() {
        ty::ConstKind::Param(param) => bind(param.index, c.into(), binds),
        _ if p == c => Match::Yes,
        _ => Match::Unknown,
    }
}

fn match_ty<'tcx>(
    p: Ty<'tcx>,
    c: Ty<'tcx>,
    binds: &mut FxHashMap<u32, ty::GenericArg<'tcx>>,
) -> Match {
    match (*p.kind(), *c.kind()) {
        (ty::Param(param), _) => bind(param.index, c.into(), binds),
        (ty::Alias(..) | ty::Infer(_) | ty::Error(_), _)
        | (_, ty::Alias(..) | ty::Infer(_) | ty::Error(_) | ty::Param(_)) => Match::Unknown,
        (ty::Adt(pd, pa), ty::Adt(cd, ca)) => {
            if pd != cd {
                Match::No
            } else {
                match_args(pa, ca, binds)
            }
        }
        (ty::Ref(_, pi, pm), ty::Ref(_, ci, cm)) | (ty::RawPtr(pi, pm), ty::RawPtr(ci, cm)) => {
            if pm != cm { Match::No } else { match_ty(pi, ci, binds) }
        }
        (ty::Slice(pi), ty::Slice(ci)) => match_ty(pi, ci, binds),
        (ty::Array(pi, pn), ty::Array(ci, cn)) => {
            combine(match_ty(pi, ci, binds), match_const(pn, cn, binds))
        }
        (ty::Tuple(pe), ty::Tuple(ce)) => {
            if pe.len() != ce.len() {
                Match::No
            } else {
                pe.iter()
                    .zip(ce.iter())
                    .fold(Match::Yes, |acc, (p, c)| combine(acc, match_ty(p, c, binds)))
            }
        }
        (ty::Bool, ty::Bool)
        | (ty::Char, ty::Char)
        | (ty::Str, ty::Str)
        | (ty::Never, ty::Never) => Match::Yes,
        (ty::Int(a), ty::Int(b)) => {
            if a == b {
                Match::Yes
            } else {
                Match::No
            }
        }
        (ty::Uint(a), ty::Uint(b)) => {
            if a == b {
                Match::Yes
            } else {
                Match::No
            }
        }
        (ty::Float(a), ty::Float(b)) => {
            if a == b {
                Match::Yes
            } else {
                Match::No
            }
        }
        _ if std::mem::discriminant(p.kind()) != std::mem::discriminant(c.kind()) => Match::No,
        // The same rigid kind this matcher does not take apart (a fn pointer, a
        // trait object, a closure): no definite answer.
        _ => Match::Unknown,
    }
}
