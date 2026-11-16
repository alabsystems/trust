//! Independent controls for both retained opaque policies and selection routes.
//! Each submodule owns its complete virtual Rust crate, preserving every original
//! fixture item and preventing the two unrelated Leaky<i64>/Losing implementations
//! from being fused into a different program.
use super::*;

mod bounds_only_controls {
    // Copyright 2026 Andrew Yates
    // SPDX-License-Identifier: MIT OR Apache-2.0

    //! fix10/core-refusals (L1, L3): the #48 layout funnel
    //! (`ctfe_reentrancy::layout_query_is_reentrant_safe_deep`) withheld the layout of every
    //! local struct whose field is a monomorphic associated-type projection (`Atomic<bool>`'s
    //! `UnsafeCell<<bool as AtomicPrimitive>::Storage>`) and of every struct that reaches a local
    //! ADT under a fn-pointer binder (`NonNull<fmt::rt::Argument<'_>>`, whose `fn(&mut
    //! Formatter<'_>)` field put an escaping bound region into `Formatter`'s instantiated fields).
    //! Measured in `core`: about 55 `Atomic<_>` bodies refused as "signature reaches a layout-less
    //! struct" by L1 alone.
    //!
    //! The funnel now reads what the selected impl WROTE for a monomorphic projection, and erases
    //! free regions before instantiating a local ADT's fields. These tests pin both admissions and
    //! every decline that keeps the funnel's argument intact: an impl value carrying an unevaluated
    //! constant whose evaluation would build a body (CTFE inside `mir_built`), an opaque value (a
    //! reveal), a nested projection, a `default` item, a generic argument, and a generic associated
    //! type. Each admitted type's `layout_of` is then asked, as `registered_struct_layout_fill` asks
    //! it. fix11 (L2): an impl value whose constant's whole CTFE closure is leaf (`[u8; LEN]`, `LEN`
    //! a literal) is now read as its value — `at8`, this file's decline control until then, admits,
    //! and a constant that CALLS (`ati8`, `[u8; len()]`) is the control. fix11
    //! (CTFE-IN-MIR-BUILT-1): inside the freeze a projection is selected only when no candidate
    //! impl's where-clause can evaluate a constant (`wh`, `where [(); len()]: Sized`, declines),
    //! each candidate read at the arguments it applies at (`wh_easy`'s `u8: Easy` admits,
    //! `wh_hard`'s `u8: Hard`, whose impl names a constant, declines; `wh_tail`'s `u8: Tailed`,
    //! whose impl's `TailT: Sized` reads a projection tail, declines).
    //!
    //! OPAQUE-IMPL-WHERE-LEAK-1: the selection is now walked leak-free inside `mir_built` in a crate
    //! that declares an opaque (this fixture declares five), so an impl whose WHERE-CLAUSE names an
    //! opaque — through an auto trait of a type holding one (`Wl: Send`), or directly (`Tait2:
    //! Debug`) — is declined, while one whose where-clauses name none (`T: Copy` at `u32`) is still
    //! read. The same where-clauses decide `try_normalize_leak_free`.

    use super::*;

    const FIXTURE_PATH: &str = "every_reached_type_projections_fixture.rs";
    const FIXTURE_SOURCE: &str = r#"
#![feature(impl_trait_in_assoc_type, specialization, type_alias_impl_trait, unsafe_binders)]
#![allow(dead_code, incomplete_features)]
#![recursion_limit = "1024"]
use std::cell::UnsafeCell;
use std::ptr::NonNull;

#[repr(C, align(4))]
pub struct Align4<T>(T);

pub trait Prim { type Storage; fn mk() -> Self::Storage; }
const LEN: usize = 4;
impl Prim for u32 { type Storage = Align4<u32>; fn mk() -> Self::Storage { Align4(0) } }
impl Prim for u8 { type Storage = [u8; LEN]; fn mk() -> Self::Storage { [0; LEN] } }
impl Prim for u16 { type Storage = impl Sized; fn mk() -> Self::Storage { 0u16 } }
const fn len() -> usize { 4 }
impl Prim for i8 { type Storage = [u8; len()]; fn mk() -> Self::Storage { [0; len()] } }
impl Prim for u64 {
    type Storage = <u32 as Prim>::Storage;
    fn mk() -> Self::Storage { Align4(0) }
}

pub struct At<T: Prim> { v: UnsafeCell<<T as Prim>::Storage> }
pub fn at32(a: At<u32>) -> At<u32> { a }
pub fn at8(a: At<u8>) -> At<u8> { a }
pub fn ati8(a: At<i8>) -> At<i8> { a }

pub trait Wq { type S; }
impl Wq for u16 where [(); len()]: Sized { type S = u8; }
pub struct Wh<T: Wq> { s: <T as Wq>::S, n: u8 }
pub fn wh(x: Wh<u16>) -> Wh<u16> { x }
pub trait Easy {}
impl Easy for u8 {}
impl<T: Easy> Wq for (T, T) { type S = T; }
pub fn wh_easy(x: Wh<(u8, u8)>) -> Wh<(u8, u8)> { x }
pub trait Hard {}
impl Hard for u8 where [(); len()]: Sized {}
impl<T: Hard> Wq for [T; 1] { type S = T; }
pub fn wh_hard(x: Wh<[u8; 1]>) -> Wh<[u8; 1]> { x }
pub trait Tl { type S; }
impl Tl for u16 { type S = u8; }
pub struct TailT { s: <u16 as Tl>::S }
pub trait Tailed {}
impl Tailed for u8 where TailT: Sized {}
impl<T: Tailed> Wq for (T, T, T) { type S = T; }
pub fn wh_tail(x: Wh<(u8, u8, u8)>) -> Wh<(u8, u8, u8)> { x }
pub fn at16(a: At<u16>) -> At<u16> { a }
pub fn at64(a: At<u64>) -> At<u64> { a }
pub fn at_generic<T: Prim>(a: At<T>) -> At<T> { a }

pub trait Sp { type A; }
impl<T> Sp for T { default type A = u8; }
impl Sp for u32 { type A = u16; }
pub struct S<T: Sp> { a: <T as Sp>::A }
pub fn s32(x: S<u32>) -> S<u32> { x }
pub fn s8(x: S<u8>) -> S<u8> { x }

pub trait Gat { type G<'a>; }
impl Gat for u32 { type G<'a> = &'a u32; }
pub struct Gs<'a, T: Gat> { g: <T as Gat>::G<'a> }
pub fn gat(x: Gs<'_, u32>) -> usize { std::mem::size_of_val(&x) }

pub struct Fm<'a> { buf: &'a mut u32, n: u32 }
pub struct Arg<'a> { f: fn(&mut Fm<'_>) -> u32, p: &'a u8 }
pub struct H<'a> { a: NonNull<Arg<'a>>, n: usize }
pub fn h(x: H<'_>) -> usize { x.n }

pub type Tait = impl Sized;
pub struct Wl { x: Tait }
#[define_opaque(Tait)]
pub fn tait_def(x: u8) -> Tait { x }
pub type Tait2 = impl std::fmt::Debug;
#[define_opaque(Tait2)]
pub fn tait2_def(x: u8) -> Tait2 { x }
pub type TaitDeclaredSend = impl Send;
#[define_opaque(TaitDeclaredSend)]
pub fn tait_declared_send_def(x: u8) -> TaitDeclaredSend { x }
pub trait SuperSend: Send {}
impl SuperSend for u8 {}
pub type TaitInheritedSend = impl SuperSend;
#[define_opaque(TaitInheritedSend)]
pub fn tait_inherited_send_def(x: u8) -> TaitInheritedSend { x }
pub fn trait_send_declared_opaque(x: TaitDeclaredSend) -> TaitDeclaredSend { x }
pub fn trait_send_inherited_opaque(x: TaitInheritedSend) -> TaitInheritedSend { x }
pub fn trait_send_undeclared_opaque(x: Tait) -> Tait { x }
pub trait Leaky { type Storage; }
impl Leaky for u32 where Wl: Send { type Storage = u32; }
impl Leaky for u16 where Tait2: std::fmt::Debug { type Storage = u16; }
impl Leaky for u64 where Tait: Send { type Storage = u64; }
impl<T: Copy> Leaky for (T,) { type Storage = T; }
pub struct X;
pub struct SafeX;
pub trait Bound {}
impl<'a> Bound for &'a X where Tait2: std::fmt::Debug {}
impl<'a> Bound for &'a SafeX {}
impl Leaky for i32 where for<'a> &'a X: Bound { type Storage = u8; }
impl Leaky for i64 where for<'a> &'a SafeX: Bound { type Storage = u8; }
pub trait Indirect {}
impl Indirect for i16 where Tait2: std::fmt::Debug {}
impl Leaky for i16 where i16: Indirect { type Storage = u8; }
pub struct Lk<T: Leaky> { v: <T as Leaky>::Storage }
pub fn lk_auto(x: Lk<u32>) -> Lk<u32> { x }
pub fn lk_nonauto(x: Lk<u16>) -> Lk<u16> { x }
pub fn lk_bounded(x: Lk<(u32,)>) -> Lk<(u32,)> { x }
pub fn norm_auto(x: <u64 as Leaky>::Storage) -> u64 { x }
pub fn norm_nonauto(x: <u16 as Leaky>::Storage) -> u16 { x }
pub fn norm_bounded(x: <(u32,) as Leaky>::Storage) -> u32 { x }
pub fn norm_auto_field(x: <u32 as Leaky>::Storage) -> u32 { x }
pub fn norm_higher(x: <i32 as Leaky>::Storage) -> u8 { x }
pub fn norm_higher_safe(x: <i64 as Leaky>::Storage) -> u8 { x }
pub fn norm_indirect(x: <i16 as Leaky>::Storage) -> u8 { x }
pub fn select_ctfe(x: <u16 as Wq>::S) -> u8 { x }
// The builtin object candidate confirms Item: Hard, whose concrete impl reaches
// len(). No user impl header for DynCtfe exposes that CTFE path to the preflight.
pub trait DynCtfe { type Item: Hard; }
pub fn dyn_ctfe(x: &dyn DynCtfe<Item = u8>) {}
// `impl<T>` implicitly requires `T: Sized`. As written that bound names no
// alias; at TailCtfe it reads the projection and confirms Wq's len() bound.
pub trait Blanket {}
impl<T> Blanket for T {}
pub struct TailCtfe { s: <u16 as Wq>::S }
pub struct TailSafe { s: u8 }
pub fn blanket_sized_tail(x: TailCtfe) {}
pub fn blanket_sized_safe(x: TailSafe) {}
#[derive(Clone, Copy)]
pub struct BoundTail<'a> { r: &'a (), s: <u16 as Wq>::S }
#[derive(Clone, Copy)]
pub struct BoundSafe<'a> { r: &'a (), s: u8 }
pub fn blanket_sized_binder_tail(x: unsafe<'a> BoundTail<'a>) {}
pub fn blanket_sized_binder_safe(x: unsafe<'a> BoundSafe<'a>) {}
pub fn trait_send_safe(x: u32) -> u32 { x }
pub fn trait_send_opaque_field(x: Wl) -> Wl { x }

pub trait Source { type Item; }
impl Source for u8 { type Item = u32; }
pub trait Shadowed { type Storage; }
impl Shadowed for u8 where u8: Source<Item = u32> { type Storage = u8; }
pub fn norm_shadowed(x: <u8 as Shadowed>::Storage) -> u8 { x }
pub trait Losing<A> { type Storage; }
impl<T, A> Losing<A> for T { default type Storage = u8; }
impl Losing<<u8 as Source>::Item> for u8 { type Storage = u16; }
pub fn norm_losing(x: <u8 as Losing<u64>>::Storage) -> <u8 as Losing<u64>>::Storage { x }

pub trait Super { type Item; }
pub trait Sub: Super {}
pub fn upcast_projection(x: &dyn Sub<Item = u32>) -> &dyn Super<Item = u32> { x }

// A finite, satisfiable trait chain: the terminal u8 implements Link. PhantomData
// keeps the independent Sized-tail limit out of the chain's budget measurement.
pub struct Deep<T>(std::marker::PhantomData<T>);
pub trait Link {}
impl Link for u8 {}
impl<T: Link> Link for Deep<T> {}
pub trait End { type Storage; }
impl<T: Link> End for Deep<T> { type Storage = u8; }
macro_rules! deep {
    () => { u8 };
    ($_head:tt $($tail:tt)*) => { Deep<deep!($($tail)*)> };
}
pub fn select_budget_small(x: <deep!(0 0 0 0 0 0 0 0) as End>::Storage) -> u8 { x }
pub fn select_budget_large(x: <deep!(0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) as End>::Storage) -> u8 { x }
"#;

    struct FixtureFileLoader {
        source: String,
    }

    impl rustc_span::source_map::FileLoader for FixtureFileLoader {
        fn file_exists(&self, path: &Path) -> bool {
            path == Path::new(FIXTURE_PATH)
        }

        fn read_file(&self, path: &Path) -> io::Result<String> {
            if self.file_exists(path) {
                Ok(self.source.clone())
            } else {
                Err(io::Error::other("unexpected every_reached_type fixture path"))
            }
        }

        fn read_binary_file(&self, _path: &Path) -> io::Result<Arc<[u8]>> {
            Err(io::Error::other("binary source reads are unsupported in this fixture"))
        }

        fn current_directory(&self) -> io::Result<PathBuf> {
            std::env::current_dir()
        }
    }

    /// Fixture fn name -> (funnel answer for its first parameter's type, that type's
    /// `layout_of` size when the funnel admitted it).
    #[derive(Default)]
    struct FunnelCallbacks {
        answers: BTreeMap<String, (bool, Option<u64>)>,
        /// Fixture fn name (`norm_*`) -> `try_normalize_leak_free` of its first parameter's
        /// UNNORMALIZED type, asked inside the freeze, rendered.
        normalized: BTreeMap<String, Option<String>>,
        /// Direct selection admission, before `layout_of` or `Instance::try_resolve` could
        /// reveal a hidden type. In the next solver, a fully proved source has no returned
        /// nested obligations, so these controls must exercise the independent tree walk.
        selected: BTreeMap<String, bool>,
        selected_unfrozen: BTreeMap<String, bool>,
        selection_types: BTreeMap<String, usize>,
        traits: BTreeMap<String, bool>,
        next_solver: bool,
        dyn_ctfe_preflight: Option<bool>,
        blanket_preflight: BTreeMap<String, bool>,
        scalar_copy_model: BTreeMap<String, bool>,
        normalization_cache_roundtrips:
            BTreeMap<String, (Option<String>, Option<String>, Option<String>, Option<String>)>,
        opaque_bounds_only_mode: bool,
    }

    impl FunnelCallbacks {
        fn record_selection<'tcx>(
            &mut self,
            tcx: TyCtxt<'tcx>,
            name: &str,
            trait_ref: ty::TraitRef<'tcx>,
        ) {
            self.selection_types.insert(
                name.into(),
                trait_ref.self_ty().walk().filter_map(|arg| arg.as_type()).count(),
            );
            let admitted = || {
                crate::ctfe_reentrancy::select_reveal_free(tcx, ty::ParamEnv::empty(), trait_ref)
                    .is_some()
            };
            // The unfrozen run isolates the opaque/probe walk from the additional CTFE
            // preflight required before an eager solve on a `mir_built` stack.
            let frozen = {
                let _frozen = crate::ctfe_reentrancy::enter();
                admitted()
            };
            self.selected.insert(name.into(), frozen);
            if !matches!(name, "select_ctfe" | "dyn_ctfe") {
                self.selected_unfrozen.insert(name.into(), admitted());
            }
        }
    }

    impl rustc_driver::Callbacks for FunnelCallbacks {
        fn config(&mut self, config: &mut Config) {
            config.file_loader =
                Some(Box::new(FixtureFileLoader { source: FIXTURE_SOURCE.into() }));
        }

        fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
            tcx.sess.dcx().abort_if_errors();
            self.next_solver = tcx.next_trait_solver_globally();
            self.opaque_bounds_only_mode = matches!(
                crate::ctfe_reentrancy::leak_free_typing_mode(tcx),
                ty::TypingMode::OpaqueBoundsOnly
            );
            {
                use rustc_middle::ty::Upcast;
                let copy = tcx.lang_items().copy_trait().expect("Copy trait");
                let primitive = |t| ty::TraitRef::new(tcx, copy, [t]).upcast(tcx);
                for (name, t) in [
                    ("bool", tcx.types.bool),
                    ("char", tcx.types.char),
                    ("u8", tcx.types.u8),
                    ("u32", tcx.types.u32),
                    ("i32", tcx.types.i32),
                    ("f32", tcx.types.f32),
                ] {
                    self.scalar_copy_model.insert(
                        name.into(),
                        crate::ctfe_reentrancy::primitive_copy_selection_is_reveal_free(
                            tcx,
                            ty::ParamEnv::empty(),
                            primitive(t),
                        ),
                    );
                }
                let scalar = primitive(tcx.types.u32);
                let trait_bound: ty::Clause<'tcx> =
                    ty::TraitRef::new(tcx, copy, [tcx.types.u32]).upcast(tcx);
                let trait_environment = ty::ParamEnv::new(tcx, [trait_bound]);
                self.scalar_copy_model.insert(
                    "trait_environment".into(),
                    crate::ctfe_reentrancy::primitive_copy_selection_is_reveal_free(
                        tcx,
                        trait_environment,
                        scalar,
                    ),
                );
                let negative: ty::Predicate<'tcx> = ty::TraitClause {
                    trait_ref: ty::TraitRef::new(tcx, copy, [tcx.types.u32]),
                    polarity: ty::ClausePolarity::Negative,
                }
                .upcast(tcx);
                self.scalar_copy_model.insert(
                    "negative_copy".into(),
                    crate::ctfe_reentrancy::primitive_copy_selection_is_reveal_free(
                        tcx,
                        ty::ParamEnv::empty(),
                        negative,
                    ),
                );
                for (name, t) in [
                    ("tuple", ty::Ty::new_tup(tcx, &[tcx.types.u32])),
                    (
                        "raw_pointer",
                        ty::Ty::new_ptr(tcx, tcx.types.u32, rustc_hir::Mutability::Not),
                    ),
                ] {
                    self.scalar_copy_model.insert(
                        name.into(),
                        crate::ctfe_reentrancy::primitive_copy_selection_is_reveal_free(
                            tcx,
                            ty::ParamEnv::empty(),
                            primitive(t),
                        ),
                    );
                }
            }
            for owner in tcx.hir_body_owners() {
                let did = owner.to_def_id();
                if tcx.def_kind(did) != rustc_hir::def::DefKind::Fn {
                    continue;
                }
                let name = tcx.item_name(did).to_string();
                let sig = tcx.fn_sig(did).instantiate_identity().skip_norm_wip();
                let sig = tcx.instantiate_bound_regions_with_erased(sig);
                // A parameterless fixture fn (`const fn len()`, the `wh` control) is a helper, not a
                // funnel case.
                let Some(&ty) = sig.inputs().first() else {
                    continue;
                };
                // The funnel is asked from inside `mir_built`; ask it there, under the freeze frame
                // the hook holds while it lowers this fn.
                let admitted = {
                    let _frozen = crate::ctfe_reentrancy::enter_building(owner);
                    crate::ctfe_reentrancy::layout_query_is_reentrant_safe_deep(tcx, ty)
                };
                let size = admitted.then(|| {
                    tcx.layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(ty))
                        .expect("an admitted type lays out")
                        .size
                        .bytes()
                });
                if name.starts_with("norm_") || name.starts_with("select_") {
                    if name.starts_with("norm_") {
                        let normalized = {
                            let _frozen = crate::ctfe_reentrancy::enter();
                            crate::ctfe_reentrancy::try_normalize_bounds_only_for_test(
                                tcx,
                                ty::ParamEnv::empty(),
                                ty,
                            )
                        };
                        self.normalized.insert(name.clone(), normalized.map(|t| format!("{t:?}")));
                        if matches!(name.as_str(), "norm_auto" | "norm_nonauto") {
                            // Warm a mode which may read hidden types, then repeat
                            // the guarded query twice. Each must keep its own answer.
                            let ordinary = || {
                                tcx.try_normalize_erasing_regions(
                                    ty::TypingEnv::fully_monomorphized(),
                                    ty::Unnormalized::new_wip(ty),
                                )
                                .ok()
                                .map(|t| format!("{t:?}"))
                            };
                            let guarded = || {
                                let _frozen = crate::ctfe_reentrancy::enter();
                                crate::ctfe_reentrancy::try_normalize_bounds_only_for_test(
                                    tcx,
                                    ty::ParamEnv::empty(),
                                    ty,
                                )
                                .map(|t| format!("{t:?}"))
                            };
                            self.normalization_cache_roundtrips.insert(
                                name.clone(),
                                (ordinary(), guarded(), ordinary(), guarded()),
                            );
                        }
                    }
                    let ty::Alias(_, alias) = *ty.kind() else {
                        panic!("the direct normalization fixture must retain its projection");
                    };
                    let ty::AliasTyKind::Projection { def_id } = alias.kind else {
                        panic!("the direct normalization fixture must name a trait projection");
                    };
                    let trait_ref =
                        ty::TraitRef::new_from_args(tcx, tcx.parent(def_id.into()), alias.args);
                    self.record_selection(tcx, &name, trait_ref);
                }
                if name == "dyn_ctfe" {
                    let ty::Ref(_, object, _) = *ty.kind() else { panic!("dyn CTFE reference") };
                    let ty::Dynamic(bounds, _) = *object.kind() else { panic!("dyn CTFE object") };
                    let principal = bounds.principal().expect("dyn CTFE principal");
                    let trait_ref = tcx
                        .instantiate_bound_regions_with_erased(principal.with_self_ty(tcx, object));
                    // Check the safety gate itself: a proof-tree refusal occurs only after
                    // the eager solver may have evaluated the associated-type bound.
                    self.dyn_ctfe_preflight =
                        Some(crate::ctfe_reentrancy::next_selection_is_const_inert(
                            tcx,
                            ty::ParamEnv::empty(),
                            trait_ref,
                        ));
                    self.record_selection(tcx, &name, trait_ref);
                }
                if name.starts_with("blanket_sized_") {
                    let blanket = tcx
                        .hir_crate_items(())
                        .free_items()
                        .map(|item| item.owner_id.to_def_id())
                        .filter(|&id| tcx.def_kind(id) == rustc_hir::def::DefKind::Trait)
                        .find(|&id| tcx.item_name(id).as_str() == "Blanket")
                        .expect("Blanket trait");
                    let trait_ref = ty::TraitRef::new(tcx, blanket, [ty]);
                    // This is the pre-evaluation gate itself, not a later visitor
                    // refusal after the solver has already normalized the tail.
                    self.blanket_preflight.insert(
                        name.clone(),
                        crate::ctfe_reentrancy::next_selection_is_const_inert(
                            tcx,
                            ty::ParamEnv::empty(),
                            trait_ref,
                        ),
                    );
                }
                if name.starts_with("trait_send_") {
                    let _frozen = crate::ctfe_reentrancy::enter();
                    let send = tcx.get_diagnostic_item(rustc_span::sym::Send).expect("Send trait");
                    self.traits.insert(
                        name.clone(),
                        crate::ctfe_reentrancy::trait_holds_bounds_only_for_test(
                            tcx,
                            ty::ParamEnv::empty(),
                            ty,
                            send,
                        ),
                    );
                }
                if name.starts_with("upcast_") {
                    let ty::Ref(_, source, _) = *ty.kind() else {
                        panic!("upcast source reference")
                    };
                    let ty::Ref(_, target, _) = *sig.output().kind() else {
                        panic!("upcast target reference")
                    };
                    let unsize = tcx.lang_items().unsize_trait().expect("Unsize trait");
                    let trait_ref = ty::TraitRef::new(tcx, unsize, [source, target]);
                    self.record_selection(tcx, &name, trait_ref);
                }
                self.answers.insert(name, (admitted, size));
            }
            Compilation::Stop
        }
    }

    fn funnel_answers() -> (BTreeMap<String, (bool, Option<u64>)>, BTreeMap<String, Option<String>>)
    {
        let callbacks = funnel_answers_with_args(&[]);
        (callbacks.answers, callbacks.normalized)
    }

    fn funnel_answers_with_args(extra_args: &[&str]) -> FunnelCallbacks {
        let mut callbacks = FunnelCallbacks::default();
        let mut args = vec![
            "rustc".into(),
            FIXTURE_PATH.into(),
            "--crate-name".into(),
            "every_reached_type_projections_fixture".into(),
            "--crate-type=lib".into(),
            "--edition=2021".into(),
            "-Zno-codegen".into(),
            "-Zcodegen-backend=dummy".into(),
            "--sysroot".into(),
            compiler_sysroot(),
        ];
        args.extend(extra_args.iter().map(|arg| (*arg).to_string()));
        let result =
            rustc_driver::catch_fatal_errors(|| -> rustc_interface::interface::Result<()> {
                rustc_driver::run_compiler(&args, &mut callbacks);
                Ok(())
            });
        assert!(result.is_ok(), "failed to compile the every_reached_type fixture");
        callbacks
    }

    #[test]
    fn global_next_solver_keeps_safe_selections_and_walks_opaque_obligations() {
        // Exercise the production solver explicitly even on a compiler whose channel default
        // predates PERF-SEP26-DEFAULTS. The default-mode coverage tests below remain unchanged.
        let callbacks = funnel_answers_with_args(&["-Znext-solver=globally"]);
        assert!(callbacks.next_solver, "this regression must run the next solver");
        for name in ["norm_bounded", "norm_higher_safe"] {
            assert_eq!(callbacks.selected.get(name), Some(&true), "safe selection {name}");
            assert_eq!(callbacks.selected_unfrozen.get(name), Some(&true), "safe unfrozen {name}");
        }
        for name in ["norm_auto", "norm_auto_field", "norm_nonauto", "norm_higher", "norm_indirect"]
        {
            assert_eq!(callbacks.selected.get(name), Some(&false), "opaque selection {name}");
            assert_eq!(
                callbacks.selected_unfrozen.get(name),
                Some(&false),
                "opaque unfrozen {name}"
            );
        }
        // The upstream diagnostic view deliberately omits shadowed-environment and dyn
        // projection-compatibility probes, and candidates that fail before a canonical
        // response. None of those omissions can count as an empty, reveal-free proof tree.
        for name in ["norm_shadowed", "norm_losing", "upcast_projection"] {
            assert_eq!(callbacks.selected.get(name), Some(&false), "unobservable selection {name}");
            assert_eq!(
                callbacks.selected_unfrozen.get(name),
                Some(&false),
                "unobservable unfrozen {name}"
            );
        }
        assert_eq!(callbacks.selected.get("select_ctfe"), Some(&false));
        assert_eq!(
            callbacks.dyn_ctfe_preflight,
            Some(false),
            "decline before eager object solving"
        );
        assert_eq!(callbacks.selected.get("dyn_ctfe"), Some(&false));
        assert!(callbacks.selection_types["select_budget_small"] < 32);
        assert!(callbacks.selection_types["select_budget_large"] > 256);
        for selections in [&callbacks.selected, &callbacks.selected_unfrozen] {
            assert_eq!(selections.get("select_budget_small"), Some(&true));
            assert_eq!(selections.get("select_budget_large"), Some(&false));
        }
        assert_eq!(callbacks.traits.get("trait_send_safe"), Some(&true));
        assert_eq!(callbacks.traits.get("trait_send_opaque_field"), Some(&false));
        assert_eq!(callbacks.normalized.get("norm_auto"), Some(&None));
        assert_eq!(callbacks.normalized.get("norm_auto_field"), Some(&None));
        assert_eq!(callbacks.normalized.get("norm_bounded"), Some(&Some("u32".into())));
        // Analysis can answer the declared bound without revealing the opaque. The codegen
        // selection above must still decline it, even when rustc reports Certainty::Yes.
        assert_eq!(callbacks.normalized.get("norm_nonauto"), Some(&Some("u16".into())));
    }

    #[test]
    fn global_next_solver_preflight_checks_instantiated_sized_bounds() {
        let callbacks = funnel_answers_with_args(&["-Znext-solver=globally"]);
        assert!(callbacks.next_solver, "this regression must run the next solver");
        assert_eq!(callbacks.blanket_preflight.get("blanket_sized_tail"), Some(&false));
        assert_eq!(callbacks.blanket_preflight.get("blanket_sized_safe"), Some(&true));
    }

    #[test]
    fn global_next_solver_preflight_walks_unsafe_binder_sized_tails() {
        let callbacks = funnel_answers_with_args(&["-Znext-solver=globally"]);
        assert!(callbacks.next_solver, "this regression must run the next solver");
        assert_eq!(callbacks.blanket_preflight.get("blanket_sized_binder_tail"), Some(&false));
        assert_eq!(callbacks.blanket_preflight.get("blanket_sized_binder_safe"), Some(&true));
    }

    #[test]
    fn primitive_copy_terminal_has_closed_inputs() {
        let callbacks = funnel_answers_with_args(&["-Znext-solver=globally"]);
        for name in ["bool", "char", "u8", "u32", "i32", "f32"] {
            assert_eq!(callbacks.scalar_copy_model.get(name), Some(&true), "scalar {name}");
        }
        for name in ["trait_environment", "negative_copy", "tuple", "raw_pointer"] {
            assert_eq!(
                callbacks.scalar_copy_model.get(name),
                Some(&false),
                "outside scalar model {name}"
            );
        }
    }

    #[test]
    fn opaque_bound_analysis_keeps_declared_bounds_and_cache_identity() {
        let callbacks = funnel_answers_with_args(&["-Znext-solver=globally"]);
        assert!(callbacks.next_solver);
        assert!(callbacks.opaque_bounds_only_mode);
        assert_eq!(
            callbacks.normalization_cache_roundtrips.get("norm_auto"),
            Some(&(Some("u64".into()), None, Some("u64".into()), None)),
            "ordinary cache entries cannot supply an undeclared auto trait"
        );
        assert_eq!(
            callbacks.normalization_cache_roundtrips.get("norm_nonauto"),
            Some(&(Some("u16".into()), Some("u16".into()), Some("u16".into()), Some("u16".into()))),
            "a declared non-auto bound needs no hidden type"
        );
    }

    #[test]
    fn monomorphic_projection_and_binder_regions_admit_exactly_the_safe_shapes() {
        let (answers, _) = funnel_answers();
        let get = |name: &str| *answers.get(name).unwrap_or_else(|| panic!("no fixture fn {name}"));

        // L1: the selected impl wrote an alias-free value; `layout_of` agrees on its bytes.
        assert_eq!(get("at32"), (true, Some(4)), "At<u32> reads Align4<u32>");
        // The specializing impl's own, non-`default` item is what codegen selection reads.
        assert_eq!(get("s32"), (true, Some(2)), "S<u32> reads the specializing impl's u16");
        // L3: a local ADT reached under `fn(&mut Fm<'_>)` no longer leaks the binder's region.
        assert_eq!(get("h"), (true, Some(16)), "H<'_> lays out");
        // fix11 (L2): the impl value's constant `LEN` is a literal (a leaf closure), read as 4.
        assert_eq!(get("at8"), (true, Some(4)), "an impl value [u8; LEN] with LEN a leaf constant");

        // Declines: each would ask more than the funnel's argument covers.
        assert_eq!(get("ati8"), (false, None), "an impl value whose const calls a const fn (CTFE)");
        // fix11 (CTFE-IN-MIR-BUILT-1): selection would CONFIRM `[(); len()]: Sized`, i.e.
        // evaluate `len()`; inside the freeze the projection is not selected.
        assert_eq!(
            get("wh"),
            (false, None),
            "a candidate impl whose where-clause names a constant"
        );
        // A candidate is read at the arguments it applies at: `impl<T: Easy> Wq for (T, T)` at
        // `(u8, u8)` confirms `u8: Easy`, whose one impl is inert; `impl<T: Hard> Wq for [T; 1]`
        // at `[u8; 1]` confirms `u8: Hard`, whose impl names a constant, and declines.
        assert_eq!(
            get("wh_easy"),
            (true, Some(2)),
            "a trait bound of a primitive with inert impls"
        );
        assert_eq!(get("wh_hard"), (false, None), "a trait bound whose impl names a constant");
        // fix11 L2 review: `u8: Tailed`'s one impl carries `TailT: Sized`, an alias-free clause whose
        // proof normalizes `TailT`'s tail `<u16 as Tl>::S` (an impl whose where-clauses could
        // evaluate a constant: tests/ui/trust/sized_tail_clause_ctfe_no_query_cycle.rs).
        assert_eq!(get("wh_tail"), (false, None), "a bound whose impl's Sized clause reads a tail");
        assert_eq!(get("at16"), (false, None), "an impl value that is an opaque (a reveal)");
        assert_eq!(get("at64"), (false, None), "an impl value that is itself a projection");
        assert_eq!(get("at_generic"), (false, None), "a generic argument");
        assert_eq!(get("s8"), (false, None), "a `default` item");
        assert_eq!(get("gat"), (false, None), "a generic associated type");
    }

    /// OPAQUE-IMPL-WHERE-LEAK-1: a codegen-mode selection of `u32: Leaky` confirms `Wl: Send`,
    /// which reveals `Tait` through `Wl`'s field, and one of `u16: Leaky` normalizes `Tait2: Debug`,
    /// which reveals `Tait2`; inside `mir_built` of either opaque's defining body that is an E0391
    /// on valid Rust. The funnel declines both projections and the leak-free normalizer refuses
    /// the auto-trait one, while `(u32,)`'s impl, whose where-clause (`T: Copy`) names no opaque,
    /// is read and normalized as before.
    #[test]
    fn an_impl_where_clause_naming_an_opaque_declines_the_projection() {
        let (answers, normalized) = funnel_answers();
        let get = |name: &str| *answers.get(name).unwrap_or_else(|| panic!("no fixture fn {name}"));
        let norm = |name: &str| {
            normalized.get(name).unwrap_or_else(|| panic!("no fixture fn {name}")).clone()
        };

        assert_eq!(get("lk_auto"), (false, None), "`Wl: Send` reaches `Tait` through a field");
        assert_eq!(get("lk_nonauto"), (false, None), "`Tait2: Debug` names the opaque");
        // fix11 L2's const-inert gate, asked first inside the freeze, checks `T: Copy` at `u32` and
        // admits it; the leak-free walk then finds nothing naming an opaque.
        assert_eq!(get("lk_bounded"), (true, Some(4)), "`u32: Copy` names no opaque");

        // The auto-trait goal is asked of the opaque itself (`impl Leaky for u64 where Tait: Send`).
        // Every leak-free question carries `leak_free_infcx`'s `'?0: 'static` clause, which keeps it
        // out of the old solver's GLOBAL caches (OPAQUE-IMPL-WHERE-LEAK-2), so the leaking answer
        // typeck cached for the same goal after analysis is never read here: the ambiguity is
        // deterministic.
        assert_eq!(norm("norm_auto"), None, "the auto-trait goal on `Tait` is ambiguous");
        assert_eq!(
            norm("norm_bounded"),
            Some("u32".to_string()),
            "a clean where-clause normalizes"
        );
        // `Tait2: Debug` holds from the opaque's own bound without revealing it: an ANALYSIS
        // question may answer it (only the codegen-mode selection above must not).
        assert_eq!(norm("norm_nonauto"), Some("u16".to_string()), "a bound answers `Tait2: Debug`");
    }

    #[test]
    fn opaque_bound_analysis_uses_declared_auto_traits_without_hidden_leakage() {
        let callbacks = funnel_answers_with_args(&["-Znext-solver=globally"]);
        assert!(callbacks.next_solver);
        assert!(callbacks.opaque_bounds_only_mode);
        for name in ["trait_send_declared_opaque", "trait_send_inherited_opaque"] {
            assert_eq!(callbacks.traits.get(name), Some(&true), "declared auto bound {name}");
        }
        for name in ["trait_send_undeclared_opaque", "trait_send_opaque_field"] {
            assert_eq!(
                callbacks.traits.get(name),
                Some(&false),
                "no hidden auto-trait leakage {name}"
            );
        }
    }

    struct NoCoreCopyCallbacks {
        source: String,
        answer: Option<bool>,
    }
    impl rustc_driver::Callbacks for NoCoreCopyCallbacks {
        fn config(&mut self, config: &mut Config) {
            config.file_loader = Some(Box::new(FixtureFileLoader { source: self.source.clone() }));
        }
        fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
            use rustc_middle::ty::Upcast;
            tcx.sess.dcx().abort_if_errors();
            assert!(tcx.next_trait_solver_globally());
            let copy = tcx.lang_items().copy_trait().expect("fixture Copy language item");
            self.answer = Some(crate::ctfe_reentrancy::primitive_copy_selection_is_reveal_free(
                tcx,
                ty::ParamEnv::empty(),
                ty::TraitRef::new(tcx, copy, [tcx.types.u32]).upcast(tcx),
            ));
            Compilation::Stop
        }
    }
    fn no_core_copy_answer(source: String) -> bool {
        let mut callbacks = NoCoreCopyCallbacks { source, answer: None };
        let args = vec![
            "rustc".into(),
            FIXTURE_PATH.into(),
            "--crate-name=no_core_copy_terminal".into(),
            "--crate-type=lib".into(),
            "--edition=2021".into(),
            "-Zno-codegen".into(),
            "-Zcodegen-backend=dummy".into(),
            "-Znext-solver=globally".into(),
            "--sysroot".into(),
            compiler_sysroot(),
        ];
        let result =
            rustc_driver::catch_fatal_errors(|| -> rustc_interface::interface::Result<()> {
                rustc_driver::run_compiler(&args, &mut callbacks);
                Ok(())
            });
        assert!(result.is_ok(), "no_core fixture must compile before its admission is judged");
        callbacks.answer.expect("no_core analysis callback must run")
    }
    #[test]
    fn primitive_copy_terminal_checks_custom_language_item_declarations() {
        const SOURCE: &str = r#"#![feature(no_core,lang_items)]
#![allow(internal_features)]
#![no_core]
#[lang="pointee_sized"] pub trait PointeeSized {}
#[lang="meta_sized"] pub trait MetaSized: PointeeSized {}
#[lang="sized"] pub trait Sized: MetaSized {}
#[lang="copy"] pub trait Copy: Clone {}
#[lang="clone"] pub trait Clone: Sized {}
pub trait Extra {}
impl Extra for u32 {}
impl Extra for u8 {}
impl Clone for u32 {}
impl Copy for u32 {}
"#;
        for (name, source, expected) in [
            ("closed_markers", SOURCE.to_string(), true),
            ("copy_extra_supertrait", SOURCE.replace("Copy: Clone", "Copy: Clone + Extra"), false),
            (
                "clone_extra_supertrait",
                SOURCE.replace("Clone: Sized", "Clone: Sized + Extra"),
                false,
            ),
            (
                "copy_concrete_bound",
                SOURCE.replace("Copy: Clone {}", "Copy: Clone where u8: Extra {}"),
                false,
            ),
        ] {
            assert_eq!(no_core_copy_answer(source), expected, "custom language items {name}");
        }
    }
}

mod opaque_analysis_controls {
    // Copyright 2026 Andrew Yates
    // SPDX-License-Identifier: MIT OR Apache-2.0

    //! fix10/core-refusals (L1, L3): the #48 layout funnel
    //! (`ctfe_reentrancy::layout_query_is_reentrant_safe_deep`) withheld the layout of every
    //! local struct whose field is a monomorphic associated-type projection (`Atomic<bool>`'s
    //! `UnsafeCell<<bool as AtomicPrimitive>::Storage>`) and of every struct that reaches a local
    //! ADT under a fn-pointer binder (`NonNull<fmt::rt::Argument<'_>>`, whose `fn(&mut
    //! Formatter<'_>)` field put an escaping bound region into `Formatter`'s instantiated fields).
    //! Measured in `core`: about 55 `Atomic<_>` bodies refused as "signature reaches a layout-less
    //! struct" by L1 alone.
    //!
    //! The funnel now reads what the selected impl WROTE for a monomorphic projection, and erases
    //! free regions before instantiating a local ADT's fields. These tests pin both admissions and
    //! every decline that keeps the funnel's argument intact: an impl value carrying an unevaluated
    //! constant whose evaluation would build a body (CTFE inside `mir_built`), an opaque value (a
    //! reveal), a nested projection, a `default` item, a generic argument, and a generic associated
    //! type. Each admitted type's `layout_of` is then asked, as `registered_struct_layout_fill` asks
    //! it. fix11 (L2): an impl value whose constant's whole CTFE closure is leaf (`[u8; LEN]`, `LEN`
    //! a literal) is now read as its value — `at8`, this file's decline control until then, admits,
    //! and a constant that CALLS (`ati8`, `[u8; len()]`) is the control. fix11
    //! (CTFE-IN-MIR-BUILT-1): inside the freeze a projection is selected only when no candidate
    //! impl's where-clause can evaluate a constant (`wh`, `where [(); len()]: Sized`, declines),
    //! each candidate read at the arguments it applies at (`wh_easy`'s `u8: Easy` admits,
    //! `wh_hard`'s `u8: Hard`, whose impl names a constant, declines; `wh_tail`'s `u8: Tailed`,
    //! whose impl's `TailT: Sized` reads a projection tail, declines).
    //!
    //! OPAQUE-IMPL-WHERE-LEAK-1: the selection is now walked leak-free inside `mir_built` in a crate
    //! that declares an opaque (this fixture declares four), so an impl whose WHERE-CLAUSE names an
    //! opaque — through an auto trait of a type holding one (`Wl: Send`), or directly (`Tait2:
    //! Debug`) — is declined, while one whose where-clauses name none (`T: Copy` at `u32`) is still
    //! read. The same where-clauses decide `try_normalize_leak_free`.

    use super::*;

    const FIXTURE_PATH: &str = "every_reached_type_projections_fixture.rs";
    const FIXTURE_SOURCE: &str = r#"
#![feature(impl_trait_in_assoc_type, specialization, type_alias_impl_trait, transmutability)]
#![allow(dead_code, incomplete_features)]
use std::cell::UnsafeCell;
use std::ptr::NonNull;

#[repr(C, align(4))]
pub struct Align4<T>(T);

pub trait Prim { type Storage; fn mk() -> Self::Storage; }
const LEN: usize = 4;
impl Prim for u32 { type Storage = Align4<u32>; fn mk() -> Self::Storage { Align4(0) } }
impl Prim for u8 { type Storage = [u8; LEN]; fn mk() -> Self::Storage { [0; LEN] } }
impl Prim for u16 { type Storage = impl Sized; fn mk() -> Self::Storage { 0u16 } }
const fn len() -> usize { 4 }
impl Prim for i8 { type Storage = [u8; len()]; fn mk() -> Self::Storage { [0; len()] } }
impl Prim for u64 {
    type Storage = <u32 as Prim>::Storage;
    fn mk() -> Self::Storage { Align4(0) }
}

pub struct At<T: Prim> { v: UnsafeCell<<T as Prim>::Storage> }
pub fn at32(a: At<u32>) -> At<u32> { a }
pub fn at8(a: At<u8>) -> At<u8> { a }
pub fn ati8(a: At<i8>) -> At<i8> { a }

pub trait Wq { type S; }
impl Wq for u16 where [(); len()]: Sized { type S = u8; }
pub struct Wh<T: Wq> { s: <T as Wq>::S, n: u8 }
pub fn wh(x: Wh<u16>) -> Wh<u16> { x }
pub trait Easy {}
impl Easy for u8 {}
impl<T: Easy> Wq for (T, T) { type S = T; }
pub fn wh_easy(x: Wh<(u8, u8)>) -> Wh<(u8, u8)> { x }
pub trait Hard {}
impl Hard for u8 where [(); len()]: Sized {}
impl<T: Hard> Wq for [T; 1] { type S = T; }
pub fn wh_hard(x: Wh<[u8; 1]>) -> Wh<[u8; 1]> { x }
pub trait Tl { type S; }
impl Tl for u16 { type S = u8; }
pub struct TailT { s: <u16 as Tl>::S }
pub trait Tailed {}
impl Tailed for u8 where TailT: Sized {}
impl<T: Tailed> Wq for (T, T, T) { type S = T; }
pub fn wh_tail(x: Wh<(u8, u8, u8)>) -> Wh<(u8, u8, u8)> { x }
pub fn at16(a: At<u16>) -> At<u16> { a }
pub fn at64(a: At<u64>) -> At<u64> { a }
pub fn at_generic<T: Prim>(a: At<T>) -> At<T> { a }

pub trait Sp { type A; }
impl<T> Sp for T { default type A = u8; }
impl Sp for u32 { type A = u16; }
pub struct S<T: Sp> { a: <T as Sp>::A }
pub fn s32(x: S<u32>) -> S<u32> { x }
pub fn s8(x: S<u8>) -> S<u8> { x }

pub trait Gat { type G<'a>; }
impl Gat for u32 { type G<'a> = &'a u32; }
pub struct Gs<'a, T: Gat> { g: <T as Gat>::G<'a> }
pub fn gat(x: Gs<'_, u32>) -> usize { std::mem::size_of_val(&x) }

pub struct Fm<'a> { buf: &'a mut u32, n: u32 }
pub struct Arg<'a> { f: fn(&mut Fm<'_>) -> u32, p: &'a u8 }
pub struct H<'a> { a: NonNull<Arg<'a>>, n: usize }
pub fn h(x: H<'_>) -> usize { x.n }

pub type Tait = impl Sized;
pub struct Wl { x: Tait }
#[define_opaque(Tait)]
pub fn tait_def(x: u8) -> Tait { x }
pub type Tait2 = impl std::fmt::Debug;
#[define_opaque(Tait2)]
pub fn tait2_def(x: u8) -> Tait2 { x }
pub type TaitSend = impl Send;
#[define_opaque(TaitSend)]
pub fn tait_send_def(x: u8) -> TaitSend { x }
pub trait Leaky { type Storage; }
impl Leaky for u32 where Wl: Send { type Storage = u32; }
impl Leaky for u16 where Tait2: std::fmt::Debug { type Storage = u16; }
impl Leaky for u64 where Tait: Send { type Storage = u64; }
impl Leaky for i64 where TaitSend: Send { type Storage = i64; }
impl<T: Copy> Leaky for (T,) { type Storage = T; }
pub struct Lk<T: Leaky> { v: <T as Leaky>::Storage }
pub fn lk_auto(x: Lk<u32>) -> Lk<u32> { x }
pub fn lk_nonauto(x: Lk<u16>) -> Lk<u16> { x }
pub fn lk_explicit_auto(x: Lk<i64>) -> Lk<i64> { x }
pub fn lk_bounded(x: Lk<(u32,)>) -> Lk<(u32,)> { x }
pub fn norm_auto(x: <u64 as Leaky>::Storage) -> u64 { x }
pub fn norm_nonauto(x: <u16 as Leaky>::Storage) -> u16 { x }
pub fn norm_explicit_auto(x: <i64 as Leaky>::Storage) -> i64 { x }
pub fn norm_bounded(x: <(u32,) as Leaky>::Storage) -> u32 { x }
pub trait LayoutDependent { type Storage; }
impl LayoutDependent for u128 where u8: std::mem::TransmuteFrom<u8> { type Storage = u8; }
pub fn norm_transmute(x: <u128 as LayoutDependent>::Storage) -> u8 { x }
pub fn norm_leaf(x: <u8 as Prim>::Storage) -> usize { x.len() }
pub fn norm_call(x: <i8 as Prim>::Storage) -> usize { x.len() }

// The specializing impl is harmless, but considering the losing blanket impl
// can reach an opaque. Reject this before inspecting the lossy proof-tree view.
pub trait Losing { type S; }
impl<T> Losing for T where Tait2: std::fmt::Debug { default type S = u8; }
impl Losing for u32 { type S = u16; }
pub struct Loser<T: Losing> { s: <T as Losing>::S }
pub fn losing_opaque(x: Loser<u32>) -> Loser<u32> { x }

// These signatures preserve projections for direct selection/budget probes.
pub fn probe_plain(_: <u32 as Prim>::Storage) {}
pub fn probe_bounded(_: <(u32,) as Leaky>::Storage) {}
pub fn probe_generic<T: Prim>(_: <T as Prim>::Storage) {}
pub fn probe_auto(_: <u64 as Leaky>::Storage) {}
pub fn probe_nonauto(_: <u16 as Leaky>::Storage) {}
pub fn probe_explicit_auto(_: <i64 as Leaky>::Storage) {}
pub fn probe_losing(_: <u32 as Losing>::S) {}

// Trust: keep the older branch's higher-ranked boundary cases under the current
// bounded, all-candidate inertness guard; inspection alone is not exhaustive.
pub trait Higher {}
pub struct HigherPlain;
impl<'a> Higher for &'a HigherPlain {}
pub struct HigherBound;
impl<'a> Higher for &'a HigherBound where Tait2: std::fmt::Debug {}
impl Leaky for i32 where for<'a> &'a HigherPlain: Higher { type Storage = i32; }
impl Leaky for i16 where for<'a> &'a HigherBound: Higher { type Storage = i16; }
pub fn probe_higher_clean(_: <i32 as Leaky>::Storage) {}
pub fn probe_higher_opaque(_: <i16 as Leaky>::Storage) {}
"#;

    struct FixtureFileLoader;

    impl rustc_span::source_map::FileLoader for FixtureFileLoader {
        fn file_exists(&self, path: &Path) -> bool {
            path == Path::new(FIXTURE_PATH)
        }

        fn read_file(&self, path: &Path) -> io::Result<String> {
            if self.file_exists(path) {
                Ok(FIXTURE_SOURCE.into())
            } else {
                Err(io::Error::other("unexpected every_reached_type fixture path"))
            }
        }

        fn read_binary_file(&self, _path: &Path) -> io::Result<Arc<[u8]>> {
            Err(io::Error::other("binary source reads are unsupported in this fixture"))
        }

        fn current_directory(&self) -> io::Result<PathBuf> {
            std::env::current_dir()
        }
    }

    /// Fixture fn name -> (funnel answer for its first parameter's type, that type's
    /// `layout_of` size when the funnel admitted it).
    #[derive(Default)]
    struct FunnelCallbacks {
        answers: BTreeMap<String, (bool, Option<u64>)>,
        /// Fixture fn name (`norm_*`) -> `try_normalize_leak_free` of its first parameter's
        /// UNNORMALIZED type, asked inside the freeze, rendered.
        normalized: BTreeMap<String, Option<String>>,
        ordinary_normalized: BTreeMap<String, (Option<String>, Option<String>)>,
        non_revealing_boundaries: Option<(bool, bool, bool)>,
        selected: BTreeMap<String, bool>,
        // Only next-solver runs use explicit walk limits; the default exercises production.
        limits: Option<(usize, usize)>,
    }

    impl rustc_driver::Callbacks for FunnelCallbacks {
        fn config(&mut self, config: &mut Config) {
            config.file_loader = Some(Box::new(FixtureFileLoader));
        }

        fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
            tcx.sess.dcx().abort_if_errors();
            for owner in tcx.hir_body_owners() {
                let did = owner.to_def_id();
                if tcx.def_kind(did) == rustc_hir::def::DefKind::Const
                    && tcx.item_name(did).as_str() == "LEN"
                {
                    // Even a literal const or primitive layout must not silently
                    // upgrade this policy to the revealing PostAnalysis mode.
                    let env =
                        ty::TypingEnv::new(ty::ParamEnv::empty(), ty::TypingMode::OpaqueAnalysis);
                    let args = ty::GenericArgs::identity_for_item(tcx, did);
                    let cid = rustc_middle::mir::interpret::GlobalId {
                        instance: ty::Instance::new_raw(did, args),
                        promoted: None,
                    };
                    self.non_revealing_boundaries = Some((
                        matches!(
                            tcx.layout_of(env.as_query_input(tcx.types.u8)),
                            Err(ty::layout::LayoutError::TooGeneric(_)),
                        ),
                        matches!(
                            tcx.const_eval_global_id(env, cid, rustc_span::DUMMY_SP),
                            Err(rustc_middle::mir::interpret::ErrorHandled::TooGeneric(_)),
                        ),
                        matches!(ty::Instance::try_resolve(tcx, env, did, args), Ok(None)),
                    ));
                    continue;
                }
                if tcx.def_kind(did) != rustc_hir::def::DefKind::Fn {
                    continue;
                }
                let name = tcx.item_name(did).to_string();
                let sig = tcx.fn_sig(did).instantiate_identity().skip_norm_wip();
                let sig = tcx.instantiate_bound_regions_with_erased(sig);
                // A parameterless fixture fn (`const fn len()`, the `wh` control) is a helper, not a
                // funnel case.
                let Some(&ty) = sig.inputs().first() else { continue };
                if name.starts_with("probe_") {
                    let ty::Alias(_, alias) = *ty.kind() else {
                        panic!("selection probe lost its unnormalized projection: {ty:?}");
                    };
                    let ty::AliasTyKind::Projection { def_id } = alias.kind else {
                        panic!("selection probe is not a trait projection: {alias:?}");
                    };
                    let trait_ref =
                        ty::TraitRef::new_from_args(tcx, tcx.parent(def_id.into()), alias.args);
                    let _frozen = crate::ctfe_reentrancy::enter_building(owner);
                    let selected = match self.limits {
                        Some((max_work, max_depth)) => {
                            crate::ctfe_reentrancy::next_solver_selection_with_limits_for_test(
                                tcx, trait_ref, max_work, max_depth,
                            )
                        }
                        None => crate::ctfe_reentrancy::select_projection_reveal_free(
                            tcx,
                            ty::ParamEnv::empty(),
                            trait_ref,
                        )
                        .is_some(),
                    };
                    self.selected.insert(name, selected);
                    continue;
                }
                // The funnel is asked from inside `mir_built`; ask it there, under the freeze frame
                // the hook holds while it lowers this fn.
                let admitted = {
                    let _frozen = crate::ctfe_reentrancy::enter_building(owner);
                    crate::ctfe_reentrancy::layout_query_is_reentrant_safe_deep(tcx, ty)
                };
                let size = admitted.then(|| {
                    tcx.layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(ty))
                        .expect("an admitted type lays out")
                        .size
                        .bytes()
                });
                if name.starts_with("norm_") {
                    // A leak-free decline must neither reuse nor poison the ordinary
                    // analysis query's answer, even when the opaque's hidden type is known.
                    let ordinary = || {
                        tcx.try_normalize_erasing_regions(
                            ty::TypingEnv::non_body_analysis(tcx, did),
                            ty::Unnormalized::new_wip(ty),
                        )
                        .ok()
                        .map(|t| format!("{t:?}"))
                    };
                    let before = ordinary();
                    let normalized = {
                        let _frozen = crate::ctfe_reentrancy::enter();
                        crate::ctfe_reentrancy::try_normalize_leak_free(
                            tcx,
                            ty::ParamEnv::empty(),
                            ty,
                        )
                    };
                    self.normalized.insert(name.clone(), normalized.map(|t| format!("{t:?}")));
                    self.ordinary_normalized.insert(name.clone(), (before, ordinary()));
                }
                self.answers.insert(name, (admitted, size));
            }
            Compilation::Stop
        }
    }

    fn funnel_answers(
        solver: &str,
    ) -> (BTreeMap<String, (bool, Option<u64>)>, BTreeMap<String, Option<String>>) {
        let callbacks = funnel_answers_with_solver(solver, None);
        (callbacks.answers, callbacks.normalized)
    }

    fn funnel_answers_with_solver(solver: &str, limits: Option<(usize, usize)>) -> FunnelCallbacks {
        let mut callbacks = FunnelCallbacks::default();
        callbacks.limits = limits;
        let args = vec![
            "rustc".into(),
            FIXTURE_PATH.into(),
            "--crate-name".into(),
            "every_reached_type_projections_fixture".into(),
            "--crate-type=lib".into(),
            "--edition=2021".into(),
            "-Zno-codegen".into(),
            "-Zcodegen-backend=dummy".into(),
            format!("-Znext-solver={solver}"),
            "--sysroot".into(),
            compiler_sysroot(),
        ];
        let result =
            rustc_driver::catch_fatal_errors(|| -> rustc_interface::interface::Result<()> {
                rustc_driver::run_compiler(&args, &mut callbacks);
                Ok(())
            });
        assert!(result.is_ok(), "failed to compile the every_reached_type fixture");
        callbacks
    }

    struct LeafProjectionCallbacks {
        prewarm: bool,
        checked: bool,
    }

    impl rustc_driver::Callbacks for LeafProjectionCallbacks {
        fn config(&mut self, config: &mut Config) {
            config.file_loader = Some(Box::new(FixtureFileLoader));
        }

        fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
            tcx.sess.dcx().abort_if_errors();
            let owner_named = |name: &str| {
                tcx.hir_body_owners()
                    .find(|&owner| {
                        matches!(
                            tcx.def_kind(owner.to_def_id()),
                            rustc_hir::def::DefKind::Fn | rustc_hir::def::DefKind::Const
                        ) && tcx.item_name(owner.to_def_id()).as_str() == name
                    })
                    .unwrap_or_else(|| panic!("missing fixture owner {name}"))
            };
            let owner = owner_named("norm_leaf");
            let leaf = owner_named("LEN");
            let input = |owner| {
                let sig = tcx.fn_sig(owner).instantiate_identity().skip_norm_wip();
                tcx.instantiate_bound_regions_with_erased(sig).inputs()[0]
            };
            let alias = input(owner);
            assert!(matches!(alias.kind(), ty::Alias(..)), "keep the unnormalized projection");
            let env = ty::TypingEnv::fully_monomorphized();
            if self.prewarm {
                let _ = tcx
                    .try_normalize_erasing_regions(env, ty::Unnormalized::new_wip(alias))
                    .expect("ordinary post-analysis normalization may prewarm the leaf");
            }
            let normalize = || crate::ctfe_reentrancy::try_normalize_ty_unrevealed(tcx, env, alias);
            {
                let _frozen = crate::ctfe_reentrancy::enter_building(owner);
                // This is the first explicit funnel/normalizer access in this callback
                // when prewarm=false. Rust's earlier analysis may itself have queried LEN;
                // the unchanged run-make additionally tests the actual early THIR front door.
                let normalized = normalize().expect("the selected RHS admits the leaf constant");
                assert!(!normalized.has_aliases(), "{normalized:?}");
                assert!(
                    matches!(normalized.kind(), ty::Array(elem, len) if *elem == tcx.types.u8 && len.try_to_target_usize(tcx) == Some(4))
                );
                assert_eq!(
                    normalize(),
                    Some(normalized),
                    "repeated access cannot change the answer"
                );
                let generic = crate::ctfe_reentrancy::try_normalize_unrevealed(tcx, env, alias);
                assert!(
                    generic.is_none_or(|ty| ty.has_aliases()),
                    "the generic OpaqueAnalysis normalizer cannot finish CTFE: {generic:?}",
                );
                let mir = crate::ty_convert::convert_ty_in_env(tcx, env, alias);
                assert_eq!(
                    mir,
                    trust_types::Ty::Array {
                        elem: Box::new(trust_types::Ty::Int { width: 8, signed: false }),
                        len: 4,
                    },
                );

                // Registration asks about the foreign wrapper itself, while a
                // parent's field walk reaches the identical type one level down.
                // Both paths must use the same admitted RHS before checking flags.
                let field_of = |ty: ty::Ty<'tcx>| {
                    let ty::Adt(adt, args) = ty.kind() else { panic!("expected At<T>: {ty:?}") };
                    let fields = &adt.non_enum_variant().fields;
                    assert_eq!(fields.len(), 1);
                    fields.iter().next().unwrap().ty(tcx, *args).skip_normalization()
                };
                let parent = input(owner_named("at8"));
                let field = field_of(parent);
                assert!(field.has_type_flags(ty::TypeFlags::HAS_TY_PROJECTION));
                for ty in [parent, field] {
                    assert!(crate::ctfe_reentrancy::layout_query_is_reentrant_safe_deep(tcx, ty));
                    assert_eq!(
                        tcx.layout_of(env.as_query_input(ty))
                            .expect("admitted layout")
                            .size
                            .bytes(),
                        4
                    );
                }
                for name in ["ati8", "at16", "at64"] {
                    let parent = input(owner_named(name));
                    for ty in [parent, field_of(parent)] {
                        assert!(
                            !crate::ctfe_reentrancy::layout_query_is_reentrant_safe_deep(tcx, ty),
                            "{name}: callable constants, opaques and nested RHS projections still decline: {ty:?}",
                        );
                    }
                }

                let call = input(owner_named("norm_call"));
                assert!(
                    crate::ctfe_reentrancy::try_normalize_ty_unrevealed(tcx, env, call).is_none()
                );
                {
                    let _unspecified = crate::ctfe_reentrancy::enter();
                    assert!(
                        normalize().is_none(),
                        "a cached result cannot bypass an unnamed frame"
                    );
                    for ty in [parent, field] {
                        assert!(!crate::ctfe_reentrancy::layout_query_is_reentrant_safe_deep(
                            tcx, ty
                        ));
                    }
                    let mir = crate::ty_convert::convert_ty_in_env(tcx, env, alias);
                    assert!(matches!(mir, trust_types::Ty::Unsupported { .. }), "{mir:?}");
                }
                {
                    let _leaf_body = crate::ctfe_reentrancy::enter_building(leaf);
                    assert!(
                        normalize().is_none(),
                        "a cached result cannot bypass the leaf-body frame"
                    );
                    for ty in [parent, field] {
                        assert!(!crate::ctfe_reentrancy::layout_query_is_reentrant_safe_deep(
                            tcx, ty
                        ));
                    }
                }
                assert_eq!(
                    normalize(),
                    Some(normalized),
                    "nested refusal must not poison the answer"
                );
            }
            self.checked = true;
            Compilation::Stop
        }
    }

    #[test]
    fn selected_projection_leaf_normalization_preserves_freeze_and_cache_boundaries() {
        for solver in ["coherence", "globally"] {
            for prewarm in [false, true] {
                eprintln!("leaf projection case: solver={solver}, prewarm={prewarm}");
                let mut callbacks = LeafProjectionCallbacks { prewarm, checked: false };
                let args = vec![
                    "rustc".into(),
                    FIXTURE_PATH.into(),
                    "--crate-name=every_reached_type_projections_fixture".into(),
                    "--crate-type=lib".into(),
                    "--edition=2021".into(),
                    "-Zno-codegen".into(),
                    "-Zcodegen-backend=dummy".into(),
                    format!("-Znext-solver={solver}"),
                    "--sysroot".into(),
                    compiler_sysroot(),
                ];
                let result = rustc_driver::catch_fatal_errors(|| {
                    rustc_driver::run_compiler(&args, &mut callbacks);
                });
                assert!(result.is_ok() && callbacks.checked, "{solver}, prewarm={prewarm}");
            }
        }
    }

    #[test]
    fn leak_free_selection_matches_both_solvers_on_inert_inputs() {
        for solver in ["coherence", "globally"] {
            let callbacks = funnel_answers_with_solver(solver, None);
            assert_eq!(callbacks.selected.get("probe_plain"), Some(&true), "{solver}");
            assert_eq!(callbacks.selected.get("probe_bounded"), Some(&true), "{solver}");
            assert_eq!(callbacks.selected.get("probe_generic"), Some(&false), "{solver}");
            assert_eq!(callbacks.selected.get("probe_auto"), Some(&false), "{solver}");
            assert_eq!(callbacks.selected.get("probe_nonauto"), Some(&false), "{solver}");
            assert_eq!(callbacks.selected.get("probe_explicit_auto"), Some(&false), "{solver}");
            if solver == "globally" {
                // The old selection walk's documented losing-candidate residual is
                // unchanged. The new path must reject this before tree evaluation.
                assert_eq!(callbacks.selected.get("probe_losing"), Some(&false));
            }
            assert_eq!(callbacks.answers.get("losing_opaque"), Some(&(false, None)), "{solver}");
            assert_eq!(callbacks.answers.get("lk_auto"), Some(&(false, None)), "{solver}");
            assert_eq!(callbacks.answers.get("lk_nonauto"), Some(&(false, None)), "{solver}");
            assert_eq!(callbacks.answers.get("lk_explicit_auto"), Some(&(false, None)), "{solver}");
            assert_eq!(callbacks.normalized.get("norm_auto"), Some(&None), "{solver}");
            assert_eq!(
                callbacks.normalized.get("norm_bounded"),
                Some(&Some("u32".into())),
                "{solver}"
            );
        }
    }

    #[test]
    fn opaque_analysis_answers_do_not_reuse_or_poison_ordinary_analysis() {
        for solver in ["coherence", "globally"] {
            let callbacks = funnel_answers_with_solver(solver, None);
            assert_eq!(callbacks.non_revealing_boundaries, Some((true, true, true)), "{solver}");
            assert_eq!(callbacks.normalized.get("norm_auto"), Some(&None), "{solver}");
            assert_eq!(callbacks.normalized.get("norm_transmute"), Some(&None), "{solver}");
            assert_eq!(
                callbacks.ordinary_normalized.get("norm_auto"),
                Some(&(Some("u64".into()), Some("u64".into()))),
                "{solver}: ordinary analysis may leak an auto trait after analysis has finished",
            );
            assert_eq!(
                callbacks.ordinary_normalized.get("norm_transmute"),
                Some(&(Some("u8".into()), Some("u8".into()))),
                "{solver}: ordinary analysis retains builtin transmutability",
            );
            assert_eq!(
                callbacks.normalized.get("norm_explicit_auto"),
                Some(&Some("i64".into())),
                "{solver}: the declared Send bound needs no hidden type",
            );
        }
    }

    #[test]
    fn next_solver_selection_declines_when_the_real_tree_exhausts_a_bound() {
        // The root alone consumes a goal plus a candidate; one unit cannot admit it.
        let one_step = funnel_answers_with_solver("globally", Some((1, 256)));
        assert_eq!(one_step.selected.get("probe_plain"), Some(&false));
        // The bounded impl proves a nested Copy/Sized obligation. A root-only walk
        // must refuse rather than treating the visitor's recursion limit as success.
        let one_level = funnel_answers_with_solver("globally", Some((256, 1)));
        assert_eq!(one_level.selected.get("probe_bounded"), Some(&false));
        let complete = funnel_answers_with_solver("globally", Some((256, 256)));
        assert_eq!(complete.selected.get("probe_plain"), Some(&true));
        assert_eq!(complete.selected.get("probe_bounded"), Some(&true));
    }

    #[test]
    fn monomorphic_projection_and_binder_regions_admit_exactly_the_safe_shapes() {
        for solver in ["coherence", "globally"] {
            check_monomorphic_projection_and_binder_regions(solver);
        }
    }

    fn check_monomorphic_projection_and_binder_regions(solver: &str) {
        let (answers, _) = funnel_answers(solver);
        let get = |name: &str| *answers.get(name).unwrap_or_else(|| panic!("no fixture fn {name}"));

        // L1: the selected impl wrote an alias-free value; `layout_of` agrees on its bytes.
        assert_eq!(get("at32"), (true, Some(4)), "At<u32> reads Align4<u32>");
        // The specializing impl's own, non-`default` item is what codegen selection reads.
        assert_eq!(get("s32"), (true, Some(2)), "S<u32> reads the specializing impl's u16");
        // L3: a local ADT reached under `fn(&mut Fm<'_>)` no longer leaks the binder's region.
        assert_eq!(get("h"), (true, Some(16)), "H<'_> lays out");
        // fix11 (L2): the impl value's constant `LEN` is a literal (a leaf closure), read as 4.
        assert_eq!(get("at8"), (true, Some(4)), "an impl value [u8; LEN] with LEN a leaf constant");

        // Declines: each would ask more than the funnel's argument covers.
        assert_eq!(get("ati8"), (false, None), "an impl value whose const calls a const fn (CTFE)");
        // fix11 (CTFE-IN-MIR-BUILT-1): selection would CONFIRM `[(); len()]: Sized`, i.e.
        // evaluate `len()`; inside the freeze the projection is not selected.
        assert_eq!(
            get("wh"),
            (false, None),
            "a candidate impl whose where-clause names a constant"
        );
        // A candidate is read at the arguments it applies at: `impl<T: Easy> Wq for (T, T)` at
        // `(u8, u8)` confirms `u8: Easy`, whose one impl is inert; `impl<T: Hard> Wq for [T; 1]`
        // at `[u8; 1]` confirms `u8: Hard`, whose impl names a constant, and declines.
        assert_eq!(
            get("wh_easy"),
            (true, Some(2)),
            "a trait bound of a primitive with inert impls"
        );
        assert_eq!(get("wh_hard"), (false, None), "a trait bound whose impl names a constant");
        // fix11 L2 review: `u8: Tailed`'s one impl carries `TailT: Sized`, an alias-free clause whose
        // proof normalizes `TailT`'s tail `<u16 as Tl>::S` (an impl whose where-clauses could
        // evaluate a constant: tests/ui/trust/sized_tail_clause_ctfe_no_query_cycle.rs).
        assert_eq!(get("wh_tail"), (false, None), "a bound whose impl's Sized clause reads a tail");
        assert_eq!(get("at16"), (false, None), "an impl value that is an opaque (a reveal)");
        assert_eq!(get("at64"), (false, None), "an impl value that is itself a projection");
        assert_eq!(get("at_generic"), (false, None), "a generic argument");
        assert_eq!(get("s8"), (false, None), "a `default` item");
        assert_eq!(get("gat"), (false, None), "a generic associated type");
    }

    /// OPAQUE-IMPL-WHERE-LEAK-1: a codegen-mode selection of `u32: Leaky` confirms `Wl: Send`,
    /// which reveals `Tait` through `Wl`'s field, and one of `u16: Leaky` normalizes `Tait2: Debug`,
    /// which reveals `Tait2`; inside `mir_built` of either opaque's defining body that is an E0391
    /// on valid Rust. The funnel declines both projections and the leak-free normalizer refuses
    /// the auto-trait one, while `(u32,)`'s impl, whose where-clause (`T: Copy`) names no opaque,
    /// is read and normalized as before.
    #[test]
    fn an_impl_where_clause_naming_an_opaque_declines_the_projection() {
        for solver in ["coherence", "globally"] {
            check_impl_where_clause_naming_an_opaque(solver);
        }
    }

    fn check_impl_where_clause_naming_an_opaque(solver: &str) {
        let (answers, normalized) = funnel_answers(solver);
        let get = |name: &str| *answers.get(name).unwrap_or_else(|| panic!("no fixture fn {name}"));
        let norm = |name: &str| {
            normalized.get(name).unwrap_or_else(|| panic!("no fixture fn {name}")).clone()
        };

        assert_eq!(get("lk_auto"), (false, None), "`Wl: Send` reaches `Tait` through a field");
        assert_eq!(get("lk_nonauto"), (false, None), "`Tait2: Debug` names the opaque");
        assert_eq!(
            get("lk_explicit_auto"),
            (false, None),
            "a declared Send bound still names an opaque"
        );
        // fix11 L2's const-inert gate, asked first inside the freeze, checks `T: Copy` at `u32` and
        // admits it; the leak-free walk then finds nothing naming an opaque.
        assert_eq!(get("lk_bounded"), (true, Some(4)), "`u32: Copy` names no opaque");

        // The auto-trait goal is asked of the opaque itself (`impl Leaky for u64 where Tait: Send`).
        // Every leak-free question carries `leak_free_infcx`'s `'?0: 'static` clause, which keeps it
        // out of the old solver's GLOBAL caches (OPAQUE-IMPL-WHERE-LEAK-2), so the leaking answer
        // typeck cached for the same goal after analysis is never read here: the ambiguity is
        // deterministic.
        assert_eq!(norm("norm_auto"), None, "the auto-trait goal on `Tait` is ambiguous");
        assert_eq!(
            norm("norm_bounded"),
            Some("u32".to_string()),
            "a clean where-clause normalizes"
        );
        // `Tait2: Debug` holds from the opaque's own bound without revealing it: an ANALYSIS
        // question may answer it (only the codegen-mode selection above must not).
        assert_eq!(
            norm("norm_nonauto"),
            Some("u16".to_string()),
            "{solver}: a bound answers `Tait2: Debug`",
        );
    }

    // Trust: successful higher-ranked goals must not hide opaque-bearing children.
    //
    // The old solver walks the selection's nested obligations, a higher-ranked one
    // included, so the clean where-clause selects and the opaque one is refused.
    //
    // The next solver's narrow selected-projection fallback
    // (`next_solver_reveal_free::select`) admits only a subset of those
    // projections. Its `inert_input` preflight (`selection_is_const_inert`) refuses
    // every candidate impl whose where-clause is neither inert as written nor a
    // primitive-scalar bound, and `for<'a> &'a HigherPlain: Higher` is neither. So
    // both probes are refused there before the proof-tree audit runs. Merge
    // 37799e5bae added this test expecting `true` under `globally`, but neither
    // parent nor any later commit admitted it: the test was red from the start.
    // The complete codegen path's check of an opaque child under a higher-ranked
    // goal, with the next solver, is pinned by `bounds_only_controls::
    // global_next_solver_keeps_safe_selections_and_walks_opaque_obligations`
    // (`norm_higher_safe` selects, `norm_higher` refuses).
    #[test]
    fn higher_ranked_selection_checks_opaque_children_with_both_solvers() {
        let old = funnel_answers_with_solver("no", None);
        assert_eq!(old.selected.get("probe_higher_clean"), Some(&true), "no");
        assert_eq!(old.selected.get("probe_higher_opaque"), Some(&false), "no");
        let next = funnel_answers_with_solver("globally", None);
        assert_eq!(next.selected.get("probe_higher_clean"), Some(&false), "globally: preflight");
        assert_eq!(next.selected.get("probe_higher_opaque"), Some(&false), "globally");
        // Positive control: the same narrow path still admits an inert input.
        assert_eq!(next.selected.get("probe_plain"), Some(&true), "globally: positive control");
    }
}
