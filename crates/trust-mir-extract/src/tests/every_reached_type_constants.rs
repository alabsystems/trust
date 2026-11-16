// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: MIT OR Apache-2.0

//! fix11 (L2): the #48 layout funnel (`ctfe_reentrancy::layout_query_is_reentrant_safe_deep`)
//! declined every local struct whose field type names an UNEVALUATED constant — `[u8; N]`,
//! `[u8; Self::MAX_DIGITS]`, `pattern_type!(u32 is 1..)` (whose open end is the anonymous
//! constant `<u32 as RangePattern>::MAX`) — because `layout_of` evaluates it, and CTFE from
//! inside `mir_built` is an E0391 risk. In `core` that withheld the layout of every
//! `NonZero<uN>` (through `niche_types::*Inner`) and of `DecimalSeq`.
//!
//! The funnel now evaluates exactly the constants whose whole CTFE closure is LEAF (literals,
//! operators, casts, statement-free blocks, paths to further leaf constants and
//! `size_of`/`align_of` over a primitive, `()` or a pointer to one, all of primitive type; a
//! trait constant through the one impl that can apply, read without asking selection; a
//! foreign constant whose arguments name no local def) — a closure that builds no body but its
//! own leaves, so it cannot reach a query already on the stack — and that no freeze frame on
//! this thread forbids. These tests pin the admitted shapes (`TypeId`'s
//! `16 / size_of::<*const ()>()` among them), with `layout_of`'s bytes, and every decline that
//! keeps that argument: a const fn call, `size_of` over an ADT, a method call, a block with a statement, a trait constant selected over a
//! non-primitive argument, through a blanket impl, through a where-claused impl or through the
//! trait's default, a const fn whose body names the struct the constant sizes (the cycle
//! shape: `S { a: [u8; f()] }` with `f` mentioning `S`); every decline of the gate `typeck` of a
//! leaf-shaped body is asked behind (a where-clause naming a constant on the trait constant's
//! impl, on an inherent impl a `Type::NAME` path probes, on an impl of a trait in scope that
//! names the same item, and on an operator trait's impl over a primitive); an enum whose
//! explicit discriminant calls; a `Sized` where-clause whose proof's struct-tail chain names a
//! projection (fix11 L2 review: proving it normalizes the projection, whose impl's where-clauses
//! can evaluate a constant); and the freeze frames: nothing is evaluated while a frame
//! lowers a body some leaf closure could contain (here `N` itself) or names no body, and a frame
//! lowering a constant of struct type (`ARR_ZERO`), a primitive constant that calls
//! (`NOT_LEAF`) or a `fn` forbids nothing.

use super::*;

const FIXTURE_PATH: &str = "every_reached_type_constants_fixture.rs";
const FIXTURE_SOURCE: &str = r#"
#![feature(pattern_types, pattern_type_macro)]
#![allow(dead_code)]
use std::pat::pattern_type;

const N: usize = 4;
const M: usize = N * 2 + (3u8 as usize);
pub struct Arr { a: [u8; N] }
pub struct Arr2 { a: [u16; M] }
pub struct DSeq { n: usize, digits: [u8; Self::LEN] }
impl DSeq { pub const LEN: usize = 768; }
pub trait Bound { const MAX: Self; }
impl Bound for u32 { const MAX: u32 = <u32>::MAX - 1; }
pub struct Tr { a: [u8; <u32 as Bound>::MAX as usize % 7] }
pub struct Nz(pattern_type!(u32 is 1..));
pub struct Outer { x: Option<Arr>, y: (Arr2, u8) }
pub trait Prim { type Storage; }
impl Prim for u8 { type Storage = [u8; N]; }
pub struct At<T: Prim> { v: <T as Prim>::Storage }

pub fn arr(x: Arr) -> Arr { x }
pub fn arr2(x: Arr2) -> Arr2 { x }
pub fn dseq(x: DSeq) -> DSeq { x }
pub fn tr(x: Tr) -> Tr { x }
pub fn nz(x: Option<Nz>) -> Option<Nz> { x }
pub fn outer(x: Outer) -> Outer { x }
pub fn proj_leaf(x: At<u8>) -> At<u8> { x }

const fn four() -> usize { 4 }
pub struct Call { a: [u8; four()] }
pub struct TypeIdLike { d: [*const (); 16 / std::mem::size_of::<*const ()>()] }
pub struct SzU32 { a: [u8; core::mem::size_of::<u32>() + std::mem::align_of::<&u16>()] }
pub struct SzAdt { a: [u8; std::mem::size_of::<Arr>()] }
const SL: usize = "abcd".len();
pub struct Method { a: [u8; SL] }
const WS: usize = { let x = 3; x };
pub struct Stmt { a: [u8; WS] }
pub struct Loc;
pub trait K { const V: usize; }
impl K for Loc { const V: usize = 3; }
pub struct ViaLoc { a: [u8; <Loc as K>::V] }
pub struct Cyc { a: [u8; sized_by_cyc()] }
const fn sized_by_cyc() -> usize { let _r: Option<&Cyc> = None; 4 }
impl Prim for u16 { type Storage = [u8; four()]; }
pub trait Bl { const V: usize; }
impl<T> Bl for T { const V: usize = 3; }
pub struct Blanket { a: [u8; <u32 as Bl>::V] }
pub trait Wc { const V: usize; }
impl Wc for u32 where u32: Copy { const V: usize = 1; }
pub struct WhereImpl { a: [u8; <u32 as Wc>::V] }
pub trait Df { const V: usize = 5; }
impl Df for u32 {}
pub struct ViaDefault { a: [u8; <u32 as Df>::V] }

pub const ARR_ZERO: Arr = Arr { a: [0; N] };
pub const NOT_LEAF: usize = four() + 1;

// (Its constant is not called `MAX`: a trait in scope with an item of that name is a candidate
// the gate checks for every `Type::MAX` path in this module, `<u32>::MAX` among them.)
pub trait Bd2 { const TOP: usize; }
impl Bd2 for u32 where [(); four()]: Sized { const TOP: usize = 1; }
const CW: usize = <u32 as Bd2>::TOP;
pub struct TraitWhere { a: [u8; CW] }
pub struct Dw;
impl Dw where [(); four()]: Sized { pub const LEN: usize = 3; }
pub struct InherentWhere { a: [u8; Dw::LEN] }
pub struct Dt;
impl Dt { pub const SIZE: usize = 2; }
pub trait HasSize { const SIZE: usize; }
impl HasSize for u8 where [(); four()]: Sized { const SIZE: usize = 1; }
pub struct InScopeTrait { a: [u8; Dt::SIZE] }
pub struct Lo;
impl core::ops::BitXor<Lo> for u32 where [(); four()]: Sized {
    type Output = u32;
    fn bitxor(self, _: Lo) -> u32 { self }
}
const XO: usize = 6 ^ 3;
pub struct OpImpl { a: [u8; XO] }
pub enum Ed { A = four() as isize, B }
pub enum El { A = 3, B = -1, C }

pub trait Pt { type S; }
impl Pt for u16 { type S = u8; }
pub struct TailP { s: <u16 as Pt>::S }
pub struct Plain { a: u16, b: u8 }
pub struct Ds;
impl Ds where Plain: Sized { pub const DEPTH: usize = 3; }
pub struct SizedPlain { a: [u8; Ds::DEPTH] }
pub struct Dq;
impl Dq where TailP: Sized { pub const DEPTH: usize = 3; }
pub struct SizedTail { a: [u8; Dq::DEPTH] }

pub fn sized_plain(x: SizedPlain) -> SizedPlain { x }
pub fn sized_tail(x: SizedTail) -> SizedTail { x }
pub fn trait_where(x: TraitWhere) -> TraitWhere { x }
pub fn inherent_where(x: InherentWhere) -> InherentWhere { x }
pub fn in_scope_trait(x: InScopeTrait) -> InScopeTrait { x }
pub fn op_impl(x: OpImpl) -> OpImpl { x }
pub fn ed(x: Ed) -> Ed { x }
pub fn el(x: El) -> El { x }
pub fn call(x: Call) -> Call { x }
pub fn tyid(x: TypeIdLike) -> TypeIdLike { x }
pub fn sz_u32(x: SzU32) -> SzU32 { x }
pub fn sz_adt(x: SzAdt) -> SzAdt { x }
pub fn method(x: Method) -> Method { x }
pub fn stmt(x: Stmt) -> Stmt { x }
pub fn via_loc(x: ViaLoc) -> ViaLoc { x }
pub fn cyc(x: Cyc) -> Cyc { x }
pub fn proj_call(x: At<u16>) -> At<u16> { x }
pub fn blanket(x: Blanket) -> Blanket { x }
pub fn where_impl(x: WhereImpl) -> WhereImpl { x }
pub fn via_default(x: ViaDefault) -> ViaDefault { x }
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
            Err(io::Error::other("unexpected every_reached_type_constants fixture path"))
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
    /// The funnel's answer for `Arr` (`[u8; N]`) under five freeze frames: the hook "lowering"
    /// the constant `N` itself (`ctfe_reentrancy::enter_building`), a frame that names no body
    /// (`ctfe_reentrancy::enter`), the hook lowering the struct-typed constant `ARR_ZERO`, the
    /// hook lowering `N` inside the hook lowering `fn arr` (nested frames), and the hook
    /// lowering `NOT_LEAF`, a `usize` constant that calls (no leaf closure can contain it).
    arr_frames: Option<[bool; 5]>,
}

impl rustc_driver::Callbacks for FunnelCallbacks {
    fn config(&mut self, config: &mut Config) {
        config.file_loader = Some(Box::new(FixtureFileLoader));
    }

    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        tcx.sess.dcx().abort_if_errors();
        for owner in tcx.hir_body_owners() {
            let did = owner.to_def_id();
            if tcx.def_kind(did) != rustc_hir::def::DefKind::Fn {
                continue;
            }
            let name = tcx.item_name(did).to_string();
            let sig = tcx.fn_sig(did).instantiate_identity().skip_norm_wip();
            let sig = tcx.instantiate_bound_regions_with_erased(sig);
            let Some(&ty) = sig.inputs().first() else { continue };
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
            self.answers.insert(name, (admitted, size));
        }
        // The freeze-frame rule: inside `N`'s own lowering, `[u8; N]` is not evaluated (its
        // CTFE would demand the query lowering `N`), nor under a frame that names no body; a
        // frame lowering a constant of struct type cannot be a leaf body and forbids nothing.
        let owner = |kind: rustc_hir::def::DefKind, name: &str| {
            tcx.hir_body_owners()
                .find(|d| tcx.def_kind(*d) == kind && tcx.item_name(d.to_def_id()).as_str() == name)
                .unwrap_or_else(|| panic!("fixture body {name}"))
        };
        let konst = rustc_hir::def::DefKind::Const;
        let n = owner(konst, "N");
        let arr_zero = owner(konst, "ARR_ZERO");
        let not_leaf = owner(konst, "NOT_LEAF");
        let arr = owner(rustc_hir::def::DefKind::Fn, "arr");
        let sig = tcx.fn_sig(arr.to_def_id()).instantiate_identity().skip_norm_wip();
        let arr_ty = tcx.instantiate_bound_regions_with_erased(sig).inputs()[0];
        let ask = || crate::ctfe_reentrancy::layout_query_is_reentrant_safe_deep(tcx, arr_ty);
        let while_building_n = {
            let _building = crate::ctfe_reentrancy::enter_building(n);
            ask()
        };
        let unnamed = {
            let _frozen = crate::ctfe_reentrancy::enter();
            ask()
        };
        let while_building_arr_zero = {
            let _building = crate::ctfe_reentrancy::enter_building(arr_zero);
            ask()
        };
        let nested = {
            let _outer = crate::ctfe_reentrancy::enter_building(arr);
            let _inner = crate::ctfe_reentrancy::enter_building(n);
            ask()
        };
        let while_building_not_leaf = {
            let _building = crate::ctfe_reentrancy::enter_building(not_leaf);
            ask()
        };
        self.arr_frames = Some([
            while_building_n,
            unnamed,
            while_building_arr_zero,
            nested,
            while_building_not_leaf,
        ]);
        Compilation::Stop
    }
}

fn funnel_answers() -> FunnelCallbacks {
    let mut callbacks = FunnelCallbacks::default();
    let args = vec![
        "rustc".into(),
        FIXTURE_PATH.into(),
        "--crate-name".into(),
        "every_reached_type_constants_fixture".into(),
        "--crate-type=lib".into(),
        "--edition=2021".into(),
        "-Zno-codegen".into(),
        "-Zcodegen-backend=dummy".into(),
        "--sysroot".into(),
        compiler_sysroot(),
    ];
    let result = rustc_driver::catch_fatal_errors(|| -> rustc_interface::interface::Result<()> {
        rustc_driver::run_compiler(&args, &mut callbacks);
        Ok(())
    });
    assert!(result.is_ok(), "failed to compile the every_reached_type_constants fixture");
    callbacks
}

#[test]
fn leaf_closure_constants_admit_and_every_other_constant_declines() {
    let callbacks = funnel_answers();
    let answers = &callbacks.answers;
    let get = |name: &str| *answers.get(name).unwrap_or_else(|| panic!("no fixture fn {name}"));

    // Admitted: every constant's CTFE closure is leaf; `layout_of` agrees on the bytes.
    assert_eq!(get("arr"), (true, Some(4)), "[u8; N], N a literal const");
    assert_eq!(get("arr2"), (true, Some(22)), "[u16; N * 2 + (3u8 as usize)]");
    assert_eq!(get("dseq"), (true, Some(776)), "[u8; Self::LEN], an inherent assoc const");
    assert_eq!(get("tr"), (true, Some(2)), "a local trait const, selected over u32");
    // The open end `<u32 as RangePattern>::MAX` is a foreign trait constant: the niche
    // `Option` uses is the one the evaluated range gives (4 bytes, not 8).
    assert_eq!(get("nz"), (true, Some(4)), "Option<pattern_type!(u32 is 1..)>");
    assert_eq!(get("outer"), (true, Some(30)), "leaf-sized structs nested in std ADTs");
    assert_eq!(get("proj_leaf"), (true, Some(4)), "an impl value [u8; N] (L1 + L2)");

    // Declines: each evaluation would run more than leaf bodies.
    assert_eq!(get("call"), (false, None), "a const fn call");
    // The one call a leaf body may make: `size_of`/`align_of` over a layout-primitive type.
    assert_eq!(get("tyid"), (true, Some(16)), "TypeId's 16 / size_of::<*const ()>()");
    assert_eq!(get("sz_u32"), (true, Some(12)), "size_of::<u32>() + align_of::<&u16>()");
    assert_eq!(get("sz_adt"), (false, None), "size_of over an ADT (its layout is not leaf)");
    assert_eq!(get("method"), (false, None), "a method call");
    assert_eq!(get("stmt"), (false, None), "a block with a statement");
    assert_eq!(get("via_loc"), (false, None), "a trait const selected over a local ADT");
    assert_eq!(get("cyc"), (false, None), "a const fn that names the struct it sizes");
    assert_eq!(get("proj_call"), (false, None), "an impl value sized by a const fn call");
    assert_eq!(get("blanket"), (false, None), "a trait const whose trait has a blanket impl");
    assert_eq!(get("where_impl"), (false, None), "a trait const through a where-claused impl");
    assert_eq!(get("via_default"), (false, None), "a trait const the impl does not define");

    // The gate `typeck` of a leaf-shaped body is asked behind: each would let that `typeck`
    // select or probe a candidate whose where-clause evaluates `four()`.
    assert_eq!(get("trait_where"), (false, None), "a trait constant's impl names a constant");
    assert_eq!(get("inherent_where"), (false, None), "an inherent impl the probe considers");
    assert_eq!(get("in_scope_trait"), (false, None), "an in-scope trait with the same item");
    assert_eq!(get("op_impl"), (false, None), "an operator trait's impl over a primitive");
    // A `Sized` where-clause is inert only when its proof's struct-tail chain names no alias:
    // proving `TailP: Sized` normalizes `<u16 as Pt>::S`, selecting an impl whose where-clauses
    // could evaluate a constant (tests/ui/trust/sized_tail_clause_ctfe_no_query_cycle.rs).
    assert_eq!(get("sized_plain"), (true, Some(3)), "a Sized clause over an alias-free tail");
    assert_eq!(get("sized_tail"), (false, None), "a Sized clause over a projection tail");
    // `layout_of` of a local enum evaluates its explicit discriminants.
    assert_eq!(get("ed"), (false, None), "an explicit discriminant that calls a const fn");
    assert_eq!(get("el"), (true, Some(1)), "literal discriminants (-1..=3 fits an i8)");

    // Freeze frames, for `Arr` (`[u8; N]`): declined while `N` itself is lowered and under a
    // frame that names no body; admitted while the struct-typed constant `ARR_ZERO` is
    // lowered; declined when `N`'s lowering is nested inside `fn arr`'s; admitted while the
    // `usize` constant `NOT_LEAF` (it calls, so no leaf closure contains it) is lowered.
    assert_eq!(callbacks.arr_frames, Some([false, false, true, false, true]));
}
