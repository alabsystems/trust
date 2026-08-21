//@ check-pass
//@ compile-flags: -Z trust-ir-lower -Z trust-verify=off

// Trust (vtable slice 18): the trait-object key's NOMINAL half.
//
// Slice 17 made the principal key faithful, but rendered principal arguments and
// associated-type binding terms through `trust_types::Ty`'s CLOSED grammar, whose
// `Ty::Adt` carries a GENERICS-ERASED def path — `Vec<i32>` and `Vec<u64>` share one
// `name`. Admitting that would have re-opened the very merge slice 17 closed, so the
// grammar refused every nominal argument. Refusing was correct; it cost six clean rows.
//
// A def path plus RECURSIVELY RENDERED generic arguments IS injective where the erased
// name is not, and `faithful_principal_key` holds a `tcx`. So the nominal arm is now
// rendered rather than refused, in two halves:
//
//   * `trust_mir_extract::faithful_key_skeleton` walks the RUSTC type into
//     `trust_types::VtableKeyTy` — the `tcx` half: def paths and argument trees;
//   * `trust_types::VtableKeyTy::render_in_body` renders it — pure, and in `trust-types`
//     because that is where it can be unit-tested at all (`trust-mir-extract` is
//     workspace-EXCLUDED for `rustc_private`, so its tests cannot run under `targo`).
//
// STILL ONE RENDERER, which is the non-negotiable: both `tcx`-holding callers reach it
// through `faithful_principal_key`, and the MIR-side bridge holds no `tcx` and only
// HASHES the string it was handed. ZERO CHURN is BY CONSTRUCTION, not by inspection —
// the pre-slice-18 renderer runs FIRST at every node and its result is used verbatim.
//
// EVERY function below must keep COMPILING — a lowering decline is a coverage decision,
// never an error.

use std::fmt::Debug;

// ------------------------------------------------- the recovered lane

struct Wrapper;
struct Other;

trait Take<U> {
    fn t(&self) -> u32;
}
impl Take<Wrapper> for i32 {
    fn t(&self) -> u32 {
        1
    }
}
impl Take<Other> for i32 {
    fn t(&self) -> u32 {
        2
    }
}

// THE RECOVERY PIN, and the injectivity obligation in one body. Two NOMINAL principal
// arguments over one trait path and one source type: slice 17 refused both
// (`Ty(dyn principal arg: nominal)`), and under the pre-slice-17 erasure they had shared
// ONE key. They must now render, and render DIFFERENTLY.
fn two_nominal_principal_args(x: &i32) -> u32 {
    let a: &dyn Take<Wrapper> = x;
    let b: &dyn Take<Other> = x;
    a.t() + b.t()
}

struct Holder<T>(T);

impl Take<Holder<i32>> for u8 {
    fn t(&self) -> u32 {
        3
    }
}
impl Take<Holder<u64>> for u8 {
    fn t(&self) -> u32 {
        4
    }
}

// The separation where the two nominals differ ONLY in their generic argument — exactly
// what the erased `Ty::Adt.name` could not express, and the reason admitting `Adt` under
// that name would have been the same merge in another costume.
fn generic_nominal_args_separate(x: &u8) -> u32 {
    let a: &dyn Take<Holder<i32>> = x;
    let b: &dyn Take<Holder<u64>> = x;
    a.t() + b.t()
}

impl Take<Holder<Holder<i32>>> for u16 {
    fn t(&self) -> u32 {
        5
    }
}
impl Take<Holder<Holder<u64>>> for u16 {
    fn t(&self) -> u32 {
        6
    }
}

// NESTED, because a one-level key would be a trick rather than a property.
fn nested_generic_nominal_args_separate(x: &u16) -> u32 {
    let a: &dyn Take<Holder<Holder<i32>>> = x;
    let b: &dyn Take<Holder<Holder<u64>>> = x;
    a.t() + b.t()
}

mod a {
    pub struct Foo;
}
mod b {
    pub struct Foo;
}
impl Take<a::Foo> for i64 {
    fn t(&self) -> u32 {
        7
    }
}
impl Take<b::Foo> for i64 {
    fn t(&self) -> u32 {
        8
    }
}

// Two DISTINCT ADTs sharing a LAST PATH SEGMENT. The WHOLE def path is in the key, so a
// leaf-name rendering — the same class of merge as the erased generics — is excluded.
fn same_last_segment_different_adts(x: &i64) -> u32 {
    let p: &dyn Take<a::Foo> = x;
    let q: &dyn Take<b::Foo> = x;
    p.t() + q.t()
}

// ------------------------------------------------- the ASSOCIATED-BINDING half

trait Assoc {
    type Out;
    fn o(&self) -> u32;
}
struct WrapOut;
impl Assoc for WrapOut {
    type Out = Wrapper;
    fn o(&self) -> u32 {
        9
    }
}

// The binding TERM is nominal. This is the corpus's biggest slice-17 refusal bucket
// (`Ty(dyn assoc binding: nominal)`, 15 hits) and it is the SAME renderer, not a second
// one — the term and a principal argument travel through one function.
fn nominal_assoc_binding(w: &WrapOut) -> u32 {
    let d: &dyn Assoc<Out = Wrapper> = w;
    d.o()
}

struct HolderOutA;
struct HolderOutB;
impl Assoc for HolderOutA {
    type Out = Holder<i32>;
    fn o(&self) -> u32 {
        10
    }
}
impl Assoc for HolderOutB {
    type Out = Holder<u64>;
    fn o(&self) -> u32 {
        11
    }
}

// `Out = Holder<i32>` and `Out = Holder<u64>` share a principal path AND a binding NAME,
// so the TERM is the only thing that can separate them.
fn nominal_assoc_binding_terms_separate(x: &HolderOutA, y: &HolderOutB) -> u32 {
    let p: &dyn Assoc<Out = Holder<i32>> = x;
    let q: &dyn Assoc<Out = Holder<u64>> = y;
    p.o() + q.o()
}

// ------------------------------------------------- composites over nominals

pub struct Path;

// `dyn FnMut(&Path)` desugars to `FnMut<(&Path,)>` — a nominal leaf under a REF under a
// TUPLE. This shape is what carries the whole `Fn` family into the nominal lane
// (`boxed_closure_with_borrowed_param::tester` in the corpus).
fn fn_family_over_nominal_arg() -> u32 {
    let mut f: Box<dyn FnMut(&Path) -> u32> = Box::new(|_p: &Path| 12);
    let p = Path;
    f(&p)
}

// A PARAM argument (keyable since slice 17, and still BODY-SCOPED) plus a nominal binding
// term that itself contains BOTH a param and a nominal — `Result<O, String>`, the shape
// of `move_closure_can_call_captured_fnmut::compose`. A param nested inside a nominal
// keeps its `@{owner}` scope, so two bodies' `Result<O, String>` cannot merge.
fn param_nested_in_nominal_binding<I: 'static, O: 'static>() -> u32 {
    let _f: Box<dyn FnMut(I) -> Result<O, String>> =
        Box::new(|_x: I| Err::<O, String>("e".to_string()));
    13
}

struct Ctxt<'tcx> {
    _x: &'tcx u32,
}

fn bother_hrtb(_c: &mut Ctxt<'_>) -> u32 {
    14
}

// A nominal whose only generic arguments are LIFETIMES erases to an ARGLESS path — the
// slice-17 region rule, now applied at every depth. Counting `'b` here would refuse a
// real shape (`regions_relate_bound_regions_on_closures_to_inference_variables::bother`).
fn lifetime_only_nominal_arg() -> u32 {
    let mut f: Box<dyn for<'b> FnMut(&mut Ctxt<'b>) -> u32> = Box::new(bother_hrtb);
    let n = 0u32;
    let mut c = Ctxt { _x: &n };
    f(&mut c)
}

// ------------------------------------------------- ZERO-CHURN controls

// An args-free principal keys BYTE-IDENTICALLY to its pre-slice-17 spelling
// (`__trust_vtable__core::fmt::Debug$i32__`): the renderer returns the argless def path
// VERBATIM, and slice 18 does not reach that path at all.
fn args_free_principal_still_mints(x: &i32) -> u32 {
    let d: &dyn Debug = x;
    let _ = d;
    15
}

trait Convert<U> {
    fn convert(&self) -> u32;
}
impl Convert<u32> for i32 {
    fn convert(&self) -> u32 {
        16
    }
}
impl Convert<u64> for i32 {
    fn convert(&self) -> u32 {
        17
    }
}

// SCALAR arguments were already admitted in slice 17 and must not move: the closed
// grammar runs FIRST at every node, so `i32`/`u64` keep their exact spellings.
fn scalar_args_unchanged(x: &i32) -> u32 {
    let a: &dyn Convert<u32> = x;
    let b: &dyn Convert<u64> = x;
    a.convert() + b.convert()
}

trait Speak {
    fn speak(&self) -> u32;
}
struct Dog;
impl Speak for Dog {
    fn speak(&self) -> u32 {
        18
    }
}

// A bare-param SOURCE stays `param(T/#0)@{owner}` (slice 17 part B), unmoved.
fn param_source<T: Speak>(t: &T) -> &dyn Speak {
    t
}

// ------------------------------------------------- what STILL refuses, and why

impl Take<Box<str>> for i32 {
    fn t(&self) -> u32 {
        19
    }
}

// An UNSIZED argument has no canonical spelling in this grammar and still refuses. Note
// the tag MIGRATES from `nominal` to `unsized` once the unsized type sits inside a
// nominal that now renders — that is honest per-shape attribution, not a regression.
fn unsized_inside_nominal_refuses(x: &i32) -> u32 {
    let d: &dyn Take<Box<str>> = x;
    d.t()
}

struct Fixed<const N: usize>;
impl Take<Holder<Fixed<3>>> for i32 {
    fn t(&self) -> u32 {
        20
    }
}

// A CONST generic argument would merge `Fixed<3>` with `Fixed<4>` if dropped, so it
// refuses with its OWN tag (`nominal const-generic`) rather than being silently omitted.
fn const_generic_inside_nominal_refuses(x: &i32) -> u32 {
    let d: &dyn Take<Holder<Fixed<3>>> = x;
    d.t()
}

// Principal-less `dyn Send` still fails closed on both sides — no def path to key on.
fn principal_less(x: &u32) -> &dyn Send {
    x
}

trait Upcastable {
    fn u(&self) -> u32;
}
impl Upcastable for i32 {
    fn u(&self) -> u32 {
        21
    }
}

// THE NEGATIVE RESULT, recorded so nobody "recovers" it later. `impl Deref for dyn Trait
// + Send + Sync { type Target = dyn Trait; }` (`issue_108155::{impl#0}::deref`) lowered
// clean before slice 17 ONLY because both types spelled one `trait_id` under the
// auto-trait erasure, which made `self -> return` look like an identity pass-through.
// Correctly distinguished, it is a real dyn UPCAST, which the producer fail-closes. That
// clean row existed BECAUSE two distinct types were merged — it is the fail-open being
// observed, not a regression, and no nominal rendering can or should recover it.
fn auto_trait_separation_is_a_real_upcast(x: &(dyn Upcastable + Send + Sync)) -> &dyn Upcastable {
    x
}

fn main() {
    assert_eq!(two_nominal_principal_args(&0i32), 3);
    assert_eq!(generic_nominal_args_separate(&0u8), 7);
    assert_eq!(nested_generic_nominal_args_separate(&0u16), 11);
    assert_eq!(same_last_segment_different_adts(&0i64), 15);

    assert_eq!(nominal_assoc_binding(&WrapOut), 9);
    assert_eq!(nominal_assoc_binding_terms_separate(&HolderOutA, &HolderOutB), 21);

    assert_eq!(fn_family_over_nominal_arg(), 12);
    assert_eq!(param_nested_in_nominal_binding::<u8, u8>(), 13);
    assert_eq!(lifetime_only_nominal_arg(), 14);

    assert_eq!(args_free_principal_still_mints(&0i32), 15);
    assert_eq!(scalar_args_unchanged(&0i32), 33);
    assert_eq!(param_source(&Dog).speak(), 18);

    assert_eq!(unsized_inside_nominal_refuses(&0i32), 19);
    assert_eq!(const_generic_inside_nominal_refuses(&0i32), 20);
    let n = 0u32;
    let _ = principal_less(&n);
    assert_eq!(auto_trait_separation_is_a_real_upcast(&1i32).u(), 21);
}
