//@ check-pass
//@ compile-flags: -Z trust-ir-lower -Z trust-verify=off

// Trust (vtable slice 17): the trait-object IDENTITY was generics-erased, and that was a
// live fail-open in shipped code. `trust_types::Ty::Dynamic { trait_name }` records the
// principal trait's def path and NOTHING else, so `dyn Convert<u32>` and
// `dyn Convert<u64>` rendered ONE string. Two things were keyed on it:
//
//   * the vtable global NAME (`stable_vtable_global_name`, slice 3) — one global for two
//     vtables, i.e. an asserted `Load`-equality of two DIFFERENT vtables;
//   * the trait-object TYPE IDENTITY (`stable_trait_object_id` ->
//     `FatPtrKind::TraitObject { trait_id }`), which `differential.rs`'s `tys_agree`
//     compares with `Ok(x == y)` — so it answered TRUE for two genuinely different types.
//     That is a path to a FALSE AGREED, and it is the worse of the two: a wrong global
//     name is a wrong load; a wrong type identity corrupts the comparison itself.
//
// The fix renders the principal FAITHFULLY rather than refusing it, because the two
// designs fail in opposite directions: erasure fails OPEN and invisibly, while a
// rendering drift between the two sides fails VISIBLY (one type -> two ids -> the bodies
// simply do not agree), costing measurement and never soundness. The key covers the WHOLE
// existential predicate list — principal path + non-lifetime args + associated-type
// bindings + auto traits — minted by ONE renderer that both `tcx`-holding sides call
// (`trust_mir_extract::faithful_principal_key`); the MIR-side bridge holds no `tcx` and
// only HASHES the string it was handed, so producer/oracle drift is impossible by
// construction rather than prevented by discipline.
//
// Fail-closed survives as the BACKSTOP, not the policy: a component that cannot be
// spelled injectively refuses, because falling back to the erased spelling IS the bug.
//
// EVERY function below must keep COMPILING — a lowering decline is a coverage decision,
// never an error.

use std::fmt::Debug;

// ------------------------------------------------- the fail-open, now closed

trait Convert<U> {
    fn convert(&self) -> u32;
}

struct Src;
impl Convert<u32> for Src {
    fn convert(&self) -> u32 {
        1
    }
}
impl Convert<u64> for Src {
    fn convert(&self) -> u32 {
        2
    }
}

// THE REGRESSION PIN. One source type, one trait PATH, two different trait ARGUMENTS —
// two genuinely different vtables and two different types. Before this slice both spelled
// ONE `trait_id` and ONE vtable global name. They must now be distinct, and the body must
// still compile.
fn two_generic_principals(s: &Src) -> u32 {
    let a: &dyn Convert<u32> = s;
    let b: &dyn Convert<u64> = s;
    a.convert() + b.convert()
}

// The same hazard over a PRIMITIVE source, whose source key IS mintable — so the
// separation is demonstrably coming from the principal half, not the source half.
impl Convert<u32> for i32 {
    fn convert(&self) -> u32 {
        3
    }
}
impl Convert<u64> for i32 {
    fn convert(&self) -> u32 {
        4
    }
}
fn two_generic_principals_prim(x: &i32) -> u32 {
    let a: &dyn Convert<u32> = x;
    let b: &dyn Convert<u64> = x;
    a.convert() + b.convert()
}

// ZERO-CHURN CONTROL: an args-free principal must key BYTE-IDENTICALLY to the pre-slice
// spelling (`__trust_vtable__core::fmt::Debug$i32__`). The renderer returns the argless
// def path VERBATIM rather than reconstructing it, so this cannot drift.
fn args_free_principal_still_mints(x: &i32) -> u32 {
    let d: &dyn Debug = x;
    let _ = d;
    5
}

// ------------------------------------------------- lifetimes must STAY ignored

trait Lt<'a> {
    fn get(&self) -> u32;
}
struct Held;
impl<'a> Lt<'a> for Held {
    fn get(&self) -> u32 {
        6
    }
}

// A LIFETIME-only argument is not an erasure hazard: regions are erased everywhere else
// in this pipeline and cannot make two vtables differ. Counting them would both
// manufacture divergences and refuse `&'a V -> &'a dyn T`, a real shape.
fn lifetime_arg_principal<'a>(h: &'a Held) -> &'a dyn Lt<'a> {
    h
}

// ------------------------------------------------- auto traits and bindings separate

trait Plain {
    fn p(&self) -> u32;
}
impl Plain for i32 {
    fn p(&self) -> u32 {
        7
    }
}

// `dyn Plain` and `dyn Plain + Send` are DIFFERENT TYPES. Their vtables coincide (an auto
// trait adds no entries), so merging them was harmless for the vtable NAME — but not for
// the type identity `tys_agree` compares, which is why auto traits are in the key.
fn auto_trait_separation(x: &i32) -> u32 {
    let a: &dyn Plain = x;
    let b: &(dyn Plain + Send) = x;
    a.p() + b.p()
}

trait Assoc {
    type Out;
    fn o(&self) -> u32;
}
struct A32;
impl Assoc for A32 {
    type Out = u32;
    fn o(&self) -> u32 {
        8
    }
}

// An associated-type BINDING is part of the type: `dyn Assoc<Out = u32>` and
// `dyn Assoc<Out = u64>` share a principal path and are different types. Concrete
// (scalar) binding terms render, so this keys rather than refuses.
fn assoc_binding_in_key(a: &A32) -> u32 {
    let d: &dyn Assoc<Out = u32> = a;
    d.o()
}

// ------------------------------------------------- param args are BODY-SCOPED

trait Speak {
    fn speak(&self) -> u32;
}

// A bare `ty::Param` ARGUMENT (`dyn A<T>`) is renderable — `T` is one fixed type within a
// body — but it is NOT body-independent, so the key names the owning body
// (`param(T/#0)@<owner>`). Unscoped, `f<T>`'s `dyn A<T>` and `g<U>`'s `dyn A<U>` would
// render one key: the same merge, re-opened. Refusing it outright (the first cut) cost 12
// clean rows and one Agreed for no soundness gain, because the closed grammar's refusal of
// non-scalars is about NOMINAL erasure and does not transfer to a param.
fn param_arg_principal<T: Convert<u32>>(t: &T) -> u32 {
    let d: &dyn Convert<u32> = t;
    d.convert()
}

// A SECOND body with its own `T/#0`. `@<owner>` is what keeps these two distinct.
fn param_arg_other_body<T: Convert<u32>>(t: &T) -> u32 {
    let d: &dyn Convert<u32> = t;
    d.convert()
}

// ------------------------------------------------- Part B: parametric SOURCE

// The other half of the same key. A bare-param SOURCE pointee, the exact shape of the
// seven corpus movers (`by_value_self::make_*`, `borrowck_trait_lifetime::main::f`):
// previously outside the source renderer's closed grammar -> per-site symbolic carrier ->
// body SYMBOLIC. Now keyed `&param(T/#0)@<owner>` on BOTH sides, so the body is MODELLED.
// It does NOT become Agreed here: the param is the `PtrFromParts` DATA operand, so the
// pair holds at the two-sided `param_never_read` gate.
fn param_source<T: Speak>(t: &T) -> &dyn Speak {
    t
}

fn param_source_explicit<T: Speak>(t: &T) -> &dyn Speak {
    t as &dyn Speak
}

// The lifetime-bearing twin — `borrowck_trait_lifetime::main::f` in shape. The lifetime
// admission above is what keeps this on the keyed lane.
fn param_source_lt<'a, V: Speak>(v: &'a V) -> &'a dyn Speak {
    v as &'a dyn Speak
}

// TWO coercions of the SAME param in ONE body share ONE global — the read-read equality
// the body-scoped key asserts, true of every real execution.
fn param_two_coercions<T: Speak>(t: &T) -> u32 {
    let a: &dyn Speak = t;
    let b: &dyn Speak = t;
    a.speak() + b.speak()
}

// ------------------------------------------------- the fail-closed BACKSTOP

// Trust (vtable slice 18): a UNIT struct, not `Wrapper(u32)`. The field was never read,
// so this `check-pass` test emitted a `dead_code` warning with no `.stderr` file beside
// it — i.e. it was RED in compiletest from the day it landed. The type is only ever used
// as a trait ARGUMENT here, so the payload bought nothing.
struct Wrapper;
trait Take<U> {
    fn t(&self) -> u32;
}
impl Take<Wrapper> for i32 {
    fn t(&self) -> u32 {
        9
    }
}

// A NOMINAL argument REFUSED in slice 17: `Ty::Adt`'s name is generics-erased, so
// `dyn Take<Vec<i32>>` and `dyn Take<Vec<u64>>` would have rendered one string — the very
// merge that slice closed. The refusal cost coverage and was the correct answer.
//
// SUPERSEDED BY SLICE 18, which built the tcx-level injective renderer this comment
// called for: a nominal argument now KEYS (def path + recursively rendered args, regions
// erased). The function is kept as a live control — it must still COMPILE, and the
// separation it exercises is now pinned properly in
// `trust_ir_vtable_nominal_principal_key.rs`.
fn nominal_arg_refuses(x: &i32) -> u32 {
    let d: &dyn Take<Wrapper> = x;
    d.t()
}

struct Dog;
impl Speak for Dog {
    fn speak(&self) -> u32 {
        10
    }
}

// NOMINAL SOURCE still refused (unchanged by this slice; the source half's own
// generics-erasure problem, which is format work).
fn nominal_source(d: &Dog) -> &dyn Speak {
    d
}

// Principal-less `dyn Send` still fails closed on both sides — no def path to key on.
fn principal_less(x: &u32) -> &dyn Send {
    x
}

fn main() {
    let s = Src;
    assert_eq!(two_generic_principals(&s), 3);
    assert_eq!(two_generic_principals_prim(&1i32), 7);
    assert_eq!(args_free_principal_still_mints(&2i32), 5);

    let h = Held;
    assert_eq!(lifetime_arg_principal(&h).get(), 6);

    assert_eq!(auto_trait_separation(&1i32), 14);
    assert_eq!(assoc_binding_in_key(&A32), 8);

    assert_eq!(param_arg_principal(&1i32), 3);
    assert_eq!(param_arg_other_body(&1i32), 3);

    let d = Dog;
    assert_eq!(param_source(&d).speak(), 10);
    assert_eq!(param_source_explicit(&d).speak(), 10);
    assert_eq!(param_source_lt(&d).speak(), 10);
    assert_eq!(param_two_coercions(&d), 20);

    assert_eq!(nominal_arg_refuses(&1i32), 9);
    assert_eq!(nominal_source(&d).speak(), 10);
    let n = 5u32;
    let _ = principal_less(&n);
}
