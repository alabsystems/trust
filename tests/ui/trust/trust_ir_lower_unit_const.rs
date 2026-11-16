//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=on -Ztrust-policy=advisory -Aprivate_interfaces
//@ needs-trust-verify
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//! Trust (wave-UC): a `()`-TYPED named/inline CONSTANT is VALUE-LESS.
//!
//! Every body below carried a const-family tag before the wave —
//! `NamedConst(non-scalar)`, `ConstBlock(non-scalar)`, or (once the args carry a
//! live generic param) `NamedConst(eval failed)` from the composite leg's own
//! first gate. `strict` turns each of those into a compile error, so this file
//! IS the mutation check: measured 2026-08-31 against the pre-wave
//! `build/snap-lv2-subject`, this file raises exactly TWELVE
//! `-Ztrust-ir-lower=strict` errors over 18 tags (`main` is a pinned body too —
//! its `<B<A> as Tr>::DATA` read is the twelfth). Delete `lower_named_const`'s
//! `ty::Tuple([])` arm and all twelve come back; delete only the
//! `NamedConst`/`ConstBlock` widening in `try_lower_unit_arg`'s G2 and
//! `unit_const_as_arg` alone comes back, as
//! `Call(unsupported arg) [masking: <none recorded>]`.
//!
//! WHY EVERY BODY HERE IS ITS OWN CONTROL. `()` has one inhabitant and a
//! named/inline const is evaluated by CTFE, never at the read site, so each of
//! these is semantically the LITERAL `()` spelling of the same program. The
//! MIR side agrees by construction rather than by coincidence: `trust-mir-extract`
//! renders a unit-typed const operand as `ConstValue::Unit` off the ground-truth
//! rustc type, in two independent `ty.is_unit()` arms (`convert.rs`'s
//! const-operand fallback and `convert_ty_const_to_operand`), for the evaluated
//! `const ()` spelling and the `Const::Unevaluated` `const S::<T>::C` spelling
//! alike. Measured 2026-08-31 on `build/snap-lv2-subject`: the literal-`()`
//! twin of this entire file is clean and strict-green, and each target's built
//! MIR is line-identical to its twin's modulo the constant's printed name.
//! Where built assigns the const to `_0` (`s5`, `impl<T: Tr> Tr for B<T>`) and
//! the producer emits nothing, `mir_differential`'s L15 `unit-return-collapse`
//! renders both sides `return c:unit`.
//!
//! The REFUSALS live in `trust_ir_lower_unit_const_refuses.rs`: under `strict`
//! a refusal is a compile error and cannot share a file with the admissions.
//!
//! EFFECT CONSERVATION (D28, 2026-10-01): `f` and `g` drop their by-value `T`. The direct trust-ir
//! emits no `Drop` yet, so the effect-conservation gate tags each such body `Abstracted(drop, ..)`
//! and strict refuses it (expected below). A producer tag would still be its own, unannotated,
//! strict error, so this file keeps its mutation check.

#![allow(dead_code, unused_variables, unused_mut)]

struct Data;
struct Data2;
fn f<T>(_: T, _: ()) {}
//~^ ERROR the effect-conservation check refused it against the built MIR
fn g<T>(_: T, _: ()) {}
//~^ ERROR the effect-conservation check refused it against the built MIR
mod m {
    pub const FOO: () = ();
}
const BAR: () = ();

// --- the corpus shapes, one per refusal site the artifact named ------------

// `tests/ui/macros/metavar-expressions/concat-allowed-operations.rs:104` —
// a `()`-typed const item read in `let _ = …` position.
pub fn unit_const_in_let() {
    let _ = m::FOO;
}

// `tests/ui/consts/const-eval/heap/alloc_intrinsic_zero_sized.rs:10`,
// `tests/ui/reborrow/coerce_shared_consteval.rs:27`,
// `tests/ui/inline-const/interpolated.rs:10` — a tail-less inline const block
// in STATEMENT position, with live statements either side of it so the body is
// not vacuously empty.
const fn side_effect_free() {}
pub fn unit_const_block_stmt() {
    let mut n = 0i32;
    const {
        side_effect_free();
    };
    n += 1;
}

// `tests/ui/inline-const/interpolated.rs:22` — `let _ = const { };`.
pub fn unit_const_block_in_let() {
    let _ = const {};
}

// `tests/ui/resolve/blind-item-mixed-use-item.rs:17-18` — the ARGUMENT
// position, which needs `try_lower_unit_arg`'s G2 as well as the const arm:
// with the const silent but G2 unwidened the body keeps
// `Call(unsupported arg) [masking: <none recorded>]`. Both an item-level and a
// body-local const, because the local one would otherwise reach
// `lower_named_const`'s deferral rather than its type gate.
pub fn unit_const_as_arg() {
    const BAR2: () = ();
    f(Data, BAR);
    g(Data2, BAR2);
}

// `tests/ui/consts/control-flow/dead_branches_dont_eval.rs:31` — an associated
// `()` const under a LIVE generic param, in tail position. `S::<T>::C` has no
// value before monomorphization, which is why it used to take the composite
// leg's `has_non_region_param` gate and report `NamedConst(eval failed)`; unit
// needs no monomorphization to be known.
struct S<T>(T);
impl<T> S<T> {
    const C: () = ();
}

// `tests/ui/consts/control-flow/dead_branches_dont_eval.rs:18` — the same read
// inside a CLOSURE body. rustc compiles the read away entirely here, so built
// MIR is `bb0: return` on both spellings.
struct Foo<T, const N: usize>(T);
impl<T, const N: usize> Foo<T, N> {
    const BR: () = ();
}

// `tests/ui/associated-types/issue-64848.rs:12` — a `()` const whose VALUE is
// another `()` const. The body being lowered is the const initializer itself.
trait Tr {
    const DATA: ();
}
struct A;
impl Tr for A {
    const DATA: () = ();
}

// --- blast radius: the sites that consume a SILENT `None` -------------------
//
// Making the const arm silent hands it to every lane that keys on "lowering
// pushed no tag AND the operand is ground-truth unit". These four are the
// complete list (the mark-vs-`lower_expr` sites; every other `unsupported.len()`
// watermark in the producer brackets `map_ty`, which `lower_named_const` never
// reaches). All four masked the const tag with a second tag of their own before
// the wave, so each of these bodies carried TWO errors, not one.

// wave-UF, tuple element: `Tuple(unsupported field)` masked the const.
pub fn unit_const_tuple_element() -> (i32, ()) {
    (1, BAR)
}

// wave-UF, struct field: `Adt(unsupported field)` masked the const.
struct U {
    a: i32,
    u: (),
}
pub fn unit_const_struct_field() -> U {
    U { a: 1, u: BAR }
}

// the enum-ctor unit payload slot: `EnumCtor(unit payload unsupported)`.
enum E {
    V(()),
    W,
}
pub fn unit_const_enum_payload() -> E {
    E::V(BAR)
}

// wave-AR2/UB2, the rvalue snapshot of a `&()`: `Borrow(non-local place)`.
// The lane is already gated on the GROUND-TRUTH `is_unit()` of the operand, so
// it admits the const spelling for the same reason it admits the literal.
pub fn unit_const_shared_borrow() {
    let r = &BAR;
}

fn main() {
    unit_const_in_let();
    unit_const_block_stmt();
    unit_const_block_in_let();
    unit_const_as_arg();
    let _ = unit_const_tuple_element();
    let _ = unit_const_struct_field();
    let _ = unit_const_enum_payload();
    unit_const_shared_borrow();
}
