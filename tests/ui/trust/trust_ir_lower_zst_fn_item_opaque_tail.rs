//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=on -Ztrust-policy=advisory
//@ needs-trust-verify
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@ edition: 2021
//! Trust (wave-ZFT): a FUNCTION ITEM at the DIRECT TAIL of a body whose declared
//! return SIGNED as the shared opaque-alias sort — `fn foo() -> impl Copy { foo }`.
//! rustc spells the tail `ExprKind::ZstLiteral` of `ty::FnDef` type, whose hidden
//! type IS the opaque, so the value's only consumer is the implicit `Return`.
//! `map_ty` spells a fn item `Ty::Unit` (the oracle's sig-blind spelling), so
//! minting there would emit `ReturnTypeMismatch { expected: "struct.N",
//! actual: "()" }`; the arm mints at the RETURN's sort instead — exactly the
//! wave-CVR closure-tail argument, one spelling over.
//!
//! Under `strict` WITH verification on, so a regression is a compile error rather
//! than a sidecar row: `-Ztrust-verify=off` is the master off-switch and makes
//! `strict` degrade to `on`, so the source commit's `-Ztrust-verify=off` spelling
//! would pass with or without this lane on today's compiler. `advisory` keeps the
//! verifier's own findings from failing the build; only the producer is judged.
//! (Measured: the MIR-derived verifier reports one `unknown` row for `rpit_self`,
//! "type lowering exceeded depth limit 64" on the self-referential return type —
//! a verifier limitation this file does not pin, hence the WARN waiver.)
//! The bodies stay SYMBOLIC (`param_opaque`) and neither disagreement channel can
//! reach them: the interpretation differential answers `NotRun` on
//! `mir.has_opaque_types()` (`clean-skip-unrevealed-opaque`), and the derived-MIR
//! channel refuses a `Const` at `Ty::Struct` outright (`to_mir`'s
//! "Const(struct value)"), so `record_green` is never called and the body cannot
//! flip into codegen.
//!
//! CALLERS ARE DELIBERATELY ABSENT. A call whose callee signature mentions an
//! unrevealed opaque is its own fail-closed decline (`Call(opaque type in callee
//! sig)`) and would make this strict file red for a reason that has nothing to do
//! with this lane — measured on `issue-86201`'s `main`.
//!
//! Ported 2026-09-29 from 11add035e5e (salvage/stale-wave-zft-20260928). On main
//! 8e8e84edfa3 this file failed with exactly four errors, one per positive body
//! (`rpit_self`, `rpit_named`, `rpit_generic`, `tait_tail`), each
//! "could not fully lower this body (1 unsupported shape(s)): ZstLiteral"; the
//! two negative controls lowered.

#![feature(type_alias_impl_trait)]
#![allow(dead_code)]

// RPIT, SELF-referential — the `issue-36792` /
// `impl-copy-function-debuginfo-58463` shape, and the reason this lane cannot be
// answered by revealing the hidden type instead.
fn rpit_self() -> impl Copy {
    rpit_self
}

fn plain(x: u32) -> u32 {
    x
}

// RPIT over an ordinary named fn item.
fn rpit_named() -> impl Fn(u32) -> u32 {
    plain
}

fn generic_id<T>(t: T) -> T {
    t
}

// GENERIC parent: the return still signs as the shared sort, now through
// `map_ty`'s pre-monomorphization arm rather than its zero-arg opaque arm —
// the `rigid-hr-projection-issue-93340` shape.
fn rpit_generic<T>() -> impl Fn(T) -> T {
    generic_id::<T>
}

fn named_zero() -> u32 {
    0
}

// TAIT via its defining function — the `issue-86201` shape.
type Tait = impl Fn() -> u32;

#[define_opaque(Tait)]
fn tait_tail() -> Tait {
    named_zero
}

// NEGATIVE CONTROL. The fn item is bound to a `let` and then CALLED, so it is
// not a tail and the re-sort must not reach it; wave-FI2 already skips the
// binding and the call resolves by the local's TYPE, so this body lowers clean
// WITHOUT this lane. If a future widening moved the re-sort off the tail, this
// body would start carrying an opaque-sorted value with a `u32` return and the
// module would fail validation.
fn not_a_tail() -> u32 {
    let f = named_zero;
    f()
}

// NEGATIVE CONTROL. A CONCRETE (non-opaque) return whose tail is a fn item is
// impossible to write directly, so the nearest reachable one is a fn POINTER
// tail: that is an `ExprKind::PointerCoercion(ReifyFnPointer)` wrapper, taken by
// the reify arm, which mints a real `Constant::FnDef` at `Ty::Func` — never this
// lane's opaque seed.
fn reified() -> fn(u32) -> u32 {
    plain
}

fn main() {}
