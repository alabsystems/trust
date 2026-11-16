//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//~? RAW Trust
//! An UNRESOLVABLE generic dispatch must never be emitted as a call to a bundled
//! proved body. It was, whenever a type PARAMETER was named after a primitive.
//!
//! `go` below takes `x: &u8` where `u8` is the type PARAMETER (it shadows the
//! primitive inside `go`), and `v: &Prim` where `Prim` is the primitive. The two
//! `m()` calls are completely different things:
//!
//! * `v.m()` resolves to `impl Tr for u8`, whose body is bundled and proved;
//! * `x.m()` is `ImplSource::Param` — it does not resolve at all, and at
//!   monomorphization an impl may supply a body that PANICS.
//!   `collect_expected_absent_callees` classifies it correctly on the `Ok(None)`
//!   arm: NOT expected-absent, so it must stay on the fail-closed absent-callee
//!   arm.
//!
//! Both nevertheless rendered ONE callee key, because a `ty::Param` prints as its
//! bare NAME and the primitives are the only concrete types the identity seam
//! also prints as a bare name (every ADT is crate-qualified under
//! `resolve_crate_name`/`no_visible`/`no_trimmed` — measured with a parameter
//! named after a local struct, which does NOT collide):
//!
//! ```text
//! <u8 as generic_param_named_after_primitive_key_alias_stays_closed::Tr>::m
//! ```
//!
//! `trust_ir_bridge`'s `resolve_call_target` binds a call to a bundled body by
//! that STRING (`known_functions.get(callee)`), so the generic dispatch was
//! emitted as a real `Inst::Call` to the proved concrete body.
//!
//! MEASURED, both states, on two real compilers built from this tree. The
//! observable that grades it is inside the native bundle for `go`, and the exit
//! code moves with it:
//!
//! ```text
//! aliased key (pristine): EXIT=0, and the report is SILENT.
//!   go blk1: Call { callee: 1 }        <- the `impl Tr for u8` body
//!   proof_obligations: [default trust-mc function admission]
//!
//! marked parameter (with_def_path_disambiguators + ty::ParamTy):  EXIT=1
//!   go blk1: Assert { cond: 6 }
//!   proof_obligations: [default, PanicFreedom
//!     "[trust-absent-callee-assumption] call to absent callee
//!      `<u8#ty_param as …::Tr>::m`"]
//! ```
//!
//! That is byte-for-byte the shape the CONTROL already had — the same file with
//! the parameter spelled `T` — which is the point: one identifier decided whether
//! `go` was reported panic-free for EVERY `T: Tr`.
//!
//! `#` is not identifier-spellable, so no source type can impersonate the marked
//! form, and `hir::PrimTy::from_name` (rustc's own "this identifier names a
//! primitive type" predicate — the same rule that lets the parameter shadow it)
//! makes the marked set exactly the colliding set.
//!
//! SCOPE — read this before assuming more than it says. This file pins ONE
//! collision class. The callee key is NARROWED, not injective. In particular a
//! GENERIC call's key is still spelled exactly like a generic DEFINITION's path
//! (`fn f<T: Tr>(x: &T) { x.m() }` renders what `impl<T: Marker> Tr for T`'s `m`
//! renders), which is a MEASURED, STILL-OPEN false proof of the same shape;
//! `ty::ParamTy` carries no owner, so no spelling can separate those two. The
//! residual list on `trust_mir_extract::direct_call_def_path` enumerates it with
//! its reproducer and says what identity would be needed instead.
#![no_std]
#![allow(dead_code, non_camel_case_types)]

pub trait Tr {
    fn m(&self) -> u32;
}

impl Tr for u8 {
    fn m(&self) -> u32 {
        1
    }
}

/// The PRIMITIVE `u8`, named where the parameter does not shadow it.
type Prim = u8;

// OD-1 phase 1 (2026-10-04): `x.m()` in `go` is now an ADMITTED instance-hypothesis
// site (`<u8 as Tr>::m` on `go`'s own parameter, open, unresolved). The compiler
// admits it by its exact MIR block and the bridge lowers that block before any
// by-name call binding, so it can no longer be bound to `impl Tr for u8` either; `go`
// publishes one `assumption:instance-hypothesis` row and passes strict
// CONDITIONALLY (the warning below), never as proved. The by-name collision this file
// guards against is still exercised on a NON-admitted site: `go_raw` hands the
// dispatch a raw pointer (design §2.3), so its call stays on the fatal absent-callee
// arm, and the strict build must still refuse it.
pub fn go<u8: Tr>(x: &u8, v: &Prim) -> u32 {
    //~^ WARN 1 instance hypothesis row(s)
    let a = v.m();
    let c = x.m();
    a.wrapping_add(c)
}

pub trait Tr2 {
    fn m2(&self, p: *const Prim) -> u32;
}

impl Tr2 for Prim {
    fn m2(&self, _p: *const Prim) -> u32 {
        1
    }
}

pub fn go_raw<u8: Tr2>(x: &u8, v: &Prim, p: *const Prim) -> u32 {
    //~^ ERROR Trust strict verification failed
    let a = v.m2(p);
    let c = x.m2(p);
    a.wrapping_add(c)
}
