//@ revisions: extern_decl_ptr extern_decl_ptr_certify extern_decl_map
//@ revisions: dyn_trait_item_ptr_certify dyn_trait_item_map
//@ revisions: generic_trait_item_ptr_certify generic_trait_item_map
//@ revisions: concrete_trait_item_ptr_certify concrete_trait_item_any_certify local_ctor_map
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[extern_decl_ptr_certify] compile-flags: -Ztrust-policy=certify
//@[dyn_trait_item_ptr_certify] compile-flags: -Ztrust-policy=certify
//@[generic_trait_item_ptr_certify] compile-flags: -Ztrust-policy=certify
//@[concrete_trait_item_ptr_certify] compile-flags: -Ztrust-policy=certify
//@[concrete_trait_item_any_certify] compile-flags: -Ztrust-policy=certify
//@[extern_decl_ptr] check-fail
//@[extern_decl_ptr_certify] check-fail
//@[extern_decl_map] check-fail
//@[dyn_trait_item_ptr_certify] check-fail
//@[dyn_trait_item_map] check-fail
//@[generic_trait_item_ptr_certify] check-fail
//@[generic_trait_item_map] check-fail
//@[concrete_trait_item_ptr_certify] check-pass
//@[concrete_trait_item_any_certify] check-fail
//@[local_ctor_map] check-pass
//@ dont-check-compiler-stderr
//@[extern_decl_ptr] dont-require-annotations: ERROR
//@[extern_decl_ptr_certify] dont-require-annotations: ERROR
//@[extern_decl_map] dont-require-annotations: ERROR
//@[dyn_trait_item_ptr_certify] dont-require-annotations: ERROR
//@[dyn_trait_item_map] dont-require-annotations: ERROR
//@[generic_trait_item_ptr_certify] dont-require-annotations: ERROR
//@[generic_trait_item_map] dont-require-annotations: ERROR
//@[concrete_trait_item_ptr_certify] dont-require-annotations: ERROR
//@[local_ctor_map] dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! A LOCAL function item is "verified as its own root" only when it NAMES A
//! BODY this crate verifies. Two local items do not, and each was accepted by
//! the reified-pointer carve-out and the callable type-argument test.
//!
//! * A `safe fn` declared in a local `unsafe extern "Rust"` block: its body is
//!   another crate's `#[no_mangle]` function — in the measurement, a dependency
//!   built `-Ztrust-verify=off` whose `trust_probe_boom(x)` is `100 / x`.
//! * A local TRAIT item whose `Self` is not concrete: `<dyn Tr as Tr>::m0`
//!   (resolves to a virtual call) or `T::m0` in a generic body. Its body is
//!   whatever impl the caller supplies — in the measurement, `impl Tr for Bomb
//!   { fn m0(&self) -> u32 { 100 / self.0 } }` in a verify-off `main`.
//!
//! BEFORE (adversarial review, 2026-09-29; stage 1 of the requires-gate change
//! `141b0488896` and of origin/main `fb9f57688a6` alike, and again on origin/main
//! `cb8406c0bf0` for this test; m3's std): `*_ptr` built exit 0 on strict, the
//! default policy and certify, `extern_decl_map` and `dyn_trait_item_map` on
//! strict and the default policy (certify refused them), and each program then
//! divided by zero (exit 101). The DIRECT calls (`trust_probe_boom(y)`,
//! `d.m0()`) were already refused on all three. `generic_trait_item_map`
//! (`map(T::m0)` in a generic body) was ALREADY refused on all three lanes on
//! `cb8406c0bf0` by another row; it is kept as a pin, since this gate now
//! refuses it too.
//!
//! AFTER: `local_fn_item_resolved_body` must reach a concrete LOCAL body with
//! MIR — never a foreign-item declaration, a virtual call, or a trait item this
//! body's generics leave open — or the call falls to the indirect-call gate.
//! Controls: a trait item whose impl is concrete and local, reified or handed
//! to `any`, passes certify; a local constructor handed to `map` passes the
//! default policy (certify refuses core's `Map`, unchanged).
//! Companion: `callable_handed_to_std_through_a_reference.rs`.
//!
//! Amended 2026-10-04 (OD-1 item 14, docs/DECISION_QUEUE.md "OD-1"): a pointer reified
//! from `T::m0` and called in the same body (`generic_trait_item_ptr_certify`) is now an
//! ADMITTED open generic dispatch site, the same as the direct call `d.m0()`: it
//! publishes an `assumption:instance-hypothesis` row and each instance this crate names
//! is charged by a discharge row. Certify still refuses it, now on that hypothesis
//! row ("certify verification failed ... instance hypothesis row(s)"); a downstream
//! `Bomb` instance is charged nowhere until phase 2, exactly as for `d.m0()`
//! (KNOWN_HAZARDS 2026-10-04). Handing `T::m0` to `map` is not a call in this body
//! and is still refused by the indirect-call gate (`generic_trait_item_map`).

#[cfg(any(extern_decl_ptr, extern_decl_ptr_certify, extern_decl_map))]
unsafe extern "Rust" {
    safe fn trust_probe_boom(x: u32) -> u32;
}

#[cfg(any(extern_decl_ptr, extern_decl_ptr_certify))]
pub fn p(y: u32) -> u32 {
    //[extern_decl_ptr,extern_decl_ptr_certify]~^ ERROR Trust strict verification failed for `local_item_naming_no_verified_body_as_value::p`
    let fp: fn(u32) -> u32 = trust_probe_boom;
    fp(y)
}

#[cfg(extern_decl_map)]
pub fn p(y: u32) -> u32 {
    //[extern_decl_map]~^ ERROR Trust strict verification failed for `local_item_naming_no_verified_body_as_value::p`
    match [y, 1, 2].iter().copied().map(trust_probe_boom).last() {
        Some(r) => r,
        None => 0,
    }
}

#[cfg(any(
    dyn_trait_item_ptr_certify,
    dyn_trait_item_map,
    generic_trait_item_ptr_certify,
    generic_trait_item_map
))]
pub trait Tr {
    fn m0(&self) -> u32;
}

#[cfg(dyn_trait_item_ptr_certify)]
pub fn p(xs: &[&'static dyn Tr]) -> u32 {
    //[dyn_trait_item_ptr_certify]~^ ERROR Trust strict verification failed for `local_item_naming_no_verified_body_as_value::p`
    let fp: fn(&'static (dyn Tr + 'static)) -> u32 = <dyn Tr as Tr>::m0;
    match xs.last() {
        Some(d) => fp(*d),
        None => 0,
    }
}

#[cfg(dyn_trait_item_map)]
pub fn p(xs: &[&'static dyn Tr]) -> u32 {
    //[dyn_trait_item_map]~^ ERROR Trust strict verification failed for `local_item_naming_no_verified_body_as_value::p`
    match xs.iter().copied().map(<dyn Tr as Tr>::m0).last() {
        Some(r) => r,
        None => 0,
    }
}

#[cfg(generic_trait_item_ptr_certify)]
pub fn p<T: Tr>(xs: &[T]) -> u32 {
    //[generic_trait_item_ptr_certify]~^ ERROR Trust certify verification failed for `local_item_naming_no_verified_body_as_value::p`: 1 instance hypothesis row(s)
    let fp: fn(&T) -> u32 = T::m0;
    match xs.last() {
        Some(d) => fp(d),
        None => 0,
    }
}

#[cfg(generic_trait_item_map)]
pub fn p<T: Tr>(xs: &[T]) -> u32 {
    //[generic_trait_item_map]~^ ERROR Trust strict verification failed for `local_item_naming_no_verified_body_as_value::p`
    match xs.iter().map(T::m0).last() {
        Some(r) => r,
        None => 0,
    }
}

// ---- controls ----

#[cfg(any(concrete_trait_item_ptr_certify, concrete_trait_item_any_certify))]
pub trait Tp {
    fn pos(x: &u32) -> bool;
}
#[cfg(any(concrete_trait_item_ptr_certify, concrete_trait_item_any_certify))]
pub struct S;
#[cfg(any(concrete_trait_item_ptr_certify, concrete_trait_item_any_certify))]
impl Tp for S {
    fn pos(x: &u32) -> bool {
        *x > 1
    }
}

#[cfg(concrete_trait_item_ptr_certify)]
pub fn p(v: &[u32; 3]) -> bool {
    let fp: fn(&u32) -> bool = <S as Tp>::pos;
    fp(&v[0])
}

#[cfg(concrete_trait_item_any_certify)]
// Re-pinned 2026-10-15 (the merge of 2026-10-14, DECISION_QUEUE D103(e)): still refused, but no
// longer zero-row. The call into the bundled body now carries the counted panic-freedom
// aggregate (one unproved `runtime_checked` row), so ZERO-ROW-GATE's note is gone and the
// body is refused on that row instead.
//[concrete_trait_item_any_certify]~vv ERROR Trust strict verification failed for `local_item_naming_no_verified_body_as_value::p`
//[concrete_trait_item_any_certify]~v ERROR Trust Level 0 safety verification incomplete for `local_item_naming_no_verified_body_as_value::p`
pub fn p(v: &[u32; 3]) -> bool {
    v.iter().any(<S as Tp>::pos)
}

#[cfg(local_ctor_map)]
pub struct Wr(pub u32);
#[cfg(local_ctor_map)]
pub fn p(v: &[u32; 3]) -> usize {
    v.iter().copied().map(Wr).count()
}
