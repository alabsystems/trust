//@ revisions: p01_req_map_collect p03_req_option_map p05_req_any p09_req_ref_item_map
//@ revisions: p32_req_trait_impl_item p41_dep_ref_item_map p43_dep_ref_item_option_map
//@ revisions: p34_req_and_then p06_req_filter_map p10_req_flat_map p45_dep_mutref_item_map
//@ revisions: ok_reqfree_item_map ok_guarding_item_map
//@ needs-trust-verify
//@ edition: 2021
//@ aux-build:iter_hof_verify_off_dep.rs
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[p01_req_map_collect] check-fail
//@[p03_req_option_map] check-fail
//@[p05_req_any] check-fail
//@[p09_req_ref_item_map] check-fail
//@[p32_req_trait_impl_item] check-fail
//@[p41_dep_ref_item_map] check-fail
//@[p43_dep_ref_item_option_map] check-fail
//@[p34_req_and_then] check-fail
//@[p06_req_filter_map] check-fail
//@[p10_req_flat_map] check-fail
//@[p45_dep_mutref_item_map] check-fail
//@[ok_reqfree_item_map] check-pass
//@[ok_guarding_item_map] check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! W4 ITER-HOF fix round 1: the round-0 adversarial review's false accepts
//! (verdict DO-NOT-LAND), each pinned verbatim.
//!
//! W4 (b) routes a HOF whose `F` is a LOCAL fn item like one whose `F` is a
//! closure (the closure-consumer arm, a tolerated runtime-checked row) and
//! bundles the item's body. The tolerance rested on "the driven callable is
//! verified as its own root", which is false for an item carrying a `requires`
//! (its body is verified UNDER the clause, and std's call never establishes it)
//! and for a verify-off dependency's item handed by reference.
//!
//! BEFORE: on the pre-fix W4 snapshot (`<home>/trust-land/snap-w4-iterhof`,
//! `0.10.0+g3b30328c0`) every check-fail revision below built exit 0 and a
//! verify-off driver panicked — divide by zero, or the dependency's assert on 7
//! (the prober's `runtime_exit`/`truth_exit` 101 for each). `p03_req_option_map`
//! and `p34_req_and_then` even carried a PROVED caller row (the bundled item's
//! body ran with its `requires` assumed). `p43_dep_ref_item_option_map` printed
//! NO diagnostic at all. `p05_req_any` was already accepted before W4 (main's
//! requires gate, 0cee618c6e, closed it); it is pinned here because W4 routes
//! the same item shape.
//!
//! AFTER: main's requires gate (`local_fn_item_is_verified_unconditionally`,
//! `peel_fn_forwarding_layers`; `trait_impl_requires` for `p32`) refuses each
//! caller, and `hof_local_fn_item_def_id` no longer bundles a requires-carrying
//! item, so no PROVED row stands beside the refusal. The controls are the shapes
//! W4 exists for: a requires-FREE item, and one that GUARDS its call of a
//! requires-carrying item.
//!
//! MEASURED (direct `trustc -Ztrust-verify=on --crate-type lib --cfg <rev>`, the aux
//! built verify-off): the pre-fix W4 snapshot exits 0 on all eleven check-fail
//! revisions and on both controls; stage 1 of origin/main `07091c92c1` (no W4
//! ITER-HOF) refuses all thirteen, controls included — the controls are the W4
//! over-refusal this branch exists to remove.
//!
//! Companions: `iter_hof_local_fn_item.rs`, `callable_handed_to_std_through_a_reference.rs`,
//! `requires_callee_handed_to_generic_code.rs`, `trait_impl_requires_charged_to_no_caller.rs`.

#[cfg(any(p41_dep_ref_item_map, p43_dep_ref_item_option_map, p45_dep_mutref_item_map))]
extern crate iter_hof_verify_off_dep as dep;

#[cfg(any(p01_req_map_collect, p09_req_ref_item_map))]
fn inv(x: &u32) -> u32 requires *x != 0 {
    100 / *x
}

#[cfg(p01_req_map_collect)]
pub fn f(v: &[u32]) -> Vec<u32> {
    v.iter().map(inv).collect()
}

#[cfg(p09_req_ref_item_map)]
pub fn f(v: &[u32]) -> Vec<u32> {
    v.iter().map(&inv).collect()
}

#[cfg(p03_req_option_map)]
fn inv(x: u32) -> u32 requires x != 0 {
    100 / x
}

#[cfg(p03_req_option_map)]
pub fn f(x: Option<u32>) -> Option<u32> {
    x.map(inv)
}

#[cfg(p34_req_and_then)]
fn inv(x: u32) -> Option<u32> requires x != 0 {
    Some(100 / x)
}

#[cfg(p34_req_and_then)]
pub fn f(x: Option<u32>) -> Option<u32> {
    x.and_then(inv)
}

#[cfg(p05_req_any)]
fn is_big(x: &u32) -> bool requires *x != 0 {
    100 / *x < 5
}

#[cfg(p05_req_any)]
pub fn f(v: &[u32]) -> bool {
    v.iter().any(is_big)
}

#[cfg(p06_req_filter_map)]
fn half_of_inv(x: &u32) -> Option<u32> requires *x != 0 {
    let q = 100 / *x;
    if q % 2 == 0 { Some(q) } else { None }
}

#[cfg(p06_req_filter_map)]
pub fn f(v: &[u32]) -> Vec<u32> {
    v.iter().filter_map(half_of_inv).collect()
}

#[cfg(p10_req_flat_map)]
fn lower_at(b: &u8) -> std::char::ToLowercase requires *b < 4 {
    let t: [u8; 4] = [65, 66, 67, 68];
    char::from(t[*b as usize]).to_lowercase()
}

#[cfg(p10_req_flat_map)]
pub fn f(v: &[u8]) -> String {
    v.iter().flat_map(lower_at).collect()
}

#[cfg(p32_req_trait_impl_item)]
pub struct S;
#[cfg(p32_req_trait_impl_item)]
pub trait Tr {
    fn m(x: &u32) -> u32;
}
#[cfg(p32_req_trait_impl_item)]
impl Tr for S {
    fn m(x: &u32) -> u32 requires *x != 0 {
        100 / *x
    }
}

#[cfg(p32_req_trait_impl_item)]
pub fn f(v: &[u32]) -> Vec<u32> {
    v.iter().map(<S as Tr>::m).collect()
}

#[cfg(p41_dep_ref_item_map)]
pub fn f(v: &[u32]) -> Vec<u32> {
    v.iter().map(&dep::boom).collect()
}

#[cfg(p43_dep_ref_item_option_map)]
pub fn f(x: Option<u32>) -> Option<u32> {
    x.map(&dep::boom_v)
}

#[cfg(p45_dep_mutref_item_map)]
pub fn f(v: &[u32]) -> Vec<u32> {
    let mut g = dep::boom;
    v.iter().map(&mut g).collect()
}

#[cfg(ok_reqfree_item_map)]
fn ident(word: &str) -> String {
    word.to_string()
}

#[cfg(ok_reqfree_item_map)]
pub fn f(s: &str) -> Vec<String> {
    s.split(' ').map(ident).collect()
}

#[cfg(ok_guarding_item_map)]
fn inv(x: u32) -> u32 requires x != 0 {
    100 / x
}

#[cfg(ok_guarding_item_map)]
fn safe_inv(x: &u32) -> u32 {
    if *x != 0 { inv(*x) } else { 0 }
}

#[cfg(ok_guarding_item_map)]
pub fn f(v: &[u32]) -> Vec<u32> {
    v.iter().map(safe_inv).collect()
}
