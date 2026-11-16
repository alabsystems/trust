//@ revisions: method_call method_call_certify trait_path_certify trait_ptr_certify trait_map
//@ revisions: override_certify
//@ revisions: inherent_certify total_impl_certify
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[method_call_certify] compile-flags: -Ztrust-policy=certify
//@[trait_path_certify] compile-flags: -Ztrust-policy=certify
//@[trait_ptr_certify] compile-flags: -Ztrust-policy=certify
//@[override_certify] compile-flags: -Ztrust-policy=certify
//@[inherent_certify] compile-flags: -Ztrust-policy=certify
//@[total_impl_certify] compile-flags: -Ztrust-policy=certify
//@[method_call] check-fail
//@[method_call_certify] check-fail
//@[trait_path_certify] check-fail
//@[trait_ptr_certify] check-fail
//@[trait_map] check-fail
//@[override_certify] check-fail
//@[inherent_certify] check-pass
//@[total_impl_certify] check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! A `requires` on a TRAIT IMPL method is charged to no caller: every call that
//! reaches the method names the TRAIT's item (`S.m(y)`, `<S as Tr>::m(y)`, a
//! pointer to `<S as Tr>::m`, `map(<S as Tr>::m)`, generic code, `dyn`), and the
//! caller-side lane charges the contract of the item a call names. The impl's
//! body was nevertheless verified UNDER its clause.
//!
//! BEFORE (stage 1 of origin/main `8b8d68d1abe`, m3's std, measured 2026-09-29):
//! `method_call`, `trait_path` and `override` built exit 0 under `certify` with
//! `p` counted VERIFIED (1 of 1, resp. 2 of 2); `trait_ptr` built exit 0 under
//! `certify`; `trait_map` built exit 0 on the default policy. A verify-off `main`
//! calling `p(0)` (`override`: `p(5)`, which passes the trait default's
//! `requires x != 0` and fails the impl's `x > 5`) divided by zero (exit 101).
//! Generic `T::m` and `dyn` calls were already refused, for unrelated reasons.
//!
//! AFTER: the impl method itself is refused on the fail-closed lanes
//! (`trait_impl_requires`). Controls: an INHERENT method's `requires` is charged
//! at its direct call and a guarded call passes `certify` (`inherent`); a total
//! trait impl method with no `requires` passes `certify` (`total_impl`).
//! Companions: `requires_callee_reified_to_fn_pointer.rs`,
//! `requires_callee_handed_to_generic_code.rs`.

#[cfg(any(method_call, method_call_certify))]
pub trait Td {
    fn m(&self, x: u32) -> u32;
}
#[cfg(any(method_call, method_call_certify))]
pub struct S;
#[cfg(any(method_call, method_call_certify))]
impl Td for S {
    fn m(&self, x: u32) -> u32 requires x != 0 {
        //[method_call,method_call_certify]~^ ERROR Trust verification failed for `<trait_impl_requires_charged_to_no_caller::S as trait_impl_requires_charged_to_no_caller::Td>::m`: a `requires` on a trait impl method is charged to no caller
        100 / x
    }
}
#[cfg(any(method_call, method_call_certify))]
pub fn p(y: u32) -> u32 {
    S.m(y)
}

#[cfg(any(trait_path_certify, trait_ptr_certify, trait_map))]
pub trait Tr {
    fn m(x: u32) -> u32;
}
#[cfg(any(trait_path_certify, trait_ptr_certify, trait_map))]
pub struct S;
#[cfg(any(trait_path_certify, trait_ptr_certify, trait_map))]
impl Tr for S {
    fn m(x: u32) -> u32 requires x != 0 {
        //[trait_path_certify,trait_ptr_certify,trait_map]~^ ERROR a `requires` on a trait impl method is charged to no caller
        100 / x
    }
}
#[cfg(trait_path_certify)]
pub fn p(y: u32) -> u32 {
    <S as Tr>::m(y)
}
#[cfg(trait_ptr_certify)]
pub fn p(y: u32) -> u32 {
    let fp: fn(u32) -> u32 = <S as Tr>::m;
    fp(y)
}
#[cfg(trait_map)]
pub fn p(v: &[u32; 3]) -> usize {
    match v.iter().copied().map(<S as Tr>::m).last() {
        Some(_) => 1,
        None => 0,
    }
}

#[cfg(override_certify)]
pub trait Tr {
    fn m(x: u32) -> u32 requires x != 0 {
        100 / x
    }
}
#[cfg(override_certify)]
pub struct S;
#[cfg(override_certify)]
impl Tr for S {
    fn m(x: u32) -> u32 requires x > 5 {
        //[override_certify]~^ ERROR a `requires` on a trait impl method is charged to no caller
        100 / (x - 5)
    }
}
#[cfg(override_certify)]
pub fn p(y: u32) -> u32 {
    if y != 0 { <S as Tr>::m(y) } else { 0 }
}

#[cfg(inherent_certify)]
pub struct S;
#[cfg(inherent_certify)]
impl S {
    pub fn div(&self, x: u32) -> u32 requires x != 0 {
        100 / x
    }
}
#[cfg(inherent_certify)]
pub fn p(y: u32) -> u32 {
    if y != 0 { S.div(y) } else { 0 }
}

#[cfg(total_impl_certify)]
pub trait Td {
    fn m(&self, x: u32) -> u32;
}
#[cfg(total_impl_certify)]
pub struct S;
#[cfg(total_impl_certify)]
impl Td for S {
    fn m(&self, x: u32) -> u32 {
        if x != 0 { 100 / x } else { 0 }
    }
}
#[cfg(total_impl_certify)]
pub fn p(y: u32) -> u32 {
    S.m(y)
}
