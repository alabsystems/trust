//@ revisions: default certify memory_safe
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify
//@[memory_safe] compile-flags: -Ztrust-policy=memory-safe
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! SUMMARY-NAME-COLLIDE-1, the call-site half (2026-10-05): a call that runs one
//! body must not wear ANOTHER body's definition key.
//!
//! `summary_hrtb_impl_name_collision.rs` is the definition-side half: two impls
//! whose `get`s render one key. Here only ONE definition renders the key, and a
//! CALL prints as it. `W::<V<for<'a> fn(&'a u8) -> &'a u8>>::get` resolves to the
//! bounded GENERIC impl (its `V` is the `Marker`), which returns its argument; but
//! a call's name is printed from its arguments with lifetimes canonicalized to
//! `'_`, so it reads exactly like the CONCRETE sibling impl's key
//! (`V<for<'a> fn(&'a u8) -> &'static u8>`, a different type under the binder).
//! Every body-derived summary lane keyed the sibling's const set `{1}` under that
//! key and handed it to the call, and `y + 1` was proved. The trait form prints
//! the same way, because a call that resolves to a generic impl keeps the trait
//! spelling.
//!
//! BEFORE (stage 1 of `dc15b882f6` at `scratchpad/stage1-w16`, each revision's
//! own flags plus `--cfg <revision> --emit=metadata`, measured 2026-10-05):
//! `inherent` is `1 proved` and kernel-certified in all three revisions, with no
//! error or warning. `via_trait`'s `overflow:add` is proved and kernel-certified too; the
//! function is refused only by a runtime-checked absent-callee row. The two
//! controls, which call the concrete impl, are proved. The run witness is
//! `summary_generic_impl_call_key_alias_run.rs`.
//!
//! AFTER (the stage 1 of this change, measured the same way): the aliasing calls
//! are named apart from the sibling's key, so neither gets its summary and both
//! `[overflow:add]` rows are refuted by ay (`y = 4294967295`). Under `default` and
//! `certify` both functions are refused; under `memory_safe` the overflow is a
//! warning (a memory-safe panic) and `via_trait` is still refused by its
//! absent-callee row. The controls stay proved and kernel-certified: a call that
//! really runs the concrete impl keeps its name and its summary.
pub struct V<T>(pub T);
pub trait Marker {}
impl Marker for V<for<'a> fn(&'a u8) -> &'a u8> {}

// The inherent form.
pub struct W<T>(pub T);
impl<T: Marker> W<T> {
    pub fn get(x: u32) -> u32 {
        x
    }
}
impl W<V<for<'a> fn(&'a u8) -> &'static u8>> {
    pub fn get(_x: u32) -> u32 {
        1
    }
}

pub fn inherent(x: u32) -> u32 {
    //~^ NOTE [overflow:add] FAILED
    //[default,certify]~| ERROR Trust Level 0 safety verification incomplete
    //[default,certify]~| ERROR Trust strict verification failed
    //[memory_safe]~| WARN Trust Level 0 safety verification incomplete
    let y = W::<V<for<'a> fn(&'a u8) -> &'a u8>>::get(x);
    y + 1
}

pub fn inherent_control(x: u32) -> u32 {
    let y = W::<V<for<'a> fn(&'a u8) -> &'static u8>>::get(x);
    y + 1
}

// The trait form.
pub struct WT<T>(pub T);
pub trait Tr {
    fn get(x: u32) -> u32;
}
impl<T: Marker> Tr for WT<T> {
    fn get(x: u32) -> u32 {
        x
    }
}
impl Tr for WT<V<for<'a> fn(&'a u8) -> &'static u8>> {
    fn get(_x: u32) -> u32 {
        1
    }
}

pub fn via_trait(x: u32) -> u32 {
    //~^ NOTE [overflow:add] FAILED
    //[default,certify]~| ERROR Trust Level 0 safety verification incomplete
    //[default,certify]~| ERROR Trust strict verification failed
    //[memory_safe]~| WARN Trust Level 0 safety verification incomplete
    //[memory_safe]~| ERROR Trust memory-safe verification failed
    let y = <WT<V<for<'a> fn(&'a u8) -> &'a u8>> as Tr>::get(x);
    y + 1
}

pub fn via_trait_control(x: u32) -> u32 {
    let y = <WT<V<for<'a> fn(&'a u8) -> &'static u8>> as Tr>::get(x);
    y + 1
}
