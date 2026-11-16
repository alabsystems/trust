//@ needs-trust-verify
//@ edition: 2021
//@ revisions: o0 o3plain off
//@[o0] compile-flags: -Ztrust-verify=on --crate-type lib -Copt-level=0
//@[o3plain] compile-flags: -Ztrust-verify=on --crate-type lib -Copt-level=3
//@[off] compile-flags: -Ztrust-verify=off --crate-type lib
//@[o0] check-fail
//@[o3plain] check-fail
//@[off] check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! REGRESSION (2026-09-25, found publishing ay's `ay-dpll`): a recursion the LOCAL
//! call graph cannot see — `from_apply` calls the GENERIC `fold_children`, which
//! reaches `from_apply` again only as a fn item handed to `Iterator::map` — must
//! end in a TRUST VERDICT, never `error[E0391]: cycle detected when optimizing
//! MIR for ...::fold_children`.
//!
//! Measured BEFORE on stage-1 `ab7e41892` (origin/main): E0391 at every
//! `-Copt-level` 0..=3, as a lib and under `--test`; `-Ztrust-verify=off` built.
//!
//! THE CYCLE. `optimized_mir(fold_children)` -> its collection's axiom census
//! (`follow_user_axiom_pointer_hop`, reading the `T::from_apply` fn-item operand)
//! -> `optimized_mir(from_apply)` -> `from_apply`'s collection ->
//! `build_callee_contract_summaries` -> `derived_bundled_member_summary` for the
//! local generic instance `fold_children::<fn(T, T) -> T {T::then}>` ->
//! `instance_mir` = `optimized_mir(fold_children)`: the query already on the
//! stack. The static SCC (`trust_mir_is_mutually_recursive`) has no edge for a fn
//! item passed as a value, so only the live in-progress set can see it — and the
//! bundle build's own mono drain DOES consult it for the same member
//! (`mono-optimized-mir-would-cycle`); this second reader of the same
//! would-be-bundled set did not.
//!
//! THE FIX. `derived_bundled_member_summary` declines exactly as the drain does.
//! `from_apply` then keeps `fold_children` as an unproved generic absent callee and
//! is refused (fail-closed; no credit for the re-entrant edge). `then` is refused on
//! its own (drop glue of `T`), independent of the cycle.
#![allow(dead_code)]

pub enum A { Leaf, Then(Vec<A>) }
pub enum T { Skip, Then(Box<T>, Box<T>) }
impl T {
    pub fn from_apply(a: &A) -> T {
        //[o0,o3plain]~^ ERROR Trust strict verification failed for `generic_fn_item_recursion_no_query_cycle::T::from_apply`
        //[o0,o3plain]~| NOTE an unproved assumption-panic row — a generic absent callee — keeps the function fail-closed
        match a { A::Leaf => T::Skip, A::Then(c) => Self::fold_children(c, T::then) }
    }
    fn fold_children(children: &[A], combine: impl Fn(T, T) -> T) -> T {
        //[o0,o3plain]~^ ERROR Trust strict verification failed for `generic_fn_item_recursion_no_query_cycle::T::fold_children`
        let mut it = children.iter().map(T::from_apply);
        let first = it.next().unwrap_or(T::Skip);
        it.fold(first, combine)
    }
    pub fn then(self, n: T) -> T { T::Then(Box::new(self), Box::new(n)) }
    //[o0,o3plain]~^ ERROR Trust strict verification failed for `generic_fn_item_recursion_no_query_cycle::T::then`
}
