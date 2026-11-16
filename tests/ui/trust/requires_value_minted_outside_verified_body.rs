//@ revisions: static_field static_field_certify static_field_dep_memory_safe
//@ revisions: const_ptr_certify static_dyn_certify assoc_const_generic_certify
//@ revisions: trait_default_const_certify inline_const_certify anon_const_certify
//@ revisions: promoted_certify promoted_generic_certify const_call_hop_certify
//@ revisions: generic_const_arg_certify opaque_return_certify
//@ revisions: rpitit_certify trait_default_rpitit_certify
//@ revisions: generic_promoted_o0_certify
//@ revisions: static_field_advisory
//@ revisions: twin_certify closure_twin_certify
//@ revisions: sysroot_twin_certify ref_promoted_certify
//@ revisions: inline_const_item_certify inline_const_static_certify
//@ revisions: capture_o0_certify comptime_fn_certify tait_certify atpit_certify
//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: assume_total_requires_dep.rs
//@ aux-build: assume_total_callable_sink.rs
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[static_field_certify] compile-flags: -Ztrust-policy=certify
//@[static_field_dep_memory_safe] compile-flags: -Ztrust-policy=memory-safe
//@[const_ptr_certify] compile-flags: -Ztrust-policy=certify
//@[static_dyn_certify] compile-flags: -Ztrust-policy=certify
//@[assoc_const_generic_certify] compile-flags: -Ztrust-policy=certify
//@[trait_default_const_certify] compile-flags: -Ztrust-policy=certify
//@[inline_const_certify] compile-flags: -Ztrust-policy=certify
//@[inline_const_static_certify] compile-flags: -Ztrust-policy=certify
//@[anon_const_certify] compile-flags: -Ztrust-policy=certify
//@[promoted_certify] compile-flags: -Ztrust-policy=certify
//@[promoted_generic_certify] compile-flags: -Ztrust-policy=certify
//@[const_call_hop_certify] compile-flags: -Ztrust-policy=certify
//@[generic_const_arg_certify] compile-flags: -Ztrust-policy=certify
//@[opaque_return_certify] compile-flags: -Ztrust-policy=certify
//@[rpitit_certify] compile-flags: -Ztrust-policy=certify
//@[trait_default_rpitit_certify] compile-flags: -Ztrust-policy=certify
//@[generic_promoted_o0_certify] compile-flags: -Ztrust-policy=certify
//@[static_field_advisory] compile-flags: -Ztrust-policy=advisory
//@[twin_certify] compile-flags: -Ztrust-policy=certify
//@[closure_twin_certify] compile-flags: -Ztrust-policy=certify
//@[sysroot_twin_certify] compile-flags: -Ztrust-policy=certify
//@[ref_promoted_certify] compile-flags: -Ztrust-policy=certify
//@[inline_const_item_certify] compile-flags: -Ztrust-policy=certify
//@[capture_o0_certify] compile-flags: -Ztrust-policy=certify
//@[comptime_fn_certify] compile-flags: -Ztrust-policy=certify
//@[tait_certify] compile-flags: -Ztrust-policy=certify
//@[atpit_certify] compile-flags: -Ztrust-policy=certify
//@[static_field] check-fail
//@[static_field_certify] check-fail
//@[static_field_dep_memory_safe] check-fail
//@[const_ptr_certify] check-fail
//@[static_dyn_certify] check-fail
//@[assoc_const_generic_certify] check-fail
//@[trait_default_const_certify] check-fail
//@[inline_const_certify] check-fail
//@[inline_const_static_certify] check-fail
//@[anon_const_certify] check-fail
//@[promoted_certify] check-fail
//@[promoted_generic_certify] check-fail
//@[const_call_hop_certify] check-fail
//@[generic_const_arg_certify] check-fail
//@[opaque_return_certify] check-fail
//@[rpitit_certify] check-fail
//@[trait_default_rpitit_certify] check-fail
//@[generic_promoted_o0_certify] check-fail
//@[capture_o0_certify] check-fail
//@[comptime_fn_certify] check-fail
//@[tait_certify] check-fail
//@[atpit_certify] check-fail
//@[static_field_advisory] check-pass
//@[twin_certify] check-pass
//@[closure_twin_certify] check-fail
//@[sysroot_twin_certify] check-pass
//@[ref_promoted_certify] check-pass
//@[inline_const_item_certify] check-pass
//@ rustc-env:TRUST_VANILLA_DEBUG=1
//@[twin_certify] forbid-output: into a value that no call site charges
//@[closure_twin_certify] forbid-output: into a value that no call site charges
//@[sysroot_twin_certify] forbid-output: into a value that no call site charges
//@[ref_promoted_certify] forbid-output: into a value that no call site charges
//@[inline_const_item_certify] forbid-output: into a value that no call site charges
//@[capture_o0_certify] forbid-output: into a value that no call site charges
//@[twin_certify] forbid-output: [MINTED_VALUE]
//@[closure_twin_certify] forbid-output: [MINTED_VALUE]
//@[sysroot_twin_certify] forbid-output: [MINTED_VALUE]
//@[ref_promoted_certify] forbid-output: [MINTED_VALUE]
//@[inline_const_item_certify] forbid-output: [MINTED_VALUE]
//@[capture_o0_certify] forbid-output: [MINTED_VALUE]
//@[twin_certify] forbid-output: [CALLABLE_TYPE_ARG]
//@[ref_promoted_certify] forbid-output: [CALLABLE_TYPE_ARG]
//@[inline_const_item_certify] forbid-output: [CALLABLE_TYPE_ARG]
//@[capture_o0_certify] forbid-output: [CALLABLE_TYPE_ARG]
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! The minting-site seam (docs/KNOWN_HAZARDS.md, "`#[trust::assume_total]` charged none
//! of its calls", residual (b), and the ADT entry's "Not reached"; docs/DECISION_QUEUE.md,
//! AT-REQ-2): a function with a `requires` is verified UNDER it, so it may be reached only
//! where a call site charges the clause. Every rule of the indirect-call gate reads a
//! VERIFIED body. A `requires`-carrying function turned into a VALUE anywhere else was
//! refused by nobody — in a `static`, `const`, associated (a generic impl's, a trait
//! default), inline or anonymous constant's initializer, in a promoted of any owner, by a
//! generic `const fn` or generic constant an initializer hands it to, in a compile-time
//! (`#[rustc_comptime]`) function, or as the hidden type of an opaque type (an opaque
//! return `-> impl Fn(u32) -> u32 { add1 }`, an RPITIT, a TAIT, an ATPIT) — and the value
//! can reach code that calls it with any argument. `uncharged_callable::
//! refuse_requires_carrying_values_minted_outside_verified_bodies` refuses each at the site
//! that mints it: an error on the default policy, certify and memory-safe, a warning under
//! advisory.
//!
//! BEFORE (MEASURED 2026-10-03 on a stage 1 of `782780ea0d`, each revision compiled
//! directly with this file's flags and auxiliaries): every check-fail revision but
//! `generic_promoted_o0_certify` and `capture_o0_certify` compiles exit 0 (the review's
//! `comptime_fn_certify`, `tait_certify` and `atpit_certify` included, measured
//! 2026-10-03 on the same stage 1) — no pass reads the bodies, and no gate
//! reads a verified body's unevaluated constants (`generic_promoted_o3_certify`: at
//! `-Zmir-opt-level=2` the inlined `mk` leaves `f` only `Unevaluated { def: mk, promoted:
//! 0, args: [fn(u32) -> u32 {add1}] }`; linked into a verify-off `main`, `f(u32::MAX)`
//! RETURNED `0`); `static_field_advisory` has no warning; every control compiles.
//! `generic_promoted_o0_certify` is refused BEFORE and AFTER by rule (1) (the call
//! `mk::<fn(u32) -> u32 {add1}>`), the parity pin for the `-O3` revision.
//! `capture_o0_certify` is `capture_promoted_o3_certify`'s body at `-O0`: refused BEFORE
//! and AFTER, with the same two errors, by the native verifier's own rows alone (1.101:
//! the closure aggregate extracts on capture identity and the closure body refuses on
//! its own runtime-checked row beside `fk`'s) — no
//! `[CALLABLE_TYPE_ARG]`, no `[MINTED_VALUE]`. It pins that R4's carve-out at
//! `-Zmir-opt-level=2` matches what rule (1) does at `-O0` (neither refuses), not that
//! `-O0` accepts the body (a review of the seam, 2026-10-03, found R4's comment claiming
//! that).
//!
//! AFTER (MEASURED on the seam's stage 1; docs/KNOWN_HAZARDS.md names it): each positive
//! revision is refused with exactly one error, at its minting line, with the
//! `[MINTED_VALUE]` pin under `TRUST_VANILLA_DEBUG=1` (the gate's `[CALLABLE_TYPE_ARG]`
//! pin for `generic_promoted_*`). The controls: `twin_certify` and
//! `opaque_iter_twin_o3_certify`, every positive shape with the `requires`-free `inc`;
//! `closure_twin_certify`, a closure that establishes the clause and calls `add1`, in a
//! `static` and behind an opaque return (the closure is verified as its own body);
//! `sysroot_twin_certify`, a sysroot item (not asked); `ref_promoted_certify`, a promoted
//! `&add1` that mints nothing (local types are not walked); and the two the third critique
//! required, `capture_promoted_o3_certify` (a promoted of a LOCAL closure that captures
//! `add1`, inlined into its parent: walked as the closure type, so main's capture
//! carve-out holds) and `inline_const_item_certify` (an inline `const { add1 }` called
//! under a guard: its own type placeholder is not walked). Each control compiles exit 0
//! BEFORE and AFTER, except `closure_twin_certify`, whose `gc::{closure#0}` body refuses
//! on its own row (see that control); its gate and seam pins hold. `inc` and the `static_field_dep_memory_safe` alias stand in for `add1`
//! through `callee` (`dep::add1` there: memory-safe refuses a LOCAL `requires` function
//! at its own `assumption:requires` row, so the local `add1` is compiled out).
//! ERROR must be annotated; WARN need not be (advisory may report other rows), but the
//! advisory revision's own warning is.
#![allow(dead_code)]
#![cfg_attr(any(comptime_fn_certify, twin_certify), feature(rustc_attrs))]
#![cfg_attr(any(tait_certify, twin_certify), feature(type_alias_impl_trait))]
#![cfg_attr(any(atpit_certify, twin_certify), feature(impl_trait_in_assoc_type))]

#[cfg(static_field_dep_memory_safe)]
extern crate assume_total_requires_dep as dep;

#[cfg(any(
    const_call_hop_certify,
    generic_const_arg_certify,
    generic_promoted_o0_certify,
    twin_certify
))]
extern crate assume_total_callable_sink as sink;

#[cfg(not(static_field_dep_memory_safe))]
pub fn add1(x: u32) -> u32
    requires x < 100
{
    x + 1
}

#[cfg(twin_certify)]
pub fn inc(x: u32) -> u32 {
    x.wrapping_add(1)
}

#[cfg(any(
    static_field,
    static_field_certify,
    static_field_advisory,
    const_ptr_certify,
    static_dyn_certify,
    assoc_const_generic_certify,
    trait_default_const_certify,
    inline_const_certify,
    inline_const_static_certify,
    anon_const_certify,
    promoted_certify,
    promoted_generic_certify,
    const_call_hop_certify,
    generic_const_arg_certify,
    opaque_return_certify,
    rpitit_certify,
    trait_default_rpitit_certify,
    comptime_fn_certify,
    tait_certify,
    atpit_certify
))]
use crate::add1 as callee;

#[cfg(static_field_dep_memory_safe)]
use dep::add1 as callee;

#[cfg(twin_certify)]
use crate::inc as callee;

pub struct H {
    pub f: fn(u32) -> u32,
}

// A `static` initializer.
#[cfg(any(
    static_field,
    static_field_certify,
    static_field_dep_memory_safe,
    static_field_advisory,
    twin_certify
))]
pub static HS: H = H { f: callee };
//[static_field,static_field_certify,static_field_dep_memory_safe]~^ ERROR Trust verification failed for `requires_value_minted_outside_verified_body::HS` (a `static` initializer)
//[static_field_advisory]~^^ WARN Trust (advisory): Trust verification failed for

// A `const` item, reified with no field around it.
#[cfg(any(const_ptr_certify, twin_certify))]
pub const F: fn(u32) -> u32 = callee;
//[const_ptr_certify]~^ ERROR Trust verification failed for `requires_value_minted_outside_verified_body::F` (a `const` initializer)

// A `static` `&dyn Fn`: the unsizing cast's source carries the item.
#[cfg(any(static_dyn_certify, twin_certify))]
pub static D: &(dyn Fn(u32) -> u32 + Sync) = &callee;
//[static_dyn_certify]~^ ERROR Trust verification failed for

// An associated constant of a GENERIC impl: no evaluation is possible, and none is
// needed — the scan reads the polymorphic `mir_for_ctfe`.
#[cfg(any(assoc_const_generic_certify, twin_certify))]
pub struct K<T>(pub T);

#[cfg(any(assoc_const_generic_certify, twin_certify))]
impl<T> K<T> {
    pub const KF: fn(u32) -> u32 = callee;
    //[assoc_const_generic_certify]~^ ERROR Trust verification failed for
}

// A trait's DEFAULT associated constant.
#[cfg(any(trait_default_const_certify, twin_certify))]
pub trait Tr {
    const TF: fn(u32) -> u32 = callee;
    //[trait_default_const_certify]~^ ERROR Trust verification failed for
}

// An inline `const { … }`. In `fi` it returns a REFERENCE, so the reification is in the
// block's own PROMOTED (`fi::{constant#0}`'s promoted table); a bare fn-pointer constant
// is not lowered by the native verifier (`unsupported constant of MIR type fn(u32) ->
// u32`), which refused `fi` BEFORE the seam for that reason alone (MEASURED 2026-10-03,
// stage 1 of `782780ea0d`). In `FS` the block builds the value itself, so the
// reification is in the block's own `mir_for_ctfe`, read as an initializer.
#[cfg(any(inline_const_certify, twin_certify))]
pub fn fi() -> &'static H { const { &H { f: callee } } }
//[inline_const_certify]~^ ERROR Trust verification failed for a promoted constant in `requires_value_minted_outside_verified_body::fi::{constant#0}`

#[cfg(any(inline_const_static_certify, twin_certify))]
pub static FS: H = const { H { f: callee } };
//[inline_const_static_certify]~^ ERROR Trust verification failed for an inline `const` in `requires_value_minted_outside_verified_body::FS`

// An anonymous constant (an array length): its value cannot carry the pointer, so this
// pins the decision to include anonymous constants (fail-closed; AT-REQ-2).
#[cfg(any(anon_const_certify, twin_certify))]
pub fn fa() -> [u8; { let _p: fn(u32) -> u32 = callee; 1 }] { [0] }
//[anon_const_certify]~^ ERROR Trust verification failed for an anonymous constant in

// A promoted of a verified function, and of a generic one.
#[cfg(any(promoted_certify, twin_certify))]
pub fn fp() -> &'static H { &H { f: callee } }
//[promoted_certify]~^ ERROR Trust verification failed for a promoted constant in `requires_value_minted_outside_verified_body::fp`

#[cfg(any(promoted_generic_certify, twin_certify))]
pub fn fg<T>() -> &'static H { &H { f: callee } }
//[promoted_generic_certify]~^ ERROR Trust verification failed for a promoted constant in

// Rule (1) in an initializer: a verify-off generic `const fn` reifies `tramp::<F>` for the
// item it is handed, during const evaluation, where no cast in this crate shows it.
#[cfg(any(const_call_hop_certify, twin_certify))]
pub static HH: sink::H = sink::mk_h(callee);
//[const_call_hop_certify]~^ ERROR Trust verification failed for `requires_value_minted_outside_verified_body::HH` (a `static` initializer)

// Rule (4) in an initializer: a verify-off GENERIC constant mints the pointer, and the
// initializer instantiates it with the item (inferred from the later assignment).
#[cfg(any(generic_const_arg_certify, twin_certify))]
pub static HK: sink::H = { let mut k = sink::KH::<_>::V; k.0 = Some(callee); k.1 };
//[generic_const_arg_certify]~^ ERROR Trust verification failed for `requires_value_minted_outside_verified_body::HK` (a `static` initializer)

// Rule (7): a returned item leaves its body through the return place — no call, no cast.
#[cfg(any(opaque_return_certify, twin_certify))]
pub fn go() -> impl Fn(u32) -> u32 { callee }
//[opaque_return_certify]~^ ERROR Trust verification failed for the opaque return type of `requires_value_minted_outside_verified_body::go`

// An RPITIT in an impl (the trait's own declaration has no body and is skipped), and in a
// trait's default method.
#[cfg(any(rpitit_certify, twin_certify))]
pub trait Hg {
    fn g() -> impl Fn(u32) -> u32;
}

#[cfg(any(rpitit_certify, twin_certify))]
pub struct MyT;

#[cfg(any(rpitit_certify, twin_certify))]
impl Hg for MyT {
    fn g() -> impl Fn(u32) -> u32 { callee }
    //[rpitit_certify]~^ ERROR Trust verification failed for the opaque return type of
}

#[cfg(any(trait_default_rpitit_certify, twin_certify))]
pub trait Hd {
    fn gd() -> impl Fn(u32) -> u32 { callee }
    //[trait_default_rpitit_certify]~^ ERROR Trust verification failed for the opaque return type of
}

// A compile-time function (`#[rustc_comptime]`, `ConstContext::Const`): no verification
// pass reads it (it has no `optimized_mir`), and the `static` that calls it holds the
// value it makes. Read as its `mir_for_ctfe`, as an initializer is.
#[cfg(any(comptime_fn_certify, twin_certify))]
#[rustc_comptime]
fn mkh() -> H { H { f: callee } }
//[comptime_fn_certify]~^ ERROR Trust verification failed for `requires_value_minted_outside_verified_body::mkh` (a compile-time function)

#[cfg(any(comptime_fn_certify, twin_certify))]
pub static HM: H = mkh();

// A type-alias `impl Trait` (TAIT): the defining function returns the item through the
// return place, and callers see only `GT` — R7 reads the alias's hidden type.
#[cfg(any(tait_certify, twin_certify))]
pub type GT = impl Fn(u32) -> u32;
//[tait_certify]~^ ERROR Trust verification failed for the opaque type `requires_value_minted_outside_verified_body::GT`

#[cfg(any(tait_certify, twin_certify))]
#[define_opaque(GT)]
pub fn gt() -> GT { callee }

// An associated-type `impl Trait` (ATPIT): the same through an impl's associated type.
#[cfg(any(atpit_certify, twin_certify))]
pub trait Mk {
    type F: Fn(u32) -> u32;
    fn mk() -> Self::F;
}

#[cfg(any(atpit_certify, twin_certify))]
pub struct MkT;

#[cfg(any(atpit_certify, twin_certify))]
impl Mk for MkT {
    type F = impl Fn(u32) -> u32;
    //[atpit_certify]~^ ERROR Trust verification failed for the opaque type `<requires_value_minted_outside_verified_body::MkT as requires_value_minted_outside_verified_body::Mk>::F`
    fn mk() -> Self::F { callee }
}

// Rule (4) in the GATE. `mk` takes `&F`, not `F`: a dropped or forgotten `F` would leave a
// `Drop` terminator or a `forget::<fn(u32) -> u32 {add1}>` call in `f` for another rule to
// refuse, and this revision pins rule (4) alone.
#[cfg(generic_promoted_o0_certify)]
#[inline(always)]
fn mk<F: Fn(u32) -> u32>(_f: &F) -> &'static sink::H {
    &sink::H { f: sink::tramp::<F> }
}

// Trust (r15, 2026-10-07): `sink::run_h` is a verify-OFF dependency fn, an edge into
// unverified code, so `consume`'s `assume_total` skip is revoked and it is verified in
// full (`unverified_edges`; `unverified_edge_kinds.rs`), refused on that call.
#[cfg(generic_promoted_o0_certify)]
#[trust::assume_total]
#[inline(never)]
fn consume(h: &sink::H, y: u32) -> u32 {
    //[generic_promoted_o0_certify]~^ WARN does not cover its unsafe operations or its edges into code this compilation does not verify
    //[generic_promoted_o0_certify]~| ERROR Trust Level 0 safety verification incomplete for `requires_value_minted_outside_verified_body::consume`
    //[generic_promoted_o0_certify]~| ERROR Trust strict verification failed for `requires_value_minted_outside_verified_body::consume`
    sink::run_h(h, y)
}

#[cfg(generic_promoted_o0_certify)]
pub fn f(y: u32) -> u32 {
    //[generic_promoted_o0_certify]~^ ERROR Trust strict verification failed for `requires_value_minted_outside_verified_body::f`
    consume(mk(&add1), y)
}

// The controls.
//
// A closure that establishes the clause and calls `add1` directly: verified as its own
// body, where the call is charged and proved. It captures `k` behind the opaque return so
// it is no zero-sized constant (which the native lowering does not take).
// Re-pinned 2026-11-03 (the 1.101 port, merged trust-mc): both closure
// bodies' panic-freedom rows were `runtime_checked`, not proved, because
// trust-mc's operand-consumption guard refused the bridge's aggregate seed.
// Since BMC-LANE-1 (2026-11-06) the bridge builds a complete aggregate with
// `MakeAggregate`, and `HC`'s capture-free closure body is proved again. `gc`'s
// closure body still refuses on its own row, and not over a seed: it builds no
// aggregate (the environment is built in `gc`, which has no row), it reads `k`
// through its `&{closure}` environment parameter, and trust-mc's operand-consumption
// guard grants a root reference parameter's pointee no definedness. The same
// refusal (`OperandConsumption`) reproduces closure-free in `fn h(e: &(u32,), x: u32)`
// and `fn hr(e: &u32, x: u32)` (docs/DECISION_QUEUE.md BMC-LANE-1, "Not done"). The
// gate and the seam accept both shapes either way: the forbid-output pins below are
// unchanged.
#[cfg(closure_twin_certify)]
pub static HC: H = H { f: |x| if x < 100 { add1(x) } else { 0 } };

#[cfg(closure_twin_certify)]
pub fn gc(k: u32) -> impl Fn(u32) -> u32 {
    move |x| if x < 100 { add1(x) } else { k }
    //[closure_twin_certify]~^ ERROR Trust Level 0 safety verification incomplete for `requires_value_minted_outside_verified_body::gc::{closure#0}`
    //[closure_twin_certify]~| ERROR Trust strict verification failed for `requires_value_minted_outside_verified_body::gc::{closure#0}`
}

// A sysroot item is not asked: the sysroot is built verify-off and elides nothing.
#[cfg(sysroot_twin_certify)]
pub static FW: fn(u32, u32) -> u32 = u32::wrapping_add;

// A promoted `&add1`: a reference to the item, no value anyone can call through.
#[cfg(ref_promoted_certify)]
pub fn fr(y: u32) -> u32 {
    let _r = &add1;
    y
}

// A promoted of a LOCAL closure that captures `add1` (and `k`, so the closure is no
// zero-sized constant), inlined into `fk` at `-Zmir-opt-level=2`:
// `Unevaluated { def: {closure}, promoted, args: [.., (fn(u32) -> u32 {add1}, u32)] }`.
// `capture_o0_certify` is the same body at `-O0`: refused, but only by the native
// verifier's own rows (1.101: the closure aggregate extracts on capture identity
// and the closure body refuses on its own runtime-checked row, beside `fk`'s) —
// neither the gate (no `[CALLABLE_TYPE_ARG]`) nor the seam refuses it. So R4's carve-out
// at `-Zmir-opt-level=2` matches what rule (1) does at `-O0`; it does not make the body
// accepted at `-O0`.
#[cfg(capture_o0_certify)]
pub fn fk(y: u32, k: u32) -> &'static u32 {
    //[capture_o0_certify]~^ ERROR Trust Level 0 safety verification incomplete for `requires_value_minted_outside_verified_body::fk`
    //[capture_o0_certify]~| ERROR Trust strict verification failed for `requires_value_minted_outside_verified_body::fk`
    let g = add1;
    let c = move |x: u32| -> &'static u32 { if x < 100 && g(x) > k { &1 } else { &0 } };
    //[capture_o0_certify]~^ ERROR Trust Level 0 safety verification incomplete for `requires_value_minted_outside_verified_body::fk::{closure#0}`
    //[capture_o0_certify]~| ERROR Trust strict verification failed for `requires_value_minted_outside_verified_body::fk::{closure#0}`
    c(y)
}

// An inline `const { add1 }` whose value, the item, is called under a guard.
// Re-pinned 2026-11-03 to check-fail (the merged trust-mc guard left `fq`'s own
// panic-freedom row `runtime_checked`); back to check-pass since BMC-LANE-1
// (2026-11-06), where the bridge's complete constructor executes and the row is
// proved. The gate/seam acceptance never changed (the forbid-output pin below).
#[cfg(inline_const_item_certify)]
pub fn fq(y: u32) -> u32 {
    if y < 100 {
        let g = const { add1 };
        g(y)
    } else {
        0
    }
}

//[static_field,static_field_certify,static_field_advisory,const_ptr_certify,static_dyn_certify]~? RAW [MINTED_VALUE] `requires_value_minted_outside_verified_body::add1` owes its caller a `requires` and becomes a value in
//[assoc_const_generic_certify,trait_default_const_certify,inline_const_certify,inline_const_static_certify]~? RAW [MINTED_VALUE] `requires_value_minted_outside_verified_body::add1` owes its caller a `requires` and becomes a value in
//[anon_const_certify,promoted_certify,promoted_generic_certify]~? RAW [MINTED_VALUE] `requires_value_minted_outside_verified_body::add1` owes its caller a `requires` and becomes a value in
//[const_call_hop_certify,generic_const_arg_certify]~? RAW [MINTED_VALUE] `requires_value_minted_outside_verified_body::add1` owes its caller a `requires` and becomes a value in
//[opaque_return_certify,rpitit_certify]~? RAW [MINTED_VALUE] `requires_value_minted_outside_verified_body::add1` owes its caller a `requires` and becomes a value in the opaque return type of
//[trait_default_rpitit_certify]~? RAW [MINTED_VALUE] `requires_value_minted_outside_verified_body::add1` owes its caller a `requires` and becomes a value in the opaque return type of
//[static_field_dep_memory_safe]~? RAW [MINTED_VALUE] `assume_total_requires_dep::add1` owes its caller a `requires` and becomes a value in
//[comptime_fn_certify]~? RAW [MINTED_VALUE] `requires_value_minted_outside_verified_body::add1` owes its caller a `requires` and becomes a value in `requires_value_minted_outside_verified_body::mkh` (a compile-time function)
//[tait_certify]~? RAW [MINTED_VALUE] `requires_value_minted_outside_verified_body::add1` owes its caller a `requires` and becomes a value in the opaque type `requires_value_minted_outside_verified_body::GT`
//[atpit_certify]~? RAW [MINTED_VALUE] `requires_value_minted_outside_verified_body::add1` owes its caller a `requires` and becomes a value in the opaque type `<requires_value_minted_outside_verified_body::MkT as
//[generic_promoted_o0_certify]~? RAW [CALLABLE_TYPE_ARG] local item `add1` owes its caller a `requires`; not resolved
