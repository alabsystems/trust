//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! MUTANT: a callee key the `dyn` reliance rule discharges must not carry that
//! discharge to a bundled call the rule never examined.
//!
//! Per-site grouping is not enough. `trust_mir_extract::func_operand_name` is
//! MANY-TO-ONE inside one crate, and the discharge channel the bridge reads is a
//! set of those STRINGS, so it is not enough for every VIRTUAL site under a key
//! to discharge — no other bundled call may render to that key either. Gate 0's
//! `CallKeyLedger` records which lane certified each bundled call and refuses any
//! key that is not exclusively this lane's.
//!
//! The collision is built from a supertrait call and a `dyn`-typed impl, and it
//! is real, not injected:
//!
//! * a virtual call to a SUPERTRAIT method through `&dyn Sub` renders
//!   `<dyn drive::Sub as drive::Super>::m` — the two names differ, which is what
//!   makes the shape reachable at all;
//! * in the second block, `Sub` is a plain marker trait, so `impl Super for dyn
//!   Sub {}` is legal and inherits `Super`'s DEFAULT `m`. The direct call
//!   `<dyn Sub as Super>::m(t)` resolves to that trait default — an
//!   `InstanceKind::Item`, NOT a `Virtual`, so it is no site of this rule — and
//!   `devirtualized_callee_name` declines to rename it (it is not an impl item),
//!   leaving `def_path_str_with_args(Super::m, [dyn Sub])`. Block-scoped names
//!   carry no disambiguator, so that is the SAME string.
//! * `#[trust::skip]` keeps its `panic!()` body out of the bundle, so the call
//!   rides the bridge's fail-closed absent-callee arm — exactly the row an
//!   inserted key would drop.
//!
//! MEASURED, both states, on builds one mutation apart. With gate 0 present:
//!
//! ```text
//! site=<dyn …drive::Sub as …drive::Super>::m (1 site(s))
//!     => kept (callee key ALIASES a bundled call this rule did not certify)
//! ```
//!
//! With `only_dyn_sites` disabled at the decision site, the probe instead prints
//! `C-FLOW admitted 1 target(s)` / `=> DISCHARGED` and the
//! `Trust strict verification failed for … drive` error below DISAPPEARS — the
//! skipped, `panic!()`-bodied call was credited with the FIRST block's proof.
//! That error's absence is what this fixture grades: the `skipped` error stays
//! either way, so the exit code alone does not witness this gate.
//!
//! Note the arithmetic of the group: there is only ONE virtual site here and it
//! passes every C-FLOW conjunct. Group-wide all-or-nothing is therefore NOT what
//! closes this file — gate 0 is the only thing holding it.
//!
//! # THE ALIAS THIS FILE WAS MINTED FOR IS NOW CLOSED AT THE RENDERING SEAM
//!
//! `trust_mir_extract::safe_def_path_str` renders under
//! `with_def_path_disambiguators`, so the second block's `trait Super` renders
//! `…drive::Super#1` and its `<dyn Sub as Super>::m` call NO LONGER SHARES the
//! first block's key. MEASURED on this tree: the graded
//! `Trust strict verification failed` and `Trust full verification skipped`
//! errors are both still emitted, with identical counts; the only stderr delta is
//! the `#1` spelling. The `#[trust::skip]` `panic!()` body is its own
//! fail-closed reason.
//!
//! COVERAGE CONSEQUENCE, stated so nobody mistakes this for a live guard: gate 0
//! is no longer what holds this file. Disabling `only_dyn_sites` would not make
//! the `strict verification failed` error disappear any more, because the
//! discharged key no longer names the skipped call. It stays the historical record
//! of the exploit; gate 0's live coverage is now the residual the seam cannot
//! reach — two impls that instantiate to one `<self_ty as trait_ref>` under one
//! parent (specialization), and a GENERIC call whose key is spelled like a
//! generic DEFINITION's path, a MEASURED still-open false proof. Both are
//! enumerated on `direct_call_def_path`. The key is narrowed, NOT injective.
#![no_std]
#![allow(dead_code)]
#![feature(register_tool)]
#![register_tool(trust)]

pub fn drive() -> u32 {
    //~^ ERROR Trust strict verification failed
    let a = {
        // A provable virtual site: C-FLOW admits `S`, so this key WOULD be
        // discharged if it named nothing else.
        trait Super {
            fn m(&self) -> u32;
        }
        trait Sub: Super {}
        struct S;
        impl Super for S {
            fn m(&self) -> u32 {
                1
            }
        }
        impl Sub for S {}
        let s = S;
        let t: &dyn Sub = &s;
        t.m()
    };
    let b = {
        // Same two names, no supertrait relation — so `dyn Sub` does not already
        // implement `Super` and this impl is legal. Its call renders the SAME
        // callee key and is certified by NO lane.
        trait Super {
            #[trust::skip]
            fn m(&self) -> u32 {
                //~^ ERROR Trust full verification skipped
                panic!()
            }
        }
        trait Sub {}
        struct S;
        impl Sub for S {}
        impl Super for dyn Sub {}
        let s = S;
        let t: &dyn Sub = &s;
        <dyn Sub as Super>::m(t)
    };
    a.wrapping_add(b)
}
