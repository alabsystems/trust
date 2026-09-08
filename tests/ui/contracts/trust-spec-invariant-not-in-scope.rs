//! Trust: with no `trust` crate linked, the `trust::invariant` path must still
//! be REFUSED — the refusal must not become a quieter way to accept it.
//!
//! This pins the OTHER end of the refusal. The property being guarded has not
//! changed since this test was written: a `trust::` annotation in a crate that
//! never linked the `trust` spec crate must not compile clean, because a builtin
//! (or a tool registration) that silently answers for it would accept the
//! annotation while verifying nothing.
//!
//! WHAT CHANGED (2026-08-30) IS *WHY* IT IS REFUSED, NOT WHETHER. `trust` is now
//! a PREDEFINED tool (`rustc_resolve::macros::registered_tools_ast`), which is
//! what lets `#[trust::skip]` and the rest of the verify-pass vocabulary work
//! without a hand-written `#![register_tool(trust)]`. The path therefore
//! resolves, so this is no longer `E0433: cannot find module or crate 'trust'`.
//!
//! It is a STRONGER outcome than the old one, and that is the thing to check
//! when this file next changes. `invariant` is a CLAIMED name in
//! `trust_types::trust_attr_namespace` — `trust-mir-extract`'s
//! `contract_kind_from_name` reads it off `attr.path().last()` out of the HIR
//! attributes, and an inert tool attribute survives into HIR — so the annotation
//! is now genuinely CONSUMED here rather than unresolved. Measured on the stage2
//! built from this commit: it produces two obligations, and the second names the
//! defect precisely ("item-position `invariant` names no program point, so it
//! has no exact meaning to lower"). Under the default strict policy that is a
//! build error. So the annotation is no longer accepted-while-verifying-nothing;
//! it is read, refused, and told what to write instead.
//!
//! The companion half — a name NO consumer claims, which cannot be refused this
//! way because nothing lowers it — is `tests/ui/trust/tool_attr_unknown_refused.rs`,
//! where the E5 conservation check in `rustc_resolve` supplies the refusal. The
//! two together are what make tool registration safe: every `trust::` name is
//! either consumed (and judged on its merits, as here) or refused by name.
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ edition: 2021

#![allow(dead_code)]

#[trust::invariant(x > 0)]
fn annotated(x: i32) -> i32 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    x
}

fn main() {}
