//@ dont-check-compiler-stderr
//@ edition: 2018
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=on -Ztrust-policy=advisory
//@ needs-trust-verify
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//! Trust (wave-CT): a coroutine VALUE TYPE — the type of a `let _a = async {};`
//! binding, not the coroutine's own env param — carries the same fact-free
//! `opaque_alias` sort that wave-PO2b (49d8684270) already mints for the VALUE
//! at these very sites.
//!
//! This closes a SKEW rather than opening a lane. PO2b lowers the literal to
//! `Const { Ty::Struct(opaque_alias), Aggregate[] }`, but the binding's own type
//! fell to `map_ty`'s catch-all and came back `Ty::Unit` — the local was
//! DECLARED at one sort and INITIALIZED at another, and the `Ty` tag was all
//! that kept these bodies out of the clean set. `strict` turns that tag into a
//! compile error, so this file is the mutation check: every body below fails on
//! the control build and compiles on the subject.
//!
//! EFFECT CONSERVATION (D28, 2026-10-01): the four fns drop coroutine VALUES (a coroutine's drop
//! glue depends on its state and saved locals, which rustc's own `needs_drop` does not compute
//! either), while each `async {}` body's drop of its OWN env runs nothing and stays clean. The
//! direct trust-ir emits no `Drop` yet, so the effect-conservation gate tags each such body
//! `Abstracted(drop, ..)` and strict refuses it (expected below). A producer tag would still be
//! its own, unannotated, strict error, so this file keeps its mutation check.

/// The `issue-54752-async-block.rs` shape, verbatim.
fn async_block_local() {
    //~^ ERROR the effect-conservation check refused it against the built MIR
    let _a = async {};
}

/// Two coroutine sorts in one body. They deliberately share ONE struct: the
/// sort "stands for MANY distinct pre-mono types at once" by `mint_alias_opaque_struct`'s
/// own contract, exactly as the alias lane collapses `<S as Tr>::Ok` and `::Error`.
fn two_sorts() {
    //~^ ERROR the effect-conservation check refused it against the built MIR
    let _a = async {};
    let _b = async {};
}

/// The type in a non-binding position: produced, then dropped unnamed.
fn discarded() {
    //~^ ERROR the effect-conservation check refused it against the built MIR
    let _ = async {};
}

/// An async block behind a reference — the type appears as a pointee, which is
/// where `map_ty` is re-entered rather than called at the binding.
fn behind_ref() {
    //~^ ERROR the effect-conservation check refused it against the built MIR
    let a = async {};
    let _r = &a;
}

fn main() {
    async_block_local();
    two_sorts();
    discarded();
    behind_ref();
}
