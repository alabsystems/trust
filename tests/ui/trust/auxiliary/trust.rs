//! Trust: minimal stand-in for the `trust-spec` passthrough proc-macro crate
//! (its lib crate name is `trust`). Under tRustc, the resolver's spec-contract
//! hook (`trust_spec_contract_attr_extension`) replaces these crate-root
//! `trust::{requires,ensures,invariant}` attribute proc macros with the
//! compiler-owned Trust contract builtins before expansion, so the passthrough
//! bodies below never run for those three attributes.
//!
//! `requires` and `ensures` are replaced by LOWERINGS. `invariant` is replaced
//! by a REFUSAL (`ExpandTrustInvariant`) — it must keep resolving so that the
//! refusal is reachable and can carry its fix, but it has no verified meaning.
//! `decreases` is a DESUGARING (`ExpandTrustDecreases`): the builtin re-emits
//! the native `decreases <e>` clause spelling verbatim, so the attribute and
//! first-class surfaces are one implementation. (An earlier revision of this
//! file said `decreases` was "deliberately absent here ... it is E0433"; that
//! was true before the D4 lane and is now false.)

// Auxiliary proc-macro crates are built at the default (2015) edition, where
// `proc_macro` is not in the extern prelude for `use` paths: declare it.
extern crate proc_macro;

use proc_macro::TokenStream;

#[proc_macro_attribute]
pub fn requires(_attr: TokenStream, item: TokenStream) -> TokenStream {
    item
}

#[proc_macro_attribute]
pub fn ensures(_attr: TokenStream, item: TokenStream) -> TokenStream {
    item
}

// Mirrors `trust-spec`'s `invariant`: a REFUSAL, not a passthrough. Under
// `-Z trust-verify=on` the resolver swaps this out for `ExpandTrustInvariant`
// and this body never runs; under `-Z trust-verify=off` (which is what
// compiletest passes for the `ui` suite) there is no swap, so this body is the
// only thing standing between the annotation and silent erasure.
#[proc_macro_attribute]
pub fn invariant(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let mut out: TokenStream = concat!(
        "compile_error!(\"`trust::invariant` is not a verified contract surface: it is never ",
        "checked on any lane, so it states a guarantee nothing enforces. For a loop invariant, ",
        "use a first-class loop clause: `while <cond> invariant <predicate> { ... }` or ",
        "`loop invariant <predicate> { ... }`. For a ",
        "condition that must hold on entry, use `#[trust::requires(<predicate>)]`. For a ",
        "condition that must hold on return, use `#[trust::ensures(move |r: &T| <predicate>)]`. ",
        "Otherwise delete the attribute: leaving it in place states nothing.\");",
    )
    .parse()
    .expect("the compile_error! invocation above is a string literal and must parse");
    out.extend(item);
    out
}

// Trust (D4): the compat spelling of the first-class `decreases e` clause. The
// resolver replaces this one too, with a builtin that re-emits the NATIVE
// clause spelling, so the passthrough body below never runs under `-Z
// trust-verify=on` either.
#[proc_macro_attribute]
pub fn decreases(_attr: TokenStream, item: TokenStream) -> TokenStream {
    item
}
