//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type=lib

//! **Registering the `trust` tool must not make a bad attribute SILENT — and the
//! refusal must reach a crate that never wrote `#![register_tool(trust)]`.**
//!
//! `trust` is a predefined tool (`rustc_resolve::macros::registered_tools_ast`),
//! which is what lets `#[trust::skip]` work in a crate that never wrote
//! `#![register_tool(trust)]`. The cost of registering it is that an unknown
//! `trust::` path stops being `E0433: cannot find module or crate 'trust'` and
//! becomes an INERT tool attribute — a strictly worse outcome, because the
//! annotation then compiles clean while asserting nothing. Measured before the
//! companion check landed: `#![register_tool(trust)]` plus
//! `#[trust::invariant(false)]` compiled with NO diagnostic at all, and the
//! `ExpandTrustInvariant` refusal that exists for exactly that spelling was
//! never reached.
//!
//! The E5 conservation check in `rustc_resolve::macros::smart_resolve_macro_path`
//! closes that hole. `trust_attr_namespace_conservation.rs` is the fixture for
//! the check itself, and it writes `#![register_tool(trust)]` explicitly. THIS
//! file is the #42 half: the same refusal must fire in a crate that registers
//! nothing, because that is now every crate in the fleet. If the predefined tool
//! entry is removed these become `E0433` instead, and if the check is gated back
//! behind anything the registration is not gated on, they become silence.
//!
//! The clean side — that all supported spellings still pass, also without
//! `register_tool` — is pinned by the sibling `tool_attr_vocabulary_accepted.rs`.

// A one-keystroke misspelling of `assume_total`. Inert without the check, and the
// diagnostic must name the intended attribute rather than only refusing.
#[trust::asume_total] //~ ERROR is not a Trust attribute
pub fn typo() {}

// Not Trust vocabulary at all, and near nothing — no suggestion is better than a
// confidently wrong one.
#[trust::totally_made_up] //~ ERROR is not a Trust attribute
pub fn unknown() {}

// A deeper path in the reserved namespace. Nothing reads a claimed name out of
// one, so `skip` does not launder it.
#[trust::skip::garbage] //~ ERROR is not a Trust attribute
pub fn deeper_path() {}

// `loop_invariant` is claimed ONLY by the pre-resolution loop-clause recognizer
// (`ast::trust_contract::trust_loop_clause_attr_kind`), which matches a `while` /
// `loop` HEADER and removes the attribute. On an ITEM there is no header, so the
// recognizer never claims it and it arrives here. That used to die as an
// unresolved attribute; predefining the tool would have turned that death into
// silence, and leaving `loop_invariant` out of the vocabulary is what keeps the
// loop-clause surface fail-closed. See the module-level bullet in
// `trust_types::trust_attr_namespace`.
#[trust::loop_invariant(true)] //~ ERROR is not a Trust attribute
pub fn misplaced_loop_clause() {}
