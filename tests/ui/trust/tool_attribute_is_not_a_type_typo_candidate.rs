//@ compile-flags: -Z trust-verify=off
//! **REGRESSION.** A registered tool name must never be offered as a typo
//! candidate for a type, a trait or a value.
//!
//! `Scope::ToolPrelude` in `compiler/rustc_resolve/src/error_helper.rs` used to
//! extend the candidate list without consulting `filter_fn`, unlike every
//! sibling arm in the same match. Upstream never noticed because none of its own
//! predefined tool names lands near a common type name; `trust` does, so the
//! hole became visible the moment Trust joined `predefined_tools` —
//! `tests/ui/suggestions/suggest-swapping-self-ty-and-trait.rs` began rendering
//!
//! ```text
//! help: a tool attribute with a similar name exists
//! LL - impl<'a, T> Struct<T> for Trait<'a, T> {}
//! LL + impl<'a, T> trust<T> for Trait<'a, T> {}
//! ```
//!
//! where upstream labels the type `not a trait`. The hole was never
//! Trust-specific, which is why the value row below misspells `clippy`, one of
//! upstream's own predefined tools.
//!
//! READ THE SCOPE CHAIN BEFORE CHANGING ANY ROW HERE. `visit_scopes`
//! (`compiler/rustc_resolve/src/ident.rs`) reaches `Scope::ToolPrelude` from
//! exactly one predecessor, `Scope::ExternPreludeFlags`, and
//! `Scope::ExternPreludeItems` is only entered from `Scope::ModuleGlobs` when
//! `ns == TypeNS`. The value chain ends `StdLibPrelude -> break`, and the macro
//! chain ends `MacroUsePrelude -> StdLibPrelude -> BuiltinAttrs -> break`;
//! neither visits the tool prelude. Two consequences, and they are NOT the same:
//!
//!   * the two TYPE-namespace rows are the regression guards — a trait bound
//!     resolves in `TypeNS` too — and that is A/B MEASURED, not inferred. With
//!     the guard reverted and stage1 rebuilt, this file fails, and its actual
//!     stderr offers `fn in_a_type_position(_: trust)` and `T: trust` under
//!     `help: a tool attribute with a similar name exists`;
//!   * the VALUE row got NO suggestion on that same unfixed build. It is a
//!     control, not a guard: `ValueNS` cannot reach the tool prelude. It is here
//!     so that widening the arm to `ValueNS` — which would read as a harmless
//!     generalisation — cannot pass unnoticed.
//!
//! By the same chain a misspelled bare `#[trast]` got no tool suggestion before
//! the fix either, and gets none after: do not "restore" one by loosening the
//! filter, and do not add an attribute row here expecting one.
//!
//! The arm's `res` is wrong too, and deliberately left alone: it reports
//! `Res::NonMacroAttr(NonMacroAttrKind::Tool)` ("a tool attribute") while the
//! binding a registered tool actually gets is `Res::ToolMod`
//! (`Resolver::registered_tool_decls`). With `filter_fn` applied no caller
//! accepts either one, so the value is unobservable and correcting it could not
//! be measured. It is recorded here instead of changed blind.

fn in_a_type_position(_: trast) {}
//~^ ERROR cannot find type `trast` in this scope

fn in_a_trait_position<T: trast>(_: T) {}
//~^ ERROR cannot find trait `trast` in this scope

fn in_a_value_position() -> u32 {
    clippa
    //~^ ERROR cannot find value `clippa` in this scope
}

// CONTROL — a CORRECTLY spelled tool attribute must still resolve. The filter
// narrows a suggestion list, not the tool prelude itself; if it had narrowed the
// prelude, this line would add a fourth error and the pinned stderr below would
// stop matching.
#[clippy::this_name_is_never_checked]
fn tool_attributes_still_resolve() {}

fn main() {}
