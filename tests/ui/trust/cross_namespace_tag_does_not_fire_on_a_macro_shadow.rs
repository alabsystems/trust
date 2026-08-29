//@ ignore-test (red until the `def_path_data_namespace` narrowing is COMPILED — see below)
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//~? RAW Trust
//! The lost-recovery direction of the cross-namespace tag
//! (`cross_namespace_key_alias_stays_closed.rs` pins the other one). A
//! `#[macro_export] macro_rules! increment` beside a `pub fn increment` is the
//! ordinary Rust idiom and carries NO ambiguity in the def-path identity space —
//! a `macro_rules!` has no MIR body and is never a callee, a type or a `Self`, so
//! this seam never renders one. The function's path must therefore be spelled
//! exactly as it would be with no macro in the file.
//!
//! It was not. `def_path_data_namespace` admitted `MacroNs` into the sibling
//! index, so the macro counted as the second namespace and the FUNCTION — the
//! non-`TypeNs` half — was tagged. MEASURED, both states, on the STAGE2 `trustc`
//! built from `ddb545d35b`, with this file's own crate name, one identifier
//! apart (the second state is this file with the macro renamed `increment_m`):
//!
//! ```text
//! MacroNs in the index:  …_macro_shadow::increment#ns0v
//! macro renamed:         …_macro_shadow::increment
//! ```
//!
//! That is a spelling move on an honest path, and it is not free: it puts an
//! EXPORTED function into the crate-boundary asymmetry recorded as §RESIDUAL 7a,
//! where the DEFINITION renders `k::increment#ns0v` and every downstream crate
//! renders the same `DefId` as `k::increment` (measured with a two-crate probe).
//!
//! ELEVEN of the SEVENTEEN tags observed across rustc's own
//! `tests/ui/{generics,impl-trait,imports,macros,modules,structs,traits}` suites
//! (2876 source files) were this shape —
//! `cfg-expr`, `cfg_select-expr`, `meta-variable-misuse`, `macro-crate-use`,
//! `macro_crate_nonterminal`. The other SIX were genuine `TypeNs`/`ValueNs`
//! pairs and must keep their tags; `imports.rs`'s `mod test` + `fn test` and its
//! `pub mod f` + `pub fn f` are the ones to check if this file is ever "fixed"
//! by weakening the index further.
//!
//! WHY IGNORED, and what un-ignores it. The narrowing that makes this green is a
//! `trustc` source change, and it has NOT been compiled — `x.py` was not
//! available to its author, and the two states above were measured on a `trustc`
//! that still has `MacroNs` in the index. Landing this file live today would put
//! a knowingly-red test in the suite, which is its own defect. Delete the
//! `ignore-test` line in the same commit as the first `x.py build` that includes
//! the narrowing; if it is then still red, the narrowing did not take and the
//! narrowing — not this file — is what is wrong.
//!
//! CHECK THE SIBLING PROBE IN THE SAME BUILD. `DefKind::ExternCrate` is the same
//! defect in a namespace with no fixture of its own: `#![no_std] extern crate
//! alloc; pub fn alloc(..)` renders `k::alloc#ns0v` today against the
//! one-identifier control `extern crate alloc as ax;` -> `k::alloc`, and it is
//! filtered out of the index by the same change that narrows `MacroNs`. If this
//! file goes green and that probe does not, the `def_kind` filter is what failed.
#![no_std]
#[macro_export]
macro_rules! increment { ($x:expr) => { $crate::increment($x) } }

pub fn increment(x: u32) -> u32 {
    //~^ ERROR incomplete for `cross_namespace_tag_does_not_fire_on_a_macro_shadow::increment`:
    x + 1
}
