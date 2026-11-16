//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ edition: 2024
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-pass
//! The predefined `trust` TOOL surface — `#[trust::requires(..)]` and
//! `#[trust::ensures(..)]` with no `trust` crate in scope — is an exact
//! desugaring of the native clause (docs/TWO_LANGUAGE_100_PERCENT_GOAL.md §3).
//! Every attribute function below has a native twin, and each pair must report
//! the SAME `Trust verification:` row.
//!
//! On main (2026-09-29) each `div_*` row is `1 proved, 0 failed, 0 unknown` with
//! `1 assumed (requires)`: the division is proved and the `requires` itself is a
//! definition-entry assumption every caller must establish.
//!
//! Measured on seal `321aaeda7` (2026-09-29), before
//! `trust_tool_contract_attr_extension` in `rustc_resolve` (the seal counted the
//! `requires` row as proved):
//!
//! * native twins: 3 proved (`abort_native`), 2 proved (`div_native`);
//! * the same attributes through the trust-spec shim (`--extern trust=`): the
//!   same rows;
//! * the same attributes on the tool surface: `0 proved, 0 failed, 3 unknown`
//!   and `1 proved, 0 failed, 1 unknown`. The attribute stayed inert and
//!   `trust-mir-extract` read it back out of raw HIR, ending at "compiler
//!   contract predicate `!self.storage.detached` was not lowered into a typed
//!   verifier formula".
//!
//! `abort_*` is the shape of aterm's grid wedge guard
//! (`aterm:crates/aterm-grid/src/grid/scrollback_offload.rs`,
//! `abort_reflow_offload`): a two-level `&mut self` field projection
//! discharged across an early return. Its rows depend on TODAY's reading of
//! `self.storage.detached` in an `ensures` as the EXIT value; D2 reads an
//! unprimed parameter at entry (docs/design/2026-07-09-two-language-spec-surface.md
//! §3, D2). When that lands, both twins flip together, which is the point of
//! pinning them side by side.

pub struct Storage {
    pub detached: bool,
}

pub struct Window {
    pub storage: Storage,
}

impl Window {
    pub fn abort_native(&mut self) //~ NOTE Trust verification: 3 proved, 0 failed, 0 unknown
        ensures !self.storage.detached
    {
        if !self.storage.detached {
            return;
        }
        self.storage.detached = false;
    }

    #[trust::ensures(!self.storage.detached)]
    pub fn abort_tool(&mut self) { //~ NOTE Trust verification: 3 proved, 0 failed, 0 unknown
        if !self.storage.detached {
            return;
        }
        self.storage.detached = false;
    }
}

pub fn div_native(n: u32, d: u32) -> u32 //~ NOTE Trust verification: 1 proved, 0 failed, 0 unknown
    requires d > 0
{
    n / d
}

#[trust::requires(d > 0)]
pub fn div_tool(n: u32, d: u32) -> u32 { //~ NOTE Trust verification: 1 proved, 0 failed, 0 unknown
    n / d
}
