//! Regression: the Trust mutual-recursion SCC graph must not contain a `#[rustc_comptime]` fn.
//!
//! `#[rustc_comptime]` lowers to `Constness::Const { always: true }`
//! (`rustc_ast_lowering/src/item.rs`), which `hir_body_const_context`
//! (`rustc_middle/src/hir/map.rs`) maps to `ConstContext::Const` rather than
//! `ConstContext::ConstFn`. `inner_mir_for_ctfe` therefore STEALS such a body's elaborated MIR
//! instead of cloning it, as it would for an ordinary `const fn`.
//!
//! The ordering that makes this reachable is ordinary compilation, not a corner case:
//!   1. `check_crate` eagerly evaluates every non-generic const item, so evaluating `N` calls
//!      `mir_for_ctfe(c)` and steals `c`'s elaborated MIR.
//!   2. `check_crate` runs BEFORE Trust's whole-crate verification walk.
//!   3. That walk requests `optimized_mir` for eligible bodies, and the first such request builds
//!      the crate-wide SCC graph.
//!
//! If that graph's node set included `c`, building the adjacency would read an already-stolen
//! `Steal` and hard-ICE with "attempted to read from stolen value".
//!
//! The fix is to exclude bodies that have no `optimized_mir` from the node set, NOT to guard the
//! borrow with `is_stolen()`: that call is documented as unusable inside rustc because it leaks
//! untracked state, the adjacency query is `cache_on_disk`, and its natural fallback — an empty
//! adjacency — is anti-conservative, since singleton components are discarded and `[]` therefore
//! reads as "known leaf" rather than "unknown".

//@ check-pass
#![feature(rustc_attrs)]

#[rustc_comptime]
fn comptime_leaf() -> usize {
    1
}

// Eagerly evaluated by `check_crate`, which steals `comptime_leaf`'s elaborated MIR.
const N: usize = comptime_leaf();

// An ordinary body, so the whole-crate verification walk requests `optimized_mir` and builds the
// SCC graph after the steal above has already happened.
fn anchor() -> usize {
    N
}

fn main() {
    let _ = anchor();
}
