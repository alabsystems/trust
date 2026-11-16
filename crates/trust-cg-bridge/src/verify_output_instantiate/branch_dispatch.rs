// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! The step-(5) branch routes in order (DECISION_QUEUE BRANCH-SPLIT-1,
//! DIV-SPLIT-1 and CONSTDIV-1): the branch split first, the guarded symbolic
//! division split only when the branch split declined, and the constant
//! division route only when both declined.
//!
//! The frozen gate (`call_event.rs` step (5), both of its `branch` arms, and
//! `call_event/closed_branch.rs` `check` on the folded items) reaches this
//! through the unfrozen recording wrapper
//! `verify_output_instantiate::try_branch_split_conjunction`, which returns
//! this function's result unchanged. So this file decides what those sites
//! may accept:
//!
//! - whatever `branch_split::try_branch_split_conjunction` returns, unchanged,
//!   when it is `Some` (the branch split keeps every conjunction it proves,
//!   and its label);
//! - otherwise `div_split::try_conjunction`, unchanged when it is `Some`,
//!   which is `None` unless some side divides (unsigned) by a term with a
//!   variable and the kernel accepts the deep atom split against G built from
//!   the items alone;
//! - otherwise, and only when some side of some item holds the exact AArch64
//!   multiply-high shape ([`has_umulh`]), `const_div::try_conjunction`: the
//!   kernel accepts one term against the conjunction of
//!   `bvfEval R(l) = bvfEval R(r)` over the items as given (the ORIGINAL
//!   items, the 128-bit product form, never a step-(4) rewrite), its label the
//!   cited `Trust.BVD` theorems and the route's tail.
//!
//! All three routes return only `KernelInstantiated` evidence or `None`; none
//! can return `Refuted` or `Unknown`, so no verdict moves to or from either.

use trust_types::Formula;

use super::{branch_split, const_div, div_split};
use crate::verify_output::ProvenEvidence;

/// The branch split, then, on its decline, the guarded symbolic division
/// split, then, on its decline, the constant division route behind its
/// pre-filter.
pub(crate) fn try_conjunction(items: &[(Formula, Formula)]) -> Option<ProvenEvidence> {
    branch_split::try_branch_split_conjunction(items)
        .or_else(|| div_split::try_conjunction(items))
        .or_else(|| try_const_div(items))
}

/// The constant division route (CONSTDIV-1 stage B2), tried only when some
/// side of some item holds the multiply-high shape: the pre-filter only
/// declines, so the kernel never sees a conjunction without one.
fn try_const_div(items: &[(Formula, Formula)]) -> Option<ProvenEvidence> {
    #[cfg(feature = "test-hooks")]
    if CONST_DIV_OFF.with(std::cell::Cell::get) {
        return None;
    }
    if !items.iter().any(|(l, r)| has_umulh(l) || has_umulh(r)) {
        return None;
    }
    const_div::try_conjunction(items)
}

/// Does `f` contain `Extract{127,64}(BvMul(ZeroExt(a,64), ZeroExt(b,64), 128))`,
/// the AArch64 `umulh` (the exact shape `const_div::walk` admits above 64
/// bits)?
pub(crate) fn has_umulh(f: &Formula) -> bool {
    let mut found = false;
    f.visit(&mut |n| {
        if let Formula::BvExtract { inner, high: 127, low: 64 } = n
            && let Formula::BvMul(l, r, 128) = &**inner
            && matches!(**l, Formula::BvZeroExt(_, 64))
            && matches!(**r, Formula::BvZeroExt(_, 64))
        {
            found = true;
        }
    });
    found
}

#[cfg(feature = "test-hooks")]
thread_local! {
    static CONST_DIV_OFF: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// TEST HOOK (`test-hooks` only): run `body` with the constant division route
/// off on THIS thread (the dispatch then returns what the branch and division
/// splits return), so a gate test can pin the grade without it. It can only
/// take evidence away.
#[cfg(feature = "test-hooks")]
#[doc(hidden)]
pub fn without_const_div_conjunction<R>(body: impl FnOnce() -> R) -> R {
    let outer = CONST_DIV_OFF.with(|off| off.replace(true));
    let result = body();
    CONST_DIV_OFF.with(|off| off.set(outer));
    result
}
