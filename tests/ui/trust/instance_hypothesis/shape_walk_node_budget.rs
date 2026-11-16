//@ revisions: advisory strict certify
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-output=human --crate-type=lib
//@[advisory] compile-flags: -Ztrust-policy=advisory
//@[strict] compile-flags: -Ztrust-policy=strict
//@[certify] compile-flags: -Ztrust-policy=certify
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@[advisory] check-pass
//@[strict] check-fail
//@[certify] check-fail
//! OD-1 item 18 review fix: the argument-shape walk has a NODE BUDGET
//! (`SHAPE_NODE_BUDGET`, 4096 visits per argument). The walk builds a tree, re-walking
//! every field occurrence, so with the depth cap at 16 its cost was `branching ^ depth`:
//! `D0` below (four copies of the next level, 15 levels) took ~30 s per revision and a
//! branching-8, 12-level chain did not finish in 180 s. A walk that spends its budget is
//! `Opaque`, which every access path refuses, so the budget only ever refuses more.
//!
//! Admitted: `wide_admitted` (`&W0`, ~2.4k nodes, inside the budget). Discharge:
//! `use_fine` (proved, counted skipped), `use_boom` (`Boom::look_w` panics: `failed`).
//! Refused (class (c) `failed`): `over_budget_refused` (`&V0`: depth 10, inside the cap,
//! but ~33k nodes — ADMITTED before the budget, so this revision pair fails without it),
//! `over_depth_refused` (`&D0`: beyond the depth cap; refused before too, and must now
//! finish in the budget's time rather than the exponential walk's).
// Admitted: a wide type well inside the budget.
pub struct W0 { pub a: W1, pub b: W1, pub c: W1, pub d: W1 }
pub struct W1 { pub a: W2, pub b: W2, pub c: W2, pub d: W2 }
pub struct W2 { pub a: W3, pub b: W3, pub c: W3, pub d: W3 }
pub struct W3 { pub a: W4, pub b: W4, pub c: W4, pub d: W4 }
pub struct W4 { pub a: W5, pub b: W5, pub c: W5, pub d: W5 }
pub struct W5 { pub x: u8 }
// Refused: within the depth cap, but beyond the node budget.
pub struct V0 { pub a: V1, pub b: V1, pub c: V1, pub d: V1 }
pub struct V1 { pub a: V2, pub b: V2, pub c: V2, pub d: V2 }
pub struct V2 { pub a: V3, pub b: V3, pub c: V3, pub d: V3 }
pub struct V3 { pub a: V4, pub b: V4, pub c: V4, pub d: V4 }
pub struct V4 { pub a: V5, pub b: V5, pub c: V5, pub d: V5 }
pub struct V5 { pub a: V6, pub b: V6, pub c: V6, pub d: V6 }
pub struct V6 { pub a: V7, pub b: V7, pub c: V7, pub d: V7 }
pub struct V7 { pub x: u8 }
// Refused: beyond the depth cap (it was before too); must finish fast.
pub struct D0 { pub a: D1, pub b: D1, pub c: D1, pub d: D1 }
pub struct D1 { pub a: D2, pub b: D2, pub c: D2, pub d: D2 }
pub struct D2 { pub a: D3, pub b: D3, pub c: D3, pub d: D3 }
pub struct D3 { pub a: D4, pub b: D4, pub c: D4, pub d: D4 }
pub struct D4 { pub a: D5, pub b: D5, pub c: D5, pub d: D5 }
pub struct D5 { pub a: D6, pub b: D6, pub c: D6, pub d: D6 }
pub struct D6 { pub a: D7, pub b: D7, pub c: D7, pub d: D7 }
pub struct D7 { pub a: D8, pub b: D8, pub c: D8, pub d: D8 }
pub struct D8 { pub a: D9, pub b: D9, pub c: D9, pub d: D9 }
pub struct D9 { pub a: D10, pub b: D10, pub c: D10, pub d: D10 }
pub struct D10 { pub a: D11, pub b: D11, pub c: D11, pub d: D11 }
pub struct D11 { pub a: D12, pub b: D12, pub c: D12, pub d: D12 }
pub struct D12 { pub a: D13, pub b: D13, pub c: D13, pub d: D13 }
pub struct D13 { pub a: D14, pub b: D14, pub c: D14, pub d: D14 }
pub struct D14 { pub a: D15, pub b: D15, pub c: D15, pub d: D15 }
pub struct D15 { pub x: u8 }

pub trait Look {
    fn look_w(&self, w: &W0);
    fn look_v(&self, v: &V0);
    fn look_d(&self, d: &D0);
}

pub fn wide_admitted<L: Look>(l: &L, w: &W0) {
    //[advisory]~^ WARN Trust verification advisory for `shape_walk_node_budget::wide_admitted`: 1 instance
    //[strict]~^^ WARN Trust verification advisory for `shape_walk_node_budget::wide_admitted`: 1 instance
    //[certify]~^^^ ERROR Trust certify verification failed for `shape_walk_node_budget::wide_admitted`: 1 instance
    l.look_w(w)
}

pub fn over_budget_refused<L: Look>(l: &L, v: &V0) {
    //[strict]~^ ERROR Trust Level 0 safety verification incomplete for `shape_walk_node_budget::over_budget_refused`: 1 obligation(s)
    //[strict]~^^ ERROR Trust strict verification failed for `shape_walk_node_budget::over_budget_refused`: 1 obligation(s)
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete for `shape_walk_node_budget::over_budget_refused`: 1 obligation(s)
    //[certify]~^^^^ ERROR Trust strict verification failed for `shape_walk_node_budget::over_budget_refused`: 1 obligation(s)
    l.look_v(v)
}

pub fn over_depth_refused<L: Look>(l: &L, d: &D0) {
    //[strict]~^ ERROR Trust Level 0 safety verification incomplete for `shape_walk_node_budget::over_depth_refused`: 1 obligation(s)
    //[strict]~^^ ERROR Trust strict verification failed for `shape_walk_node_budget::over_depth_refused`: 1 obligation(s)
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete for `shape_walk_node_budget::over_depth_refused`: 1 obligation(s)
    //[certify]~^^^^ ERROR Trust strict verification failed for `shape_walk_node_budget::over_depth_refused`: 1 obligation(s)
    l.look_d(d)
}

pub struct Fine;
pub struct Boom;

impl Look for Fine {
    fn look_w(&self, _w: &W0) {}
    fn look_v(&self, _v: &V0) {}
    fn look_d(&self, _d: &D0) {}
}

impl Look for Boom {
    fn look_w(&self, _w: &W0) {
        //[strict]~^ ERROR Trust Level 0 safety verification incomplete for `<shape_walk_node_budget::Boom as shape_walk_node_budget::Look>::look_w`: 2 obligation(s)
        //[strict]~^^ ERROR Trust strict verification failed for `<shape_walk_node_budget::Boom as shape_walk_node_budget::Look>::look_w`: 2 obligation(s)
        //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete for `<shape_walk_node_budget::Boom as shape_walk_node_budget::Look>::look_w`: 2 obligation(s)
        //[certify]~^^^^ ERROR Trust strict verification failed for `<shape_walk_node_budget::Boom as shape_walk_node_budget::Look>::look_w`: 2 obligation(s)
        panic!("boom")
    }
    fn look_v(&self, _v: &V0) {}
    fn look_d(&self, _d: &D0) {}
}

pub fn use_fine(w: &W0) {
    //~^ NOTE Trust verification: 1 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked, 1 assumed (instance discharge) out of 2 obligation(s)
    // Re-pinned 2026-10-15 (the merge of 2026-10-14, DECISION_QUEUE D103(e)): the call into
    // the bundled `wide_admitted` body carries the counted panic-freedom aggregate, which the
    // native lane left `runtime_checked` and `certify` refused.
    // Re-pinned 2026-11-07: that aggregate was `runtime_checked` only for want of
    // source reference facts. `&Fine` (the promoted borrow of a fieldless struct) now
    // carries a VALUE fact and `&W0` (an all-integer product inside the node bound)
    // parameter facts (`docs/DECISION_QUEUE.md`, 2026-11-07), so it is proved and
    // `certify` accepts `use_fine` exactly as it accepts
    // `discharge_row_per_instance::use_good` (measured A/B:
    // `deep_owned_argument_admitted.rs`).
    wide_admitted(&Fine, w)
}

pub fn use_boom(w: &W0) {
    //[advisory]~^ WARN Trust instance discharge not established for `shape_walk_node_budget::use_boom`: 1 instance(s)
    //[strict]~^^ WARN Trust Level 0 safety verification incomplete for `shape_walk_node_budget::use_boom`: 1 obligation(s)
    //[strict]~^^^ ERROR Trust instance discharge not established for `shape_walk_node_budget::use_boom`: 1 instance(s)
    //[strict]~^^^^ ERROR Trust strict verification failed for `shape_walk_node_budget::use_boom`: 1 obligation(s)
    //[certify]~^^^^^ ERROR Trust Level 0 safety verification incomplete for `shape_walk_node_budget::use_boom`: 1 obligation(s)
    //[certify]~^^^^^^ ERROR Trust instance discharge not established for `shape_walk_node_budget::use_boom`: 1 instance(s)
    //[certify]~^^^^^^^ ERROR Trust strict verification failed for `shape_walk_node_budget::use_boom`: 1 obligation(s)
    wide_admitted(&Boom, w)
}
