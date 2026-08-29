//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//! Regression for the `library/core` STEP-ZERO blocker: the trust-ir producer's
//! `eval_static_initializer` query cycle (E0391). Sibling of
//! `trust_ir_lower_self_referential_static_no_cycle.rs` — same call site, same
//! failure class, but two shapes the `LOWERING_BODIES` reentrancy stack that
//! test pins CANNOT see. Every shape below is a hard `error[E0391]` before the
//! fix and compiles after it; vanilla rustc compiles all of them.
//!
//! Measured cause. `lower_static_ref` read a static's value eagerly with
//! `tcx.eval_static_initializer` from inside `mir_built`. That query demands
//! `mir_for_ctfe` -> `mir_borrowck` of the static, plus CTFE of its
//! initializer — so its demanded-`mir_built` set is the initializer's whole
//! CTFE REACHABILITY SET, not "the initializer body" and not "that body's
//! descendants". The stack only holds the defs the producer is itself
//! lowering, so it catches neither shape:
//!
//!   NESTED. `mir_borrowck(S)` descends into every closure / const block in
//!   S's initializer and demands THEIR `mir_built`. The producer frame is then
//!   `S::{closure#0}` and `S` is nowhere on the stack. This is verbatim
//!   `core::task::wake`: `Waker::from_fn_ptr` (wake.rs:596) and
//!   `LocalWaker::from_fn_ptr` (:913) each build a `RawWakerVTable` whose
//!   `clone` closure holds `&VTABLE`. Those two `#[unstable]` functions made
//!   the whole of `library/core` a hard E0391 with ZERO obligations evaluated,
//!   and `trust.toml` cannot narrow scope
//!   (docs/design/2026-08-20-core-slice-blocker-histogram.md work item 0).
//!
//!   NO NESTING AT ALL. CTFE of S's initializer calls const fns, each demanding
//!   its own `mir_built`. Two sibling module-level items with no ancestry
//!   between them cycle just as well — which is why no ancestor/def-path rule
//!   could be complete either.
//!
//! The fix is LOCALITY, the rule this call site's own siblings already follow
//! (`eval_nonlocal_scalar_const`, `lower_named_const`,
//! `lower_composite_named_const` all refuse to CTFE a LOCAL def from inside
//! `mir_built`): a local static declines with a precise `unsupported` tag —
//! a recorded coverage gap, a hard error under `-Ztrust-ir-lower=strict`,
//! refused by the flip registry and by both differentials, never a value. A
//! NON-local static keeps its eager read and cannot cycle: its provider is the
//! metadata decoder, which returns an already-computed `ConstAllocation`.

// ---------------------------------------------------------------- shape 1
// NESTED: `core::task::wake`'s `RawWakerVTable`, reduced. The `&VTABLE` lives
// in a CLOSURE inside VTABLE's own initializer, so the producer frame that
// reaches it is `{closure#0}` and the reentrancy stack never sees `VTABLE`.
pub struct VT {
    pub clone: unsafe fn(*const ()) -> RW,
}

#[derive(Copy, Clone)]
pub struct RW {
    pub data: *const (),
    pub vtable: &'static VT,
}

impl RW {
    pub const fn new(data: *const (), vtable: &'static VT) -> RW {
        RW { data, vtable }
    }
}

impl VT {
    pub const fn new(clone: unsafe fn(*const ()) -> RW) -> Self {
        VT { clone }
    }
}

pub const fn from_fn_ptr(f: fn()) -> RW {
    static VTABLE: VT = VT::new(|this| RW::new(this, &VTABLE));
    RW::new(f as *const (), &VTABLE)
}

// ---------------------------------------------------------------- shape 2
// NESTED, DEPTH 2: the demanded body is a closure inside a closure. Pins that
// the rule is not "the immediate child of the static".
pub struct Holder {
    pub f: fn() -> *const Holder,
}
pub static H: Holder = Holder {
    f: || {
        let c = || &H as *const Holder;
        c()
    },
};

// ---------------------------------------------------------------- shape 3
// NO NESTING: `S` and `g` are siblings; neither is an ancestor of the other.
// `eval_static_initializer(S)` CTFE-calls `g`, demanding `mir_built(g)`, and
// the producer frame lowering `g` reaches `&S`.
pub static S: u32 = g();
pub const fn g() -> u32 {
    let _p: *const u32 = &S;
    7
}

// ---------------------------------------------------------------- shape 4
// THE CONST TWIN, and a different crate entirely. Nothing here is a `static`:
// `NOOP` is an assoc const whose value holds `&VTABLE`, and `VTABLE` is a const
// whose closure names `RW::NOOP`. The producer's THIR lane never touches it —
// its const legs already defer every LOCAL const — but the `mir_built` hook also
// extracts the MIR-side ORACLE through `trust-mir-extract`, and
// `const_operand_value` there force-evaluated any `Const::Unevaluated` operand
// with no notion of who was calling. `const_eval_global_id_for_typeck(NOOP)`
// demands `mir_for_ctfe(NOOP)` -> `mir_borrowck` -> the nested closure's
// `mir_built`, closing the cycle. This is `core::task::wake`'s `RawWaker::NOOP`
// (wake.rs:61) and it was the LAST of the three `library/core` cycles.
//
// The fix is `trust_mir_extract::ctfe_reentrancy`, a thread-local freeze entered
// once at the `mir_built` seam: the hazard is a property of the CALLER, since the
// same extractor is shared with the verifier at `optimized_mir` time where
// forcing CTFE is safe and load-bearing. Frozen, the operand stays opaque —
// the extractor's existing "value unavailable" answer.
pub struct VT2 {
    pub clone: fn(*const ()) -> RW2,
}
#[derive(Copy, Clone)]
pub struct RW2 {
    pub data: *const (),
    pub vtable: &'static VT2,
}
impl RW2 {
    pub const NOOP: RW2 = {
        const VTABLE: VT2 = VT2 { clone: |_| RW2::NOOP };
        RW2 { data: core::ptr::null(), vtable: &VTABLE }
    };
}

// ---------------------------------------------------------------- control
// A plain local static still COMPILES (it now declines in the producer with
// `StaticRef(local static: CTFE deferral not implemented)` — a recorded
// coverage gap, not an error). Recovering its value model is the deferral
// follow-up named at the call site.
pub static PLAIN: u64 = 7;
pub fn read_plain() -> u64 {
    PLAIN
}

fn main() {}
