//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ rustc-env:TRUST_DYN_PROBE=1
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@ check-fail
//~? RAW Liskov router: 1 VC(s), 1 proved, 0 refuted

// The Liskov router, reached and answering. Plan P4 / T4.1 moved its SMT lane
// from a subprocess `ay` to the ay linked into trustc, and this file is what
// runs that lane through the compiler.
//
// `Button::rank` promises MORE than the trait (`result >= 5` against
// `result >= 0`), so the contracts are not identical and
// `all_trait_impls_verified` hands the one covariance VC,
// `Not(result >= 5 => result >= 0)`, to `build_router`. The router must prove
// it: the probe line above is its verdict, printed before the Clean re-check.
// A lane that stops answering (a zero clock, a backend that only says Unknown,
// a dropped slot) prints `0 proved` and fails this file.
//
// What this file does not assert: whether the refinement is ACCEPTED. That
// also needs `trust_certify::certify_vc` to re-derive the VC in the Clean
// kernel, and today Clean declines the `Not(Implies(..))` shape
// `verify_liskov` emits (docs/DECISION_QUEUE.md, T4.1-IMPL-2), so the probe
// goes on to print `fails Liskov refinement` and the dyn summary is not
// minted. Nothing downstream reads that summary's postcondition yet either
// (`trust_sealed_dyn_summary.rs`). When certification lands, this file stays
// green and its twin `sealed_dyn_liskov_router_refutes.rs` keeps the
// refusal direction.
//
// `use_widget` carries no contract, as in `sealed_dyn_probe.rs`, but its
// virtual call is NOT discharged here. C-SEALED discharges a sealed `dyn` call
// only through the minted dyn summary, and the summary is minted only when
// `all_trait_impls_verified` accepts every impl, which T4.1-IMPL-2's Clean
// decline prevents. So the call keeps its fail-closed absent-callee row and the
// file is `check-fail`. MEASURED on the T4.1 stage 1 (2026-10-10): the router
// printed `1 VC(s), 1 proved, 0 refuted`, then `fails Liskov refinement`, and
// `use_widget` was refused. The probe line is this file's assertion; when
// certification lands, `use_widget` passes and this file becomes `check-pass`.

#![feature(contracts_internals)]

mod sealed {
    pub trait Widget {
        fn rank(&self) -> i32
        contract_ensures { move |result| *result >= 0 }
        {
            0
        }
    }
}

use sealed::Widget;

struct Button;
impl Widget for Button {
    fn rank(&self) -> i32
    contract_ensures { move |result| *result >= 5 }
    {
        5
    }
}

fn use_widget(w: &dyn Widget) -> i32 {
    w.rank()
}

fn main() {
    let b = Button;
    let _ = use_widget(&b);
}
