//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ rustc-env:TRUST_DYN_PROBE=1
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@ check-fail
//~? RAW Liskov router: 1 VC(s), 0 proved, 1 refuted
//~? RAW fails Liskov refinement
//@ forbid-output: all_trait_impls_verified=true

// The refusal twin of `sealed_dyn_liskov_router_proves.rs`: the same sealed
// trait, but `Button::rank` promises something the trait's `result >= 0`
// does not follow from (`result <= 10`). Its body returns 5, so the override
// verifies on its own and the check reaches the Liskov router (plan P4 /
// T4.1: the ay linked into trustc). The router must REFUTE the covariance VC
// (`result = -1` satisfies `result <= 10` and violates `result >= 0`), and
// `all_trait_impls_verified` must refuse the impl set, so no dyn summary for
// `rank` is minted. If this file went green on the `all_trait_impls_verified`
// line, a refinement the trait does not admit would have been accepted.
// With no summary, `use_widget`'s virtual call keeps its fail-closed row and
// the file is `check-fail` (MEASURED on the T4.1 stage 1, 2026-10-10); the
// probe lines are its assertion.

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
    contract_ensures { move |result| *result <= 10 }
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
