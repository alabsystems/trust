//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@ check-fail

// Discriminating test for the sealed-trait `dyn Trait` dispatch summary.
//
// `use_widget` carries a postcondition (`result >= 0`) that would require
// reasoning through the virtual call `w.rank()`. The compiler can establish
// closed-world sealedness and exact impl/trait refinement, but trust-vcgen's
// reusable-postcondition consumer deliberately accepts only a private sealed
// evidence carrier; production has no such minter yet. The call result is
// therefore havoced and the strict lane must fail closed.

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
    contract_ensures { move |result| *result >= 0 }
    {
        5
    }
}

fn use_widget(w: &dyn Widget) -> i32
//~^ WARN Trust Level 0 safety verification incomplete for `trust_sealed_dyn_summary::use_widget`
//~| ERROR Trust strict verification failed for `trust_sealed_dyn_summary::use_widget`
contract_ensures { move |result| *result >= 0 }
{
    w.rank()
}

fn main() {
    //~^ WARN Trust Level 0 safety verification incomplete for `trust_sealed_dyn_summary::main`
    //~| ERROR Trust strict verification failed for `trust_sealed_dyn_summary::main`
    let b = Button;
    let _ = use_widget(&b);
}
