//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@ check-fail

// A sealed trait and verified, exactly refining impl are not enough to mint a
// reusable dynamic-call postcondition through trust-vcgen's public summary
// surface. Until that consumer receives a compiler-sealed, exact evidence
// carrier, the virtual call and its caller must remain unproved.

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

fn use_widget(w: &dyn Widget) -> i32 {
    //~^ WARN Trust Level 0 safety verification incomplete for `sealed_dyn_probe::use_widget`
    //~| ERROR Trust strict verification failed for `sealed_dyn_probe::use_widget`
    w.rank()
}

fn main() {
    //~^ WARN Trust Level 0 safety verification incomplete for `sealed_dyn_probe::main`
    //~| ERROR Trust strict verification failed for `sealed_dyn_probe::main`
    let b = Button;
    let _ = use_widget(&b);
}
