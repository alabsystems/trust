//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@ check-fail

// ZERO-ROW-GATE AMENDMENT (2026-10-10, docs/DECISION_QUEUE.md ZERO-ROW-GATE): this file is now check-fail.
// `use_widget`'s C-SEALED discharge leaves it with zero obligations (the pinned NOTE),
// but the certificate is in no authenticated registry, so the body publishes an
// `unknown` row and is refused. "If this file went red the discharge broke" below now
// reads: the discharge broke if `use_widget` loses that NOTE (an obligation appeared)
// or if ANY other body errs, `main`'s C-FLOW discharge included. Every ERROR in this
// file is required, so an error on `main` fails the test.
//
// SAFETY ONLY — the positive half of a pair, re-aimed 2026-09-19.
//
// This file used to be check-fail, and what it actually measured was the
// PANIC-FREEDOM row on `use_widget`'s virtual call: it carries no `ensures`, so
// the "reusable dynamic-call postcondition" its old header talked about was
// never on this function at all. That row is now discharged by C-SEALED — the
// trait is local and this is a whole-program artifact, so the impl set is
// `{Button}` and `Button::rank` carries its own verdict.
//
// Its twin `trust_sealed_dyn_summary.rs` IS the postcondition test: byte-identical
// plus `contract_ensures { result >= 0 }` on `use_widget`, and it still FAILS.
// The pair is the assertion that matters about all three dyn certificates:
// they discharge panic freedom and mint no fact about the RESULT, which stays
// havoced. If this file went red the discharge broke; if its twin went GREEN a
// certificate started claiming a postcondition it never proved, which is the
// worse direction.
//
// The R43 `InstanceKind::Item` pin this file used to carry (a virtual call must
// not be granted off the trait DEFAULT's registry entry, closed 2026-09-14) now
// lives solely in `dyn_default_method_proof_does_not_cover_impl.rs`, whose impl
// PANICS and which no certificate can discharge.

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

// ZERO-ROW-GATE (2026-10-10): zero bridged obligations plus a call no authenticated registry discharges publish an `unknown` row; refused.
//~vv ERROR Trust strict verification failed for `sealed_dyn_probe::use_widget`
//~v NOTE this function has no obligation of its own
fn use_widget(w: &dyn Widget) -> i32 {
    w.rank()
}

fn main() {
    // `main` discharges through C-FLOW (its receiver is concretely `Button`,
    // so the coercion enumeration is exactly one target). `use_widget`'s
    // receiver is an opaque `&dyn Widget` that poisons the trait for C-FLOW,
    // and it is reached by C-SEALED instead — two certificates, two arguments,
    // one program.
    let b = Button;
    let _ = use_widget(&b);
}
