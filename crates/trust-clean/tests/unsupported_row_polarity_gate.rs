//! An `UnsupportedMir` row means "I do not know". The kernel-certification gate
//! must never read one as a discharge.
//!
//! # The defect this pins
//!
//! `whole_program::{certify_callee_summary → ensures_certified_modulo_3,
//! certify_function_in_graph}` select the obligations they kernel-check by
//! `vc.kind.proof_level() == ProofLevel::L0Safety` and hand `vc.formula`
//! straight to `vc_refute::check_refute_vc`, treating `RefutedModulo3` as
//! discharged. `VcKind::UnsupportedMir` IS `L0Safety`, so a declined row is
//! checked like any other — and a VC is a VIOLATION formula, so an UNSAT one
//! reads as "no violation".
//!
//! `trust_vcgen`'s `panic_calls` soft-len arm used to build its declined slice
//! row with `Formula::Bool(false)`. Measured on this fixture at that commit:
//!
//! ```text
//! discharged=true  kind=UnsupportedMir { kind: "SliceBoundsCheck", .. }  formula=Bool(false)
//! discharged=true  kind=Postcondition
//! certify_callee_summary().proved = true   registry = Certified, assumable
//! ```
//!
//! — a function that panics at `end > v.len()` certified as kernel-checked L0
//! safe, and thereby assumable by every caller. Every other `UnsupportedMir`
//! emitter in `trust-vcgen` already used the SAT `Bool(true)`; that one did not.
//!
//! # Why the fixture is shaped this way
//!
//! The `ensures result < 8` clause discharges, so the declined safety row is the
//! ONLY thing the verdict turns on. Without a contract the gate refuses for an
//! unrelated reason ("no `#[ensures]` contract to certify") and the test would
//! pass while measuring nothing — `the_gate_certifies_when_the_declined_row_is_absent`
//! below is the control that separates the two.
//!
//! # What each test kills
//!
//! There are now TWO independent defences, and the tests separate them:
//!
//! * `the_declined_row_reaches_the_gates_l0_filter` fails if the emitter's
//!   violation formula goes back to `Bool(false)`, or if the row stops being
//!   emitted at all.
//! * `a_declined_row_does_not_certify_the_function` fails if the row stops being
//!   emitted, and — with `whole_program`'s `is_declined_vc_kind_pub` clause
//!   removed — if the formula goes back to `Bool(false)`. With that kind guard
//!   in place it passes under the formula regression alone, which is the point
//!   of the guard: it is what makes the verdict independent of the formula.
//! * `the_gate_certifies_when_the_declined_row_is_absent` fails if either
//!   defence over-fires and the gate stops certifying anything.
use std::path::Path;

use trust_types::{ProofLevel, VcKind, VerifiableFunction};

/// Real extracted MIR carries deep recursive `Formula` walks; the libtest
/// default 2 MiB stack is not enough for the generation + kernel pass.
const SOLVER_STACK_BYTES: usize = 64 * 1024 * 1024;

fn load(file: &str) -> VerifiableFunction {
    let path =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("fixtures/unsupported-row-polarity").join(file);
    let text = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("fixture {} must be readable: {e}", path.display()));
    serde_json::from_str(&text)
        .unwrap_or_else(|e| panic!("fixture {} must deserialize: {e}", path.display()))
}

fn on_analysis_thread<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .stack_size(SOLVER_STACK_BYTES)
        .spawn(f)
        .expect("spawn analysis thread")
        .join()
        .expect("analysis thread must not panic")
}

fn certify(func: VerifiableFunction) -> bool {
    on_analysis_thread(move || {
        let mut registry = trust_clean::ProofStatusRegistry::new();
        let summary =
            trust_clean::certify_callee_summary(&func, trust_ir::FuncId::new(0), &mut registry);
        let proved = summary.ir_summary.proved;
        // The two readings of "certified" must agree: the summary flag a caller
        // consumes, and the registry capability that makes the callee assumable.
        assert_eq!(
            proved,
            registry.is_assumable(&func.def_path),
            "summary.proved and registry assumability must not disagree"
        );
        proved
    })
}

/// THE soundness pin. `vec_range_index_with_ensures` panics for every
/// `end > v.len()`, and its bounds obligation is DECLINED, so the kernel gate
/// has nothing on which to certify it.
#[test]
fn a_declined_row_does_not_certify_the_function() {
    assert!(
        !certify(load("vec_range_index_with_ensures.json")),
        "a function whose only safety obligation was DECLINED must not be kernel-certified; \
         this fixture panics at `end > v.len()`"
    );
}

/// The declined row really is present and really is selected by the gate's
/// `L0Safety` filter — without this the test above could pass because the row
/// never reached the gate at all, which would make it inert.
#[test]
fn the_declined_row_reaches_the_gates_l0_filter() {
    let func = load("vec_range_index_with_ensures.json");
    let (declined, saw_postcondition) = on_analysis_thread(move || {
        let vcs = trust_vcgen::generate_vcs(&func);
        let declined: Vec<_> = vcs
            .iter()
            .filter(|vc| vc.kind.proof_level() == ProofLevel::L0Safety)
            .filter_map(|vc| match &vc.kind {
                VcKind::UnsupportedMir { kind, .. } => Some((kind.clone(), vc.formula.clone())),
                _ => None,
            })
            .collect();
        let saw_post = vcs.iter().any(|vc| matches!(&vc.kind, VcKind::Postcondition));
        (declined, saw_post)
    });
    assert_eq!(
        declined.len(),
        1,
        "expected exactly one declined L0 row on this fixture; got {declined:?}"
    );
    assert_eq!(declined[0].0, "SliceBoundsCheck");
    assert_eq!(
        declined[0].1,
        trust_types::Formula::Bool(true),
        "a declined row's VIOLATION formula must be SAT; `Bool(false)` is UNSAT and this gate \
         reads UNSAT as DISCHARGED"
    );
    assert!(
        saw_postcondition,
        "the fixture must emit a Postcondition VC or the gate refuses for an unrelated reason"
    );
}

/// CONTROL: the same contract on a body with no declined row DOES certify. This
/// is what makes the pin above a statement about the declined row rather than
/// about the gate refusing everything.
#[test]
fn the_gate_certifies_when_the_declined_row_is_absent() {
    let control = load("const_return_with_ensures.json");
    let has_declined_row = on_analysis_thread({
        let control = control.clone();
        move || {
            trust_vcgen::generate_vcs(&control)
                .iter()
                .any(|vc| matches!(&vc.kind, VcKind::UnsupportedMir { .. }))
        }
    });
    assert!(!has_declined_row, "the control must have no declined row, or it controls nothing");
    assert!(
        certify(control),
        "the control body carries the SAME `ensures result < 8` and no declined row, so the \
         gate must still certify it — otherwise the pin above measures nothing"
    );
}
