use super::*;
use std::cell::{Cell, RefCell};

#[test]
fn stop_during_final_binding_refuses_before_any_selection_mutation() {
    let stopped = Cell::new(false);
    let events = RefCell::new(Vec::new());
    let accepted = binding_finishes_current(
        || { events.borrow_mut().push("poll"); !stopped.get() },
        || {
            events.borrow_mut().push("binding");
            stopped.set(true);
            true // Binding success is DATA here, not a kernel token.
        },
    );
    assert!(!accepted, "a stop reached during binding cannot select output");
    assert_eq!(*events.borrow(), ["poll", "binding", "poll"]);
    let mut invoked = false;
    assert!(!binding_finishes_current(|| false, || { invoked = true; true }));
    assert!(!invoked, "an already stopped scope must not hash the artifact");
    assert!(binding_finishes_current(|| true, || true));
    assert!(!binding_finishes_current(|| true, || false));
    // This checks the production bracket's ordering only. It constructs
    // no CheckedPresentation or native eligibility and proves no program.
}
