use std::sync::Arc;

use super::*;

#[test]
fn compiler_owned_identity_refuses_equal_module_clones_and_other_function_ids() {
    // Private identity construction is available only to its mint and this child
    // unit module; ordinary source/native work item callers cannot forge one.
    let source = Arc::new(Module::new("source_image"));
    let identity =
        ClosureOnceAdapterIdentity { source: Arc::clone(&source), function: FuncId::new(7) };
    let shared = Arc::clone(&source);
    assert!(identity.matches(&shared, FuncId::new(7)));
    let equal_clone = (*source).clone();
    assert_eq!(equal_clone, *source);
    assert!(!identity.matches(&equal_clone, FuncId::new(7)));
    assert!(!identity.matches(&source, FuncId::new(0)));
    assert!(!identity.matches(&source, FuncId::new(8)));
}
