use super::{builtin_codegen_backend, no_trust_evidence_builtin_backend_available};

#[test]
fn dummy_backend_is_resolved_without_external_loading() {
    let backend = builtin_codegen_backend("dummy").expect("dummy builtin")();
    assert_eq!(backend.name(), "dummy");
    assert!(no_trust_evidence_builtin_backend_available("dummy"));
    assert!(!no_trust_evidence_builtin_backend_available("trust-cg"));
    assert!(!no_trust_evidence_builtin_backend_available("/tmp/librustc_codegen_custom.so"));
}

#[cfg(all(feature = "llvm", feature = "trust-cg"))]
#[test]
fn sequential_sessions_resolve_each_requested_builtin_backend() {
    let names = ["llvm", "trust-cg", "llvm", "trust_cg"].map(|requested| {
        builtin_codegen_backend(requested)
            .unwrap_or_else(|| panic!("missing builtin {requested}"))()
        .name()
    });
    assert_eq!(names, ["llvm", "trust-cg", "llvm", "trust-cg"]);
    assert!(no_trust_evidence_builtin_backend_available("llvm"));
}
