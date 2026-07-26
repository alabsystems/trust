use trust_types::{
    CompilerContractBundle, CompilerProofItem, CompilerProofItemBundle, Contract, ContractKind,
    ProofItemBody, ProofItemKind, ProofItemSignature, ProofItemSource, ProofItemTarget, SourceSpan,
};

#[test]
fn native_proof_fn_is_compiler_owned_and_runtime_erased() {
    let item = CompilerProofItem {
        item_id: "proof:demo::sorted_insert_preserves_sorted".to_string(),
        name: "sorted_insert_preserves_sorted".to_string(),
        kind: ProofItemKind::ProofFn,
        target: ProofItemTarget::Function { def_path: "demo::SortedVec::insert".to_string() },
        signature: ProofItemSignature::default(),
        contracts: CompilerContractBundle::new(vec![Contract {
            kind: ContractKind::Ensures,
            span: SourceSpan::default(),
            body: "result == true".to_string(),
        }]),
        body: ProofItemBody::CompilerOwned {
            body_ref: "hir-body:demo::sorted_insert_preserves_sorted".to_string(),
        },
        source: ProofItemSource::NativeSyntax,
        span: SourceSpan::default(),
        metadata: vec![("trust.proof_item.syntax".to_string(), "proof fn".to_string())],
    };

    assert!(item.is_runtime_erased());

    let bundle = CompilerProofItemBundle::new(vec![item]);
    assert!(!bundle.is_empty());
    assert_eq!(bundle.summary.total, 1);
    assert_eq!(bundle.summary.proof_fns, 1);
    assert_eq!(bundle.summary.lemmas, 0);
    assert_eq!(bundle.summary.unsupported, 0);
}

#[test]
fn proof_item_bundle_round_trips_without_proc_macro_metadata() {
    let bundle = CompilerProofItemBundle::new(vec![CompilerProofItem {
        item_id: "proof:demo::lemma".to_string(),
        name: "lemma".to_string(),
        kind: ProofItemKind::Lemma,
        target: ProofItemTarget::LocalNamespace,
        signature: ProofItemSignature::default(),
        contracts: CompilerContractBundle::default(),
        body: ProofItemBody::Unsupported { reason: "parser slice not wired".to_string() },
        source: ProofItemSource::NativeSyntax,
        span: SourceSpan::default(),
        metadata: Vec::new(),
    }]);

    let json = serde_json::to_string(&bundle).expect("serialize proof item bundle");
    assert!(!json.contains("proc_macro"));

    let decoded: CompilerProofItemBundle =
        serde_json::from_str(&json).expect("deserialize proof item bundle");
    assert_eq!(decoded, bundle);
    assert_eq!(decoded.summary.unsupported, 1);
}
