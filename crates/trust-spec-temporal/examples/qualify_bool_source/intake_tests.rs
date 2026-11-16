// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! File/codec admission fixtures, not generated source-proof evidence.

use super::*;

fn fixture() -> (Vec<u8>, Suite) {
    use trust_ir::{
        Block, BlockId, Constant, FuncId, FuncTy, FuncTyId, Function, Inst, InstrNode, Module, Ty,
        ValueId,
    };
    let mut module = Module::new("bounded_ir_fixture");
    module.func_types.push(FuncTy {
        params: vec![],
        returns: vec![Ty::Bool],
        is_vararg: false,
        abi: None,
    });
    let mut function = Function::new(FuncId::new(0), "answer", FuncTyId::new(0), BlockId::new(0));
    function.display_path = Some("answer".to_owned());
    function.body_gate = Some(trust_ir::BodyGate::Ungated);
    let mut block = Block::new(BlockId::new(0));
    block.body.push(
        InstrNode::new(Inst::Const { ty: Ty::Bool, value: Constant::Bool(true) })
            .with_result(ValueId::new(0)),
    );
    block.body.push(InstrNode::new(Inst::Return { values: vec![ValueId::new(0)] }));
    function.blocks.push(block);
    module.functions.push(function);
    let suite = Suite {
        function: "answer".to_owned(),
        fuel: 8,
        cases: vec![Case { arguments: vec![], expected: true, permitted: true }],
        mutation_from: "true".to_owned(),
        mutation_to: "false".to_owned(),
    };
    (trust_ir::binary::serialize_module(&module).unwrap(), suite)
}

#[test]
fn sparse_file_above_existing_literal_cap_is_refused_before_decode() {
    assert_eq!(MAX_LITERAL_MODULE_BYTES, 16 * 1024 * 1024);
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("source_qualification.trust-ir.bin");
    fs::File::create(&path).unwrap().set_len(MAX_LITERAL_MODULE_BYTES as u64 + 1).unwrap();
    assert_eq!(fs::metadata(&path).unwrap().len(), MAX_LITERAL_MODULE_BYTES as u64 + 1);
    assert!(read_ir(&path).is_err(), "oversized sparse artifact must never reach the decoder");
}

#[test]
fn memory_decode_guard_matches_the_literal_lane_and_preserves_exact_boundary() {
    let (_, suite) = fixture();
    let mut bytes = vec![0; MAX_LITERAL_MODULE_BYTES + 1];
    let error = function(&bytes, &suite).unwrap_err();
    assert!(
        matches!(error.downcast_ref::<LiteralRefinementError>(), Some(LiteralRefinementError::ModuleTooLarge {bytes: size, maximum}) if *size == bytes.len() && *maximum == MAX_LITERAL_MODULE_BYTES)
    );
    let error = trust_spec_temporal::literal_refinement::certify_literal_refinement(
        &bytes,
        0,
        &LiteralInvocation::closed(vec![], 0),
    )
    .unwrap_err();
    assert!(matches!(
        error,
        LiteralRefinementError::ModuleTooLarge { maximum: MAX_LITERAL_MODULE_BYTES, .. }
    ));
    bytes.pop();
    let directory = tempfile::tempdir().unwrap();
    let exact = directory.path().join("exact-limit.trust-ir.bin");
    fs::File::create(&exact).unwrap().set_len(MAX_LITERAL_MODULE_BYTES as u64).unwrap();
    let admitted = read_ir(&exact).expect("the exact literal limit remains readable");
    assert_eq!(admitted, bytes);
    // Exactly-at-limit malformed data passes the size policy and is still
    // rejected by the codec. Neither call reaches proof preparation.
    let error = function(&bytes, &suite).unwrap_err();
    assert!(error.to_string().contains("compiler artifact decode refused"));
    let error = trust_spec_temporal::literal_refinement::certify_literal_refinement(
        &bytes,
        0,
        &LiteralInvocation::closed(vec![], 0),
    )
    .unwrap_err();
    assert!(matches!(error, LiteralRefinementError::ModuleDecode(_)));
}

#[test]
fn valid_ir_is_preserved_as_owned_bytes_before_function_admission() {
    let (bytes, suite) = fixture();
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("source_qualification.trust-ir.bin");
    fs::write(&path, &bytes).unwrap();
    let owned = read_ir(&path).unwrap();
    assert_eq!(owned, bytes);
    assert_eq!(function(&owned, &suite).unwrap(), 0);
    fs::write(&path, b"replaced after intake").unwrap();
    assert_eq!(
        function(&owned, &suite).unwrap(),
        0,
        "later path changes cannot alter owned input bytes"
    );
    assert!(function(&read_ir(&path).unwrap(), &suite).is_err());
}

#[test]
fn malformed_and_trailing_module_bytes_keep_the_existing_decoder_refusal() {
    let (mut bytes, suite) = fixture();
    bytes.push(0);
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("source_qualification.trust-ir.bin");
    for (invalid, diagnostic) in [
        (bytes, "trailing bytes after canonical module payload"),
        (b"not a TrustIR module".to_vec(), "compiler artifact decode refused"),
    ] {
        fs::write(&path, &invalid).unwrap();
        let owned = read_ir(&path).unwrap();
        assert_eq!(owned, invalid);
        let error = function(&owned, &suite).unwrap_err();
        assert!(error.to_string().contains(diagnostic), "{error}");
    }
}

#[test]
fn required_ir_leaf_is_not_optional_or_followed_through_an_alias() {
    let directory = tempfile::tempdir().unwrap();
    let missing = directory.path().join("missing.trust-ir.bin");
    assert!(read_ir(&missing).is_err());
    let (bytes, _) = fixture();
    let target = directory.path().join("actual.trust-ir.bin");
    fs::write(&target, bytes).unwrap();
    let alias = directory.path().join("source_qualification.trust-ir.bin");
    std::os::unix::fs::symlink(&target, &alias).unwrap();
    assert!(read_ir(&alias).is_err(), "artifact leaves are not canonicalized before admission");
    assert!(read_ir(directory.path()).is_err());
}
