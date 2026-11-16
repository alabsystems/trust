use trust_types::{
    BasicBlock, BlockId, LocalDecl, Operand, Place, SourceSpan, Terminator, Ty, UnwindEdge,
    VerifiableBody, VerifiableFunction,
};

use super::semantic_guard::len_call_result_has_isize_bound;

fn len_call(callee: &str, receiver_ty: Ty) -> VerifiableFunction {
    VerifiableFunction {
        name: "len_call".into(),
        def_path: "test::len_call".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::usize(), name: Some("ret".into()) },
                LocalDecl { index: 1, ty: receiver_ty, name: Some("receiver".into()) },
                LocalDecl { index: 2, ty: Ty::usize(), name: Some("len".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        func: callee.into(),
                        args: vec![Operand::Copy(Place::local(1))],
                        dest: Place::local(2),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        callee_identity: None,
                        callee_key: crate::sep_engine::tests::fixture_key(&callee.to_string()),
                        is_foreign: false,
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::usize(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

#[test]
fn len_isize_bound_requires_bytes_or_a_non_zst_slice_element() {
    let chars = len_call(
        "core::slice::<impl [char]>::len",
        Ty::Ref { mutable: false, inner: Box::new(Ty::Slice { elem: Box::new(Ty::Char) }) },
    );
    let Terminator::Call { func: callee, args, .. } = &chars.body.blocks[0].terminator else {
        unreachable!()
    };
    assert!(len_call_result_has_isize_bound(&chars, callee, args));

    let zst = len_call(
        "core::slice::<impl [()]>::len",
        Ty::Ref { mutable: false, inner: Box::new(Ty::Slice { elem: Box::new(Ty::Unit) }) },
    );
    let Terminator::Call { func: callee, args, .. } = &zst.body.blocks[0].terminator else {
        unreachable!()
    };
    assert!(
        !len_call_result_has_isize_bound(&zst, callee, args),
        "a ZST slice may have len > isize::MAX"
    );

    let string = len_call(
        "alloc::string::String::len",
        Ty::Adt {
            arbitrary_precision: None,
            validity_wrapper: None,
            name: "alloc::string::String".into(),
            fields: vec![].into(),
            variants: vec![].into(),
            disc_index_safe: false,
            faithful_enum_repr: None,
            enum_layout: None,
            adt_kind: None,
            layout: None,
        },
    );
    let Terminator::Call { func: callee, args, .. } = &string.body.blocks[0].terminator else {
        unreachable!()
    };
    assert!(len_call_result_has_isize_bound(&string, callee, args));

    let erased_vec = len_call(
        "alloc::vec::Vec::<u8>::len",
        Ty::Adt {
            arbitrary_precision: None,
            validity_wrapper: None,
            name: "alloc::vec::Vec".into(),
            fields: vec![].into(),
            variants: vec![].into(),
            disc_index_safe: false,
            faithful_enum_repr: None,
            enum_layout: None,
            adt_kind: None,
            layout: None,
        },
    );
    let Terminator::Call { func: callee, args, .. } = &erased_vec.body.blocks[0].terminator else {
        unreachable!()
    };
    assert!(
        !len_call_result_has_isize_bound(&erased_vec, callee, args),
        "an erased Vec element cannot exclude Vec<()>"
    );
}
