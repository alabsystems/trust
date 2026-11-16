// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Synthetic wire/refusal controls, not compiler-layout or execution evidence.

use super::*;
use crate::test_utils::*;
use crate::{AggregateKind, BinOp, BlockId, Place, SourceSpan, UnOp, UnwindEdge};

fn full_image() -> ConstantMemoryImage {
    let ConstValue::MemoryImage(image) = make_memory_image_constant(8) else {
        panic!("fixture image");
    };
    let mut image = *image;
    image.root = ConstantImageRoot::Pointer(ConstantImagePointer {
        allocation_id: 1,
        offset_bytes: 0,
        immutable: false,
        shared_ref: true,
    });
    let mut bytes = vec![None; 48];
    bytes[..16].fill(Some(0));
    bytes[0] = Some(3);
    image.nodes.insert(
        1,
        ConstantImageNode::Static {
            definition: ConstantImageDefinition {
                def_path: "fixture::NAME".into(),
                def_path_hash: CallableDefPathHash::new(1, 10),
            },
            declared_mutable: false,
            freeze: false,
            thread_local: false,
            foreign: false,
            initializer: ConstantImageMemory {
                layout: ConstantImageLayout { size_bytes: 48, align_bytes: 8 },
                mutable: true,
                bytes,
                relocations: vec![ConstantImageRelocation {
                    offset_bytes: 8,
                    pointer: ConstantImagePointer {
                        allocation_id: 2,
                        offset_bytes: 0,
                        immutable: true,
                        shared_ref: false,
                    },
                }],
            },
        },
    );
    image.nodes.insert(
        2,
        ConstantImageNode::Function {
            definition: ConstantImageDefinition {
                def_path: "fixture::initializer".into(),
                def_path_hash: CallableDefPathHash::new(1, 11),
            },
            instance_fingerprint: [u64::MAX, u64::MAX - 1],
            instance_debug: "synthetic call-once shim".into(),
            callee_identity: CalleeIdentity {
                stable_crate_id: 1,
                def_index: 11,
                substs_digest: [u64::MAX - 2, 7],
            },
        },
    );
    image
}

#[test]
fn memory_image_json_and_binary_round_trip_preserve_complete_graph() {
    let image = full_image();
    let json = serde_json::to_vec(&image).expect("image JSON");
    let decoded: ConstantMemoryImage = serde_json::from_slice(&json).expect("decode JSON");
    assert_eq!(image, decoded);
    let binary = bincode::serialize(&image).expect("image binary");
    let decoded: ConstantMemoryImage = bincode::deserialize(&binary).expect("decode binary");
    assert_eq!(image, decoded);
    let tagged = ConstValue::MemoryImage(Box::new(image));
    let binary = bincode::serialize(&tagged).expect("tagged binary");
    assert_eq!(&binary[..4], &13_u32.to_le_bytes(), "append-only discriminant");
    let restored: ConstValue = bincode::deserialize(&binary).expect("tagged decode");
    assert_eq!(serde_json::to_value(tagged).unwrap(), serde_json::to_value(restored).unwrap());
    let old = ConstValue::struct_scalar_fields_ref("old", vec![]);
    assert_eq!(&bincode::serialize(&old).unwrap()[..4], &12_u32.to_le_bytes());
}

#[test]
fn memory_image_identity_layout_mask_and_provenance_change_serialized_commitment() {
    let original = full_image();
    let baseline = serde_json::to_vec(&original).unwrap();
    let mut changes = Vec::new();
    let mut changed = original.clone();
    changed.owner.def_path_hash = CallableDefPathHash::new(2, 2);
    changes.push(changed);
    let mut changed = original.clone();
    changed.target.little_endian = false;
    changes.push(changed);
    let mut changed = original.clone();
    changed.target.pointer_size_bytes = 4;
    changes.push(changed);
    let mut changed = original.clone();
    changed.ty_fingerprint[1] ^= 1;
    changes.push(changed);
    let mut changed = original.clone();
    let ConstantImageRoot::Pointer(pointer) = &mut changed.root else { panic!("pointer") };
    pointer.allocation_id = 9;
    changes.push(changed);
    for field in 0..5 {
        let mut changed = original.clone();
        let ConstantImageNode::Static { initializer, .. } = changed.nodes.get_mut(&1).unwrap()
        else {
            panic!("static")
        };
        match field {
            0 => initializer.bytes[16] = Some(0),
            1 => initializer.relocations[0].pointer.offset_bytes = 8,
            2 => initializer.relocations[0].pointer.allocation_id = 1,
            3 => initializer.relocations[0].pointer.immutable = false,
            4 => initializer.relocations[0].pointer.shared_ref = true,
            _ => unreachable!(),
        }
        changes.push(changed);
    }
    for changed in changes {
        assert_ne!(baseline, serde_json::to_vec(&changed).unwrap());
    }
}

#[test]
fn memory_image_equal_bytes_do_not_merge_allocation_identity_or_pointer_bits() {
    let mut image = full_image();
    let mut bytes = vec![Some(0); 16];
    bytes[8] = Some(8);
    let memory = ConstantImageNode::Memory(ConstantImageMemory {
        layout: ConstantImageLayout { size_bytes: 16, align_bytes: 8 },
        mutable: false,
        bytes,
        relocations: vec![],
    });
    image.nodes.insert(3, memory.clone());
    image.nodes.insert(4, memory);
    image.root = ConstantImageRoot::Indirect { allocation_id: 3, offset_bytes: 0 };
    let first = serde_json::to_vec(&image).unwrap();
    image.root = ConstantImageRoot::Indirect { allocation_id: 4, offset_bytes: 0 };
    assert_ne!(first, serde_json::to_vec(&image).unwrap());
    assert_eq!(image.nodes[&3], image.nodes[&4], "same bytes, distinct nodes remain");
    assert_ne!(
        serde_json::to_vec(&make_memory_image_constant(0)).unwrap(),
        serde_json::to_vec(&make_memory_image_constant(8)).unwrap(),
    );
}

#[test]
fn memory_image_equality_and_opaque_reference_classification_never_infer_values() {
    let image = make_memory_image_constant(8);
    let nested = ConstValue::struct_scalar_fields_ref(
        "malformed external carrier",
        vec![ConstValue::Int(9), image.clone()],
    );
    for value in [&image, &nested] {
        assert!(value.contains_memory_image());
        assert!(!value.is_opaque_reference());
        for other in [&image, &nested, &ConstValue::Int(8), &make_memory_image_constant(0)] {
            assert_eq!(crate::static_truth::const_eq_truth(value, other), None);
            assert_eq!(crate::static_truth::const_eq_truth(other, value), None);
        }
    }
    assert!(!ConstValue::Int(8).contains_memory_image());
    assert!(ConstValue::opaque_const().is_opaque_reference());
}

#[test]
fn memory_image_body_scan_sees_every_rvalue_shape_and_dead_blocks() {
    let image = Operand::Constant(make_memory_image_constant(8));
    let zero = Operand::Constant(ConstValue::Int(0));
    let rvalues = [
        Rvalue::Use(image.clone()),
        Rvalue::UnaryOp(UnOp::Not, image.clone()),
        Rvalue::Cast(image.clone(), Ty::Bool),
        Rvalue::Repeat(image.clone(), 0),
        Rvalue::BinaryOp(BinOp::Eq, zero.clone(), image.clone()),
        Rvalue::CheckedBinaryOp(BinOp::Add, image.clone(), zero.clone()),
        Rvalue::UncheckedBinaryOp(BinOp::Add, zero.clone(), image.clone()),
        Rvalue::Aggregate(AggregateKind::Tuple, vec![zero.clone(), image.clone()]),
        Rvalue::PtrOffset { ptr: zero, count: image.clone() },
        Rvalue::Unsupported { kind: "test".into(), detail: "test".into(), operands: vec![image] },
    ];
    for rvalue in rvalues {
        assert!(rvalue.contains_memory_image());
        let stmt = make_assign(Place::local(0), rvalue);
        assert!(stmt.contains_memory_image());
        let body = make_simple_body(
            vec![],
            vec![
                make_basic_block(0, vec![], Terminator::Return),
                make_basic_block(1, vec![stmt], Terminator::Return),
            ],
        );
        assert!(body.contains_memory_image(), "unreachable blocks remain scanned");
    }
}

#[test]
fn memory_image_statement_and_terminator_scan_includes_nested_carriers() {
    let image = Operand::Constant(ConstValue::struct_scalar_fields_ref(
        "outer",
        vec![make_memory_image_constant(8)],
    ));
    let zero = Operand::Constant(ConstValue::Int(0));
    for stmt in [
        Statement::Intrinsic { name: "test".into(), args: vec![image.clone()] },
        Statement::CopyNonOverlapping {
            src: zero.clone(),
            dst: zero,
            count: image.clone(),
            elem_ty: Ty::u8(),
            span: SourceSpan::default(),
        },
        Statement::Unsupported {
            kind: "test".into(),
            detail: "test".into(),
            operands: vec![image.clone()],
            span: SourceSpan::default(),
        },
    ] {
        assert!(stmt.contains_memory_image());
    }
    assert!(
        Terminator::Assert {
            cond: image.clone(),
            expected: true,
            msg: AssertMessage::BoundsCheck,
            target: BlockId(1),
            span: SourceSpan::default(),
            unwind: UnwindEdge::Unreachable
        }
        .contains_memory_image()
    );
    assert!(
        Terminator::SwitchInt {
            discr: image,
            targets: vec![],
            otherwise: BlockId(1),
            exhaustive_enum_unreachable: false,
            span: SourceSpan::default()
        }
        .contains_memory_image()
    );
    assert!(!Statement::Nop.contains_memory_image());
    assert!(!Terminator::Return.contains_memory_image());
    assert!(!make_simple_body(vec![], vec![]).contains_memory_image());
}

#[test]
fn opaque_scalar_body_scan_sees_every_shape_nested_carriers_and_rejects_string_lookalikes() {
    let opaque = Operand::Constant(ConstValue::opaque_scalar(64, false));
    let nested = Operand::Constant(ConstValue::struct_scalar_fields_ref(
        "outer",
        vec![ConstValue::Int(0), ConstValue::opaque_scalar(32, true)],
    ));
    let zero = Operand::Constant(ConstValue::Int(0));
    let lookalike_str = Operand::Constant(ConstValue::Str { bytes: b"OpaqueScalar".to_vec() });
    assert!(!lookalike_str.contains_opaque_scalar());
    assert!(!Operand::Constant(make_memory_image_constant(8)).contains_opaque_scalar());
    assert!(!Operand::Constant(ConstValue::opaque_const()).contains_opaque_scalar());

    for rvalue in [
        Rvalue::Use(opaque.clone()),
        Rvalue::UnaryOp(UnOp::Not, nested.clone()),
        Rvalue::Cast(opaque.clone(), Ty::Bool),
        Rvalue::Repeat(opaque.clone(), 1),
        Rvalue::BinaryOp(BinOp::Eq, zero.clone(), opaque.clone()),
        Rvalue::CheckedBinaryOp(BinOp::Add, opaque.clone(), zero.clone()),
        Rvalue::UncheckedBinaryOp(BinOp::Add, zero.clone(), nested.clone()),
        Rvalue::Aggregate(AggregateKind::Tuple, vec![zero.clone(), opaque.clone()]),
        Rvalue::PtrOffset { ptr: zero.clone(), count: opaque.clone() },
        Rvalue::Unsupported {
            kind: "test".into(),
            detail: "test".into(),
            operands: vec![opaque.clone()],
        },
    ] {
        assert!(rvalue.contains_opaque_scalar());
        let stmt = make_assign(Place::local(0), rvalue);
        assert!(stmt.contains_opaque_scalar());
        let body = make_simple_body(
            vec![],
            vec![
                make_basic_block(0, vec![], Terminator::Return),
                make_basic_block(1, vec![stmt], Terminator::Return),
            ],
        );
        assert!(body.contains_opaque_scalar(), "unreachable blocks remain scanned");
    }

    let lookalike_body = make_simple_body(
        vec![],
        vec![make_basic_block(
            0,
            vec![make_assign(Place::local(0), Rvalue::Use(lookalike_str))],
            Terminator::Return,
        )],
    );
    assert!(!lookalike_body.contains_opaque_scalar());
}
