//! Model-level range bounds for empty, wide, borrowed and owning accesses.
//! These fixtures exercise the separation engine, not compiler proof authority.

use trust_types::{BasicBlock, LocalDecl};

use super::tests::{as_slice_buf_fixture, fixture_key, negative_offset_from_raw_parts_fixture};
use super::*;

fn empty_span() -> SourceSpan {
    SourceSpan::default()
}

#[test]
fn wrapping_offset_from_raw_parts_checks_both_bounds() {
    use crate::abstract_interp::discharge::try_eval_boolean;
    use crate::abstract_interp::{AbstractDomain, IntervalDomain};

    let mut mismatches = Vec::new();
    for (offset, len, violates) in [
        (-100, 1, true),
        (-1, 1, true),
        (0, 1, false),
        (63, 1, false),
        (64, 1, true),
        (65, 1, true),
        (0, 64, false),
        (1, 64, true),
        (-100, 0, false),
        (64, 0, false),
        (100, 0, false),
    ] {
        let mut function = negative_offset_from_raw_parts_fixture();
        let Terminator::Call { func, callee_key, args, .. } =
            &mut function.body.blocks[0].terminator
        else {
            panic!("fixture must offset the pointer first");
        };
        *func = "core::ptr::const_ptr::<impl *const u8>::wrapping_offset".into();
        *callee_key = fixture_key(func);
        args[1] = Operand::Constant(trust_types::ConstValue::Int(offset));
        let Terminator::Call { args, .. } = &mut function.body.blocks[1].terminator else {
            panic!("fixture must construct the slice second");
        };
        args[1] = Operand::Constant(trust_types::ConstValue::Int(len));
        let vcs = check_sep_unsafe(&function);
        assert!(
            !vcs.iter().any(|vc| matches!(&vc.kind, VcKind::Assertion { message }
            if message.contains("[unsafe:sep:offset]"))),
            "safe wrapping offset must mint no in-bounds row"
        );
        let bounds: Vec<_> = vcs
            .iter()
            .filter(|vc| {
                matches!(&vc.kind,
            VcKind::CopyBoundsViolation { callee, .. } if callee.contains("from_raw_parts"))
            })
            .collect();
        assert_eq!(bounds.len(), 1, "the slice access must retain its own bounds obligation");
        let result = try_eval_boolean(&bounds[0].formula, &IntervalDomain::top());
        if result != Some(violates) {
            mismatches.push((offset, len, violates, result, bounds[0].formula.clone()));
        }
    }
    assert!(mismatches.is_empty(), "incorrect access bounds: {mismatches:#?}");
}

fn wrapping_access_fixture(offset: i128, len: i128) -> VerifiableFunction {
    let mut function = negative_offset_from_raw_parts_fixture();
    let Terminator::Call { func, callee_key, args, .. } = &mut function.body.blocks[0].terminator
    else {
        panic!("offset fixture")
    };
    *func = "core::ptr::const_ptr::<impl *const u8>::wrapping_offset".into();
    *callee_key = fixture_key(func);
    args[1] = Operand::Constant(trust_types::ConstValue::Int(offset));
    let Terminator::Call { args, .. } = &mut function.body.blocks[1].terminator else {
        panic!("access fixture")
    };
    args[1] = Operand::Constant(trust_types::ConstValue::Int(len));
    function
}

fn assert_concrete_access_bounds(vcs: &[VerificationCondition], expected: &[(&str, bool)]) {
    use crate::abstract_interp::discharge::try_eval_boolean;
    use crate::abstract_interp::{AbstractDomain, IntervalDomain};
    assert!(
        !vcs.iter().any(|vc| matches!(&vc.kind, VcKind::Assertion { message }
        if message.contains("[unsafe:sep:offset]"))),
        "safe wrapping offset must not provide an earlier bounds refusal"
    );
    let bounds: Vec<_> = vcs
        .iter()
        .filter_map(|vc| match &vc.kind {
            VcKind::CopyBoundsViolation { direction, .. } => {
                Some((direction.as_str(), &vc.formula))
            }
            _ => None,
        })
        .collect();
    assert_eq!(bounds.len(), expected.len(), "access must retain every bounds row");
    for &(direction, violates) in expected {
        let matching: Vec<_> = bounds.iter().filter(|(d, _)| *d == direction).collect();
        assert_eq!(matching.len(), 1);
        assert_eq!(
            try_eval_boolean(matching[0].1, &IntervalDomain::top()),
            Some(violates),
            "incorrect {direction} access bounds: {:?}",
            matching[0].1
        );
    }
}

#[test]
fn wrapping_offset_raw_reads_and_writes_check_both_bounds() {
    for callee in [
        "core::ptr::read",
        "core::ptr::read_unaligned",
        "core::ptr::read_volatile",
        "core::ptr::write",
        "core::ptr::write_unaligned",
        "core::ptr::write_volatile",
    ] {
        for (offset, violates) in [(-100, true), (-1, true), (0, false), (63, false), (64, true)] {
            let mut function = wrapping_access_fixture(offset, 1);
            let Terminator::Call { func, callee_key, args, .. } =
                &mut function.body.blocks[1].terminator
            else {
                panic!("access fixture")
            };
            *func = callee.into();
            *callee_key = fixture_key(callee);
            args.truncate(if callee.contains("write") { 2 } else { 1 });
            assert_concrete_access_bounds(&check_sep_unsafe(&function), &[("src", violates)]);
        }
    }
}

#[test]
fn wrapping_offset_copy_checks_source_and_destination_independently() {
    for callee in ["core::ptr::copy", "core::ptr::copy_nonoverlapping"] {
        for offset_side in ["src", "dst"] {
            for (offset, len, violates) in [
                (-100, 1, true),
                (-1, 1, true),
                (0, 1, false),
                (63, 1, false),
                (64, 1, true),
                (1, 64, true),
                (-100, 0, false),
                (64, 0, false),
                (100, 0, false),
            ] {
                let mut function = wrapping_access_fixture(offset, len);
                let Terminator::Call { func, callee_key, args, .. } =
                    &mut function.body.blocks[1].terminator
                else {
                    panic!("access fixture")
                };
                *func = callee.into();
                *callee_key = fixture_key(callee);
                let shifted = Operand::Copy(Place::local(3));
                let base = Operand::Copy(Place::local(2));
                *args =
                    if offset_side == "src" { vec![shifted, base] } else { vec![base, shifted] };
                args.push(Operand::Constant(trust_types::ConstValue::Int(len)));
                let vcs = check_sep_unsafe(&function);
                assert_concrete_access_bounds(
                    &vcs,
                    &[
                        ("src", offset_side == "src" && violates),
                        ("dst", offset_side == "dst" && violates),
                    ],
                );
                for side in ["src", "dst"] {
                    assert!(
                        vcs.iter().any(|vc| matches!(&vc.kind, VcKind::Assertion { message }
                        if message.contains(&format!("alignment check for {side}")))),
                        "zero-count copies must retain both alignment obligations"
                    );
                }
            }
        }
    }
}

#[test]
fn wrapping_offset_raw_parts_distinguishes_borrowed_and_owning_empty_ranges() {
    for callee in [
        "core::slice::raw::from_raw_parts",
        "core::slice::raw::from_raw_parts_mut",
        "core::str::converts::from_raw_parts",
        "core::str::converts::from_raw_parts_mut",
        "alloc::vec::Vec::<u8>::from_raw_parts",
        "alloc::string::String::from_raw_parts",
    ] {
        let owning = callee.starts_with("alloc::");
        for (offset, len, violates) in
            [(-1, 1, true), (0, 64, false), (1, 64, true), (-100, 0, false), (100, 0, owning)]
        {
            let mut function = wrapping_access_fixture(offset, len);
            let Terminator::Call { func, callee_key, args, .. } =
                &mut function.body.blocks[1].terminator
            else {
                panic!("access fixture")
            };
            *func = callee.into();
            *callee_key = fixture_key(callee);
            if owning {
                args.push(Operand::Constant(trust_types::ConstValue::Int(64)));
            }
            assert_concrete_access_bounds(&check_sep_unsafe(&function), &[("src", violates)]);
        }
    }
}

#[test]
fn wrapping_offset_accesses_scale_bytes_and_preserve_zero_sized_pointees() {
    // Cast AFTER a u8 wrapping offset so even a ZST access carries a
    // nonzero byte offset, and wide elements retain the original byte base.
    for (pointee, len, offset, violates) in [
        (Ty::u32(), 1, -4, true),
        (Ty::u32(), 1, 60, false),
        (Ty::u32(), 1, 61, true),
        (Ty::u32(), 16, 0, false),
        (Ty::u32(), 17, 0, true),
        (Ty::Tuple(vec![]), 100, -100, false),
        (Ty::Tuple(vec![]), 100, 100, false),
    ] {
        let mut function = wrapping_access_fixture(offset, len);
        let ptr_ty = Ty::RawPtr { mutable: false, pointee: Box::new(pointee) };
        function.body.locals.push(LocalDecl {
            index: 5,
            ty: ptr_ty.clone(),
            name: Some("cast_ptr".into()),
        });
        function.body.blocks[1].stmts.push(Statement::Assign {
            place: Place::local(5),
            rvalue: Rvalue::Cast(Operand::Copy(Place::local(3)), ptr_ty),
            span: empty_span(),
        });
        let Terminator::Call { args, .. } = &mut function.body.blocks[1].terminator else {
            panic!("slice fixture")
        };
        args[0] = Operand::Copy(Place::local(5));
        assert_concrete_access_bounds(&check_sep_unsafe(&function), &[("src", violates)]);
    }
}

#[test]
fn wrapping_offset_backing_certificate_cannot_justify_access_before_base() {
    use crate::abstract_interp::discharge::try_eval_boolean;
    use crate::abstract_interp::{AbstractDomain, Interval, IntervalDomain};
    // Consumer-side check only: the existing backing_cert tests establish
    // whether constructors may earn this summary. Test both summary states.
    for certified in [false, true] {
        for (offset, len, violates) in [
            (-100, 1, true),
            (-1, 1, true),
            (0, 1, false),
            (63, 1, false),
            (64, 1, true),
            (-100, 0, false),
            (100, 0, false),
        ] {
            let mut function = as_slice_buf_fixture();
            let mut access = function.body.blocks[0].terminator.clone();
            let Terminator::Call { args, target, .. } = &mut access else {
                panic!("slice fixture")
            };
            args[1] = Operand::Constant(trust_types::ConstValue::Int(len));
            // The shifted pointer is a fresh local, as rustc's MIR spells it: a tag
            // is carried only by a local holding one value (BACKING-FIRST-LOAD-1).
            args[0] = Operand::Move(Place::local(4));
            *target = Some(BlockId(2));
            let mut shift = wrapping_access_fixture(offset, len).body.blocks[0].terminator.clone();
            let Terminator::Call { dest, .. } = &mut shift else { panic!("offset fixture") };
            *dest = Place::local(4);
            function.body.locals.push(LocalDecl {
                index: 4,
                ty: Ty::RawPtr { mutable: true, pointee: Box::new(Ty::u8()) },
                name: None,
            });
            function.body.blocks[0].terminator = shift;
            function.body.blocks[1].id = BlockId(2);
            function
                .body
                .blocks
                .insert(1, BasicBlock { id: BlockId(1), stmts: vec![], terminator: access });
            let mut context =
                crate::VcgenContext::for_function(function.def_path.clone()).with_backing(true);
            if certified {
                context = context.with_callee_summaries(
                    crate::CalleeSummaryContext::default().with_certified_backing_structs(
                        std::iter::once("Buf".to_string()).collect(),
                    ),
                );
            }
            let vcs = crate::with_vcgen_context(&context, || check_sep_unsafe(&function));
            let bounds: Vec<_> = vcs
                .iter()
                .filter(|vc| {
                    matches!(&vc.kind,
                VcKind::CopyBoundsViolation { detail, .. } if detail.contains("backing field"))
                })
                .collect();
            assert_eq!(bounds.len(), 1);
            let mut domain = IntervalDomain::top();
            domain.set(
                crate::separation_logic::generated_symbol("backing_alloc_size_1_0"),
                Interval::constant(64),
            );
            domain.set("len".into(), Interval::constant(64));
            assert_eq!(
                try_eval_boolean(&bounds[0].formula, &domain),
                Some(violates),
                "certified={certified}, offset={offset}, len={len}: {:?}",
                bounds[0].formula
            );
        }
    }
}
