//! Model-level controls over the actual emitted consumer formulas. Fixture
//! keys select authenticated operation branches; they are not compiler evidence.

use trust_types::ConstValue;

use super::{Formula, Operand, Place, SepEngine, SourceSpan, Ty, VcKind};

fn call(engine: &mut SepEngine, name: &str, args: &[Operand], dest: usize) {
    let key = super::tests::fixture_key(name);
    assert!(key.is_some(), "recognized fixture key required: {name}");
    engine.interpret_call(
        name,
        args,
        &Place::local(dest),
        &SourceSpan::default(),
        false,
        key.as_ref(),
    );
}

fn prepared(offset: i128) -> SepEngine {
    prepared_with(offset, false, Ty::u8())
}

fn prepared_with(offset: i128, mutable: bool, pointee: Ty) -> SepEngine {
    let raw = Ty::RawPtr { mutable, pointee: Box::new(pointee) };
    let mut engine = SepEngine::new("negative_wrapping_consumer").with_local_tys(vec![
        Ty::Unit,
        Ty::Array { elem: Box::new(Ty::u8()), len: 64 },
        raw.clone(),
        raw,
        Ty::usize(),
    ]);
    engine.interpret_address_of(&Place::local(2), &Place::local(1), false, &SourceSpan::default());
    let method = if mutable {
        "core::ptr::mut_ptr::wrapping_offset"
    } else {
        "core::ptr::const_ptr::wrapping_offset"
    };
    call(
        &mut engine,
        method,
        &[Operand::Copy(Place::local(2)), Operand::Constant(ConstValue::Int(offset))],
        3,
    );
    assert!(engine.vcs.iter().all(|vc| !matches!(&vc.kind,
        VcKind::Assertion { message } if message.contains("[unsafe:sep:offset]"))));
    // Isolate the consumer: unrelated constructor rows cannot mask a bad VC.
    engine.vcs.clear();
    engine
}

fn integer(formula: &Formula, variables: &[(&str, i128)]) -> Option<i128> {
    match formula {
        Formula::Int(n) => Some(*n),
        Formula::Var(name, _) => variables.iter().find(|(key, _)| *key == name).map(|(_, n)| *n),
        Formula::Add(a, b) => integer(a, variables)?.checked_add(integer(b, variables)?),
        Formula::Mul(a, b) => integer(a, variables)?.checked_mul(integer(b, variables)?),
        _ => None,
    }
}

fn boolean(formula: &Formula, variables: &[(&str, i128)]) -> Option<bool> {
    match formula {
        Formula::Bool(b) => Some(*b),
        Formula::Lt(a, b) => Some(integer(a, variables)? < integer(b, variables)?),
        Formula::Gt(a, b) => Some(integer(a, variables)? > integer(b, variables)?),
        Formula::Le(a, b) => Some(integer(a, variables)? <= integer(b, variables)?),
        Formula::Ge(a, b) => Some(integer(a, variables)? >= integer(b, variables)?),
        Formula::And(xs) => {
            let mut result = true;
            for x in xs {
                result &= boolean(x, variables)?;
            }
            Some(result)
        }
        Formula::Or(xs) => {
            let mut result = false;
            for x in xs {
                result |= boolean(x, variables)?;
            }
            Some(result)
        }
        _ => None,
    }
}

fn bounds_formula<'a>(engine: &'a SepEngine, side: &str) -> &'a Formula {
    let rows: Vec<_> = engine
        .vcs
        .iter()
        .filter(|vc| {
            matches!(&vc.kind,
        VcKind::CopyBoundsViolation { direction, .. } if direction == side)
        })
        .collect();
    assert_eq!(rows.len(), 1, "exact consumer bounds row required: {:?}", engine.vcs);
    &rows[0].formula
}

fn assert_bounds(engine: &SepEngine, side: &str, violated: bool) {
    let formula = bounds_formula(engine, side);
    assert_eq!(
        boolean(formula, &[]),
        Some(violated),
        "actual range formula, not unrelated row count: {formula:?}"
    );
}

#[test]
fn signed_wrapping_offset_then_raw_read_write_checks_both_ends() {
    for name in [
        "core::ptr::read",
        "core::ptr::read_volatile",
        "core::ptr::read_unaligned",
        "core::ptr::write",
        "core::ptr::write_volatile",
        "core::ptr::write_unaligned",
    ] {
        for (offset, violated) in [(-100, true), (-1, true), (0, false), (63, false), (64, true)] {
            let write = name.contains("write");
            let mut engine = prepared_with(offset, write, Ty::u8());
            let mut args = vec![Operand::Copy(Place::local(3))];
            if write {
                args.push(Operand::Constant(ConstValue::Int(0)));
            }
            call(&mut engine, name, &args, 0);
            assert_bounds(&engine, "src", violated);
        }
    }
}

#[test]
fn signed_wrapping_offset_then_raw_parts_checks_both_ends() {
    for name in ["core::slice::raw::from_raw_parts", "core::slice::raw::from_raw_parts_mut"] {
        for (offset, violated) in [(-100, true), (-1, true), (0, false), (63, false), (64, true)] {
            let mut engine = prepared(offset);
            call(
                &mut engine,
                name,
                &[Operand::Copy(Place::local(3)), Operand::Constant(ConstValue::Int(1))],
                0,
            );
            assert_bounds(&engine, "src", violated);
        }
    }
}

#[test]
fn signed_wrapping_offset_checks_each_copy_side() {
    for name in ["core::ptr::copy", "core::ptr::copy_nonoverlapping"] {
        for negative_source in [true, false] {
            let mut engine = prepared(-100);
            let (src, dst) = if negative_source { (3, 2) } else { (2, 3) };
            call(
                &mut engine,
                name,
                &[
                    Operand::Copy(Place::local(src)),
                    Operand::Copy(Place::local(dst)),
                    Operand::Constant(ConstValue::Int(1)),
                ],
                0,
            );
            assert_bounds(&engine, "src", negative_source);
            assert_bounds(&engine, "dst", !negative_source);
        }
    }
}

#[test]
fn safe_wrapping_intermediate_can_return_to_base() {
    let mut engine = prepared(-100);
    call(
        &mut engine,
        "core::ptr::const_ptr::wrapping_offset",
        &[Operand::Copy(Place::local(3)), Operand::Constant(ConstValue::Int(100))],
        3,
    );
    assert!(engine.vcs.is_empty(), "unused wrapping construction must stay safe");
    call(&mut engine, "core::ptr::read", &[Operand::Copy(Place::local(3))], 0);
    assert_bounds(&engine, "src", false);
}

#[test]
fn empty_copy_preserves_existing_range_boundary_and_alignment_rows() {
    for pointee in [Ty::u8(), Ty::u32()] {
        let mut engine = prepared_with(-100, false, pointee);
        call(
            &mut engine,
            "core::ptr::copy",
            &[
                Operand::Copy(Place::local(3)),
                Operand::Copy(Place::local(2)),
                Operand::Constant(ConstValue::Int(0)),
            ],
            0,
        );
        // Only the existing zero-byte bounds behavior, not a whole-copy theorem.
        assert_bounds(&engine, "src", false);
        assert_bounds(&engine, "dst", false);
        assert!(engine.vcs.iter().any(|vc| matches!(&vc.kind,
            VcKind::Assertion { message } if message.contains("alignment check"))));
    }
}

#[test]
fn symbolic_width_guards_the_negative_start_without_assuming_positivity() {
    let mut engine = prepared(-100);
    call(
        &mut engine,
        "core::ptr::copy",
        &[
            Operand::Copy(Place::local(3)),
            Operand::Copy(Place::local(2)),
            Operand::Copy(Place::local(4)),
        ],
        0,
    );
    let formula = bounds_formula(&engine, "src");
    for (width, violated) in [(0, false), (1, true), (164, true)] {
        assert_eq!(boolean(formula, &[("_4", width)]), Some(violated), "{formula:?}");
    }
}

#[test]
fn both_signed_wrapping_tags_preserve_byte_stride() {
    for mutable in [false, true] {
        for (offset, violated) in [(-1, true), (0, false), (15, false), (16, true)] {
            // u32 extent is offset*4 + 4. Bounds only: the byte-array backing
            // fixture does not establish an alignment proof for u32 accesses.
            let mut engine = prepared_with(offset, mutable, Ty::u32());
            let mut args = vec![Operand::Copy(Place::local(3))];
            let name = if mutable {
                args.push(Operand::Constant(ConstValue::Int(0)));
                "core::ptr::write"
            } else {
                "core::ptr::read"
            };
            call(&mut engine, name, &args, 0);
            assert_bounds(&engine, "src", violated);
        }
    }
}

fn contains_negative_start(formula: &Formula) -> bool {
    matches!(formula, Formula::Lt(a, b)
        if integer(a, &[]) == Some(-100) && integer(b, &[]) == Some(0))
        || formula.children().into_iter().any(contains_negative_start)
}

#[test]
fn backing_certificate_does_not_erase_negative_start() {
    for certified in [false, true] {
        let mut engine =
            prepared(-100).with_field_backing(vec![(0, 1)]).with_backing_certified(certified);
        // Consumer branch fixture, not a compiler-established certificate.
        engine.field_loads.insert(3, (7, 0));
        engine.field_load_var.insert((7, 1), Formula::Int(64));
        call(
            &mut engine,
            "core::slice::raw::from_raw_parts",
            &[Operand::Copy(Place::local(3)), Operand::Constant(ConstValue::Int(1))],
            0,
        );
        let rows: Vec<_> = engine
            .vcs
            .iter()
            .filter(|vc| {
                matches!(&vc.kind,
            VcKind::CopyBoundsViolation { detail, .. } if detail.contains("backing field"))
            })
            .collect();
        assert_eq!(rows.len(), 1);
        assert!(contains_negative_start(&rows[0].formula), "{:?}", rows[0].formula);
        assert_eq!(
            matches!(&rows[0].formula, Formula::And(parts)
                if parts.iter().any(|part| matches!(part, Formula::Ge(_, _)))),
            certified,
            "retain the certified assumption around the whole violation"
        );
    }
}
