//! Read-only bounded structural oracle for THIS observed three-local/four-block
//! helper. This is test data inspection, not a frontend, proof/admission token,
//! arbitrary-body authority, or a claim about Rust execution semantics.
use rustc_middle::{mir, ty};

use super::nominal_capture::FaithfulNominalCapture;
use super::nominal_parameter::NominalParameterObservation;

pub const TRUE_TAGS: [u128; 8] = [0, 1, 2, 3, 4, 5, 8, 9];

fn source_place(place: mir::Place<'_>, local: usize) -> bool {
    place.local.as_usize() == local && place.projection.is_empty()
}

pub fn source_shape<'tcx>(
    body: &mir::Body<'tcx>,
    nominal: &NominalParameterObservation<'tcx>,
) -> bool {
    let tcx = nominal.context();
    if body.phase != mir::MirPhase::Runtime(mir::RuntimePhase::PostCleanup)
        || body.pass_count != 1
        || body.tainted_by_errors.is_some()
        || body.coroutine.is_some()
        || body.is_polymorphic
        || body.injection_phase.is_some()
        || !body.user_type_annotations.is_empty()
        || body.required_consts.as_ref().is_none_or(|constants| !constants.is_empty())
        || body.local_decls.len() != 3
        || body.basic_blocks.len() != 4
        || body.arg_count != 1
        || body.spread_arg.is_some()
        || body.source.promoted.is_some()
        || !matches!(body.source.instance, ty::InstanceKind::Item(id) if id == nominal.owner().to_def_id())
        || body.local_decls[mir::RETURN_PLACE].ty != tcx.types.bool
        || body.local_decls[mir::Local::from_usize(1)].ty != nominal.source_ty()
        || body.local_decls[mir::Local::from_usize(2)].ty != tcx.types.isize
        || body.basic_blocks.iter().any(|b| b.is_cleanup)
    {
        return false;
    }
    let blocks = &body.basic_blocks;
    for (index, count) in [1, 1, 1, 0].into_iter().enumerate() {
        if blocks[mir::BasicBlock::from_usize(index)].statements.len() != count {
            return false;
        }
    }
    let first = &blocks[mir::START_BLOCK];
    if !matches!(&first.statements[0].kind,
        mir::StatementKind::Assign(pair) if source_place(pair.0,2) &&
        matches!(pair.1,mir::Rvalue::Discriminant(place) if source_place(place,1)))
    {
        return false;
    }
    let Some(first_end) = first.terminator.as_ref() else {
        return false;
    };
    let mir::TerminatorKind::SwitchInt { discr: mir::Operand::Move(place), targets } =
        &first_end.kind
    else {
        return false;
    };
    if !source_place(*place, 2)
        || targets.otherwise().as_usize() != 1
        || targets.iter().ne(TRUE_TAGS.into_iter().map(|tag| (tag, mir::BasicBlock::from_usize(2))))
    {
        return false;
    }
    for (id, expected) in [(1, false), (2, true)] {
        let block = &blocks[mir::BasicBlock::from_usize(id)];
        let mir::StatementKind::Assign(pair) = &block.statements[0].kind else {
            return false;
        };
        let mir::Rvalue::Use(mir::Operand::Constant(value), mir::WithRetag::Yes) = &pair.1 else {
            return false;
        };
        if !source_place(pair.0, 0)
            || value.const_.ty() != tcx.types.bool
            || value.const_.try_to_bool() != Some(expected)
            || !matches!(block.terminator.as_ref().map(|t| &t.kind), Some(mir::TerminatorKind::Goto { target, loop_hint_attrs }) if target.as_usize()==3 && loop_hint_attrs.is_empty())
        {
            return false;
        }
    }
    matches!(
        blocks[mir::BasicBlock::from_usize(3)].terminator.as_ref().map(|t| &t.kind),
        Some(mir::TerminatorKind::Return)
    )
}

fn faithful_place(place: &trust_types::Place, local: usize) -> bool {
    place.local == local && place.projections.is_empty()
}

pub fn faithful_shape(
    body: &trust_types::VerifiableBody,
    nominal: &NominalParameterObservation<'_>,
) -> bool {
    use trust_types::{ConstValue, Operand, Rvalue, Statement, Terminator, Ty};
    if body.arg_count != 1
        || body.return_ty != Ty::Bool
        || body.locals.len() != 3
        || body.blocks.len() != 4
        || !body.datatype_defs.is_empty()
        || body.locals.iter().enumerate().any(|(i, l)| l.index != i)
        || body.locals[0].ty != Ty::Bool
        || body.locals[2].ty != (Ty::PtrSizedInt { signed: true })
        || body.blocks.iter().enumerate().any(|(i, b)| b.id.0 != i)
        || body.blocks.iter().zip([1, 1, 1, 0]).any(|(b, n)| b.stmts.len() != n)
    {
        return false;
    }
    if !matches!(&body.blocks[0].stmts[0], Statement::Assign {place,rvalue:Rvalue::Discriminant(from),..}
        if faithful_place(place,2)&&faithful_place(from,1))
    {
        return false;
    }
    let Terminator::SwitchInt {
        discr: Operand::Move(place),
        targets,
        otherwise,
        exhaustive_enum_unreachable: false,
        ..
    } = &body.blocks[0].terminator
    else {
        return false;
    };
    if !faithful_place(place, 2)
        || otherwise.0 != 1
        || targets
            .iter()
            .map(|(tag, block)| (*tag, block.0))
            .ne(TRUE_TAGS.into_iter().map(|tag| (tag, 2)))
    {
        return false;
    }
    for (id, expected) in [(1, false), (2, true)] {
        let block = &body.blocks[id];
        if !matches!(&block.stmts[0],Statement::Assign {place,rvalue:Rvalue::Use(Operand::Constant(ConstValue::Bool(value))),..} if faithful_place(place,0)&&*value==expected)
            || !matches!(block.terminator,Terminator::Goto(target) if target.0==3)
        {
            return false;
        }
    }
    matches!(body.blocks[3].terminator, Terminator::Return)
        && faithful_nominal(&body.locals[1].ty, nominal)
}

fn faithful_nominal(ty: &trust_types::Ty, nominal: &NominalParameterObservation<'_>) -> bool {
    use trust_types::{AdtAuth, AdtKind, EnumReprHint, EnumTagEncodingInfo, Ty};
    let Ty::Adt {
        name,
        fields,
        variants,
        disc_index_safe,
        faithful_enum_repr,
        layout,
        enum_layout,
        adt_kind,
        arbitrary_precision,
        validity_wrapper: _,
    } = ty
    else {
        return false;
    };
    let declaration = nominal.declaration();
    if declaration.variants().len() != 16
        || variants.len() != 16
        || fields.len() != 1
        || !*disc_index_safe
        || *faithful_enum_repr != Some(None)
        || layout.is_some()
        || *adt_kind != Some(AdtKind::Enum)
        || *arbitrary_precision != Some(AdtAuth::TotalDrop(None))
        || fields[0] != ("__tag".to_owned(), Ty::Int { width: 64, signed: true })
        || *name
            != trust_mir_extract::sysroot_authenticated_def_path_str(
                nominal.context(),
                declaration.did(),
            )
    {
        return false;
    }
    let Some(layout) = enum_layout else {
        return false;
    };
    if layout.size != 1
        || layout.align != 1
        || layout.variant_field_offsets.len() != 16
        || layout.variant_field_offsets.iter().any(|fields| !fields.is_empty())
        || !matches!(
            layout.encoding,
            EnumTagEncodingInfo::Direct { tag_offset: 0, tag_ty: EnumReprHint::U8 }
        )
    {
        return false;
    }
    for (((source, extracted), (ordinal, disc)), expected) in declaration
        .variants()
        .iter()
        .zip(variants.iter())
        .zip(declaration.discriminants(nominal.context()))
        .zip(0..16)
    {
        if ordinal.as_usize() != expected
            || disc.val != expected as u128
            || source.name.as_str() != extracted.name
            || !source.fields.is_empty()
            || extracted.discriminant != expected as i128
            || !extracted.fields.is_empty()
        {
            return false;
        }
    }
    true
}

pub fn actual_pair_shape(capture: &FaithfulNominalCapture<'_>) -> bool {
    // Nominal type identity comes from the genuine observation; no QName/tag
    // check can construct it. Source and output are the private producer pair.
    source_shape(capture.source().body(), capture.source().nominal())
        && faithful_shape(&capture.function().body, capture.source().nominal())
}

/// Mutants are ordinary cloned DATA, never fed into compiler query custody.
/// Each check is a whole-body rejection, not a per-node exemption.
pub fn mutation_controls(capture: &FaithfulNominalCapture<'_>) -> usize {
    let nominal = capture.source().nominal();
    let tcx = nominal.context();
    let bb = mir::BasicBlock::from_usize;
    let local = mir::Local::from_usize;
    assert!(actual_pair_shape(capture));
    let mut count = 0;
    for mutation in 0..18 {
        let mut body = capture.source().body().clone();
        match mutation {
            0 => {
                body.local_decls.pop();
            }
            1 => {
                body.basic_blocks.as_mut().truncate(3);
            }
            2 => body.arg_count = 0,
            3 => body.local_decls[local(2)].ty = tcx.types.u64,
            4 => body.local_decls[local(1)].ty = tcx.types.bool,
            5 => {
                if let mir::StatementKind::Assign(pair) =
                    &mut body.basic_blocks.as_mut()[bb(2)].statements[0].kind
                {
                    if let mir::Rvalue::Use(_, retag) = &mut pair.1 {
                        *retag = mir::WithRetag::No;
                    }
                }
            }
            6 => {
                if let mir::TerminatorKind::SwitchInt { discr, .. } =
                    &mut body.basic_blocks.as_mut()[bb(0)].terminator_mut().kind
                {
                    if let mir::Operand::Move(place) = discr {
                        *discr = mir::Operand::Copy(*place);
                    }
                }
            }
            7 => {
                if let mir::StatementKind::Assign(pair) =
                    &mut body.basic_blocks.as_mut()[bb(0)].statements[0].kind
                {
                    pair.0.local = local(0);
                }
            }
            8 => {
                if let mir::StatementKind::Assign(pair) =
                    &mut body.basic_blocks.as_mut()[bb(0)].statements[0].kind
                {
                    if let mir::Rvalue::Discriminant(place) = &mut pair.1 {
                        place.local = local(0);
                    }
                }
            }
            9 => {
                if let mir::TerminatorKind::Goto { target, .. } =
                    &mut body.basic_blocks.as_mut()[bb(1)].terminator_mut().kind
                {
                    *target = bb(0);
                }
            }
            10 => {
                body.basic_blocks.as_mut()[bb(3)].terminator_mut().kind =
                    mir::TerminatorKind::Unreachable
            }
            11 => {
                let extra = body.basic_blocks[bb(0)].statements[0].clone();
                body.basic_blocks.as_mut()[bb(0)].statements.push(extra);
            }
            12 => body.basic_blocks.as_mut()[bb(1)].is_cleanup = true,
            13 => body.source.instance = ty::InstanceKind::Item(nominal.declaration().did()),
            14 => body.phase = mir::MirPhase::Runtime(mir::RuntimePhase::Optimized),
            15 => body.basic_blocks.as_mut()[bb(3)].terminator = None,
            16 => {
                if let mir::TerminatorKind::SwitchInt { targets, .. } =
                    &mut body.basic_blocks.as_mut()[bb(0)].terminator_mut().kind
                {
                    *targets = mir::SwitchTargets::new(
                        TRUE_TAGS.into_iter().skip(1).map(|tag| (tag, bb(2))),
                        bb(1),
                    );
                }
            }
            17 => {
                if let mir::TerminatorKind::SwitchInt { targets, .. } =
                    &mut body.basic_blocks.as_mut()[bb(0)].terminator_mut().kind
                {
                    *targets = mir::SwitchTargets::new(
                        TRUE_TAGS.into_iter().map(|tag| (tag, bb(2))),
                        bb(0),
                    );
                }
            }
            _ => unreachable!(),
        }
        assert!(!source_shape(&body, nominal), "source mutation {mutation} admitted");
        count += 1;
    }
    for mutation in 0..16 {
        let mut body = capture.function().body.clone();
        use trust_types::{BlockId, Operand, Rvalue, Statement, Terminator, Ty};
        match mutation {
            0 => body.locals[2].ty = Ty::Bool,
            1 => {
                let extra = body.blocks[0].stmts[0].clone();
                body.blocks[0].stmts.push(extra);
            }
            2 => {
                if let Terminator::SwitchInt { discr, .. } = &mut body.blocks[0].terminator {
                    if let Operand::Move(place) = discr {
                        *discr = Operand::Copy(place.clone());
                    }
                }
            }
            3 => {
                if let Statement::Assign {
                    rvalue: Rvalue::Use(Operand::Constant(trust_types::ConstValue::Bool(value))),
                    ..
                } = &mut body.blocks[2].stmts[0]
                {
                    *value = false;
                }
            }
            4 => body.blocks[1].terminator = Terminator::Goto(BlockId(0)),
            5 => body.blocks[3].terminator = Terminator::Unreachable,
            6 => body.blocks[1].id = BlockId(0),
            7 => body.arg_count = 2,
            8 => {
                if let Ty::Adt { variants, .. } = &mut body.locals[1].ty {
                    variants.make_mut()[0].discriminant = 64;
                }
            }
            9 => {
                if let Ty::Adt { faithful_enum_repr, .. } = &mut body.locals[1].ty {
                    *faithful_enum_repr = None;
                }
            }
            10 => {
                if let Ty::Adt { name, .. } = &mut body.locals[1].ty {
                    *name = "forged".to_owned();
                }
            }
            11 => {
                body.datatype_defs.insert("hidden".to_owned(), Ty::Bool);
            }
            12 => {
                if let Terminator::SwitchInt { targets, .. } = &mut body.blocks[0].terminator {
                    targets[0].1 = BlockId(1);
                }
            }
            13 => {
                if let Terminator::SwitchInt { otherwise, .. } = &mut body.blocks[0].terminator {
                    *otherwise = BlockId(0);
                }
            }
            14 => {
                if let Terminator::SwitchInt { exhaustive_enum_unreachable, .. } =
                    &mut body.blocks[0].terminator
                {
                    *exhaustive_enum_unreachable = true;
                }
            }
            15 => {
                if let Ty::Adt { variants, .. } = &mut body.locals[1].ty {
                    variants.make_mut()[0].fields.push(("payload".to_owned(), Ty::Bool));
                }
            }
            _ => unreachable!(),
        }
        assert!(!faithful_shape(&body, nominal), "faithful mutation {mutation} admitted");
        count += 1;
    }
    assert!(actual_pair_shape(capture), "cloned data mutation changed genuine capture");
    count
}
