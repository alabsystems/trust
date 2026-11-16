// module_to_lir_unknown_offset_refused.rs — a field address the trust-ir bridge could
// not place is REFUSED by the codegen converter, measured (2026-09-29).
//
// Since 2026-09-28 the bridge spells a field address into a layout-less base as the
// object at an UNKNOWN offset — `%off = undef u64; gep u8 %base[%off]` — instead of
// the retired `index * size_of(field)` guess. The freeze-ratification follow-up asked
// for the converter's refusal of that form to be MEASURED, not read from the code: the
// first fixture passed the tuple BY VALUE, and the converter refused the tuple
// PARAMETER before it ever saw the address. Here the base is reached through a
// POINTER parameter, so the address is the first thing the converter meets that it
// cannot lower:
//
//   * unknown offset (a layout-less tuple, a layout-less struct) -> `UnsupportedUndef`
//     naming the offset's own `undef` value, never an object;
//   * the same body over a tuple whose rustc layout the function carries
//     (`VerifiableFunction::tuple_layouts`) -> a constant byte offset the converter
//     gets PAST; it stops later, at the load, on the pointer parameter's provenance
//     (measured). That control is what makes the refusal above a statement about the
//     OFFSET, not about the shape. (A tuple in a local slot cannot serve as a control
//     that lowers end to end: the converter has no `Borrow`, measured.)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_cg_bridge::{ModuleLirError, lower_module_to_lir};
use trust_ir::Module;
use trust_ir::inst::Inst;
use trust_ir::ty::Ty as IrTy;
use trust_ir::value::ValueId;
use trust_types::{
    BasicBlock, BlockId, LayoutTarget, LocalDecl, Operand, Place, Projection, Rvalue, SourceSpan,
    Statement, Terminator, TupleLayoutInfo, TupleLayouts, Ty, VerifiableBody, VerifiableFunction,
};

/// `fn read_second(p: &Base) -> u8 { let r = &(*p).1; *r }`, carrying `layouts`.
fn field_through_pointer(base: Ty, layouts: TupleLayouts) -> VerifiableFunction {
    let span = SourceSpan::default();
    VerifiableFunction {
        name: "read_second".to_string(),
        def_path: "unknown_offset::read_second".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u8(), name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Ref { mutable: false, inner: Box::new(base) },
                    name: Some("p".into()),
                },
                LocalDecl {
                    index: 2,
                    ty: Ty::Ref { mutable: false, inner: Box::new(Ty::u8()) },
                    name: Some("r".into()),
                },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Ref {
                            mutable: false,
                            place: Place {
                                local: 1,
                                projections: vec![Projection::Deref, Projection::Field(1)],
                            },
                        },
                        span: span.clone(),
                    },
                    Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place {
                            local: 2,
                            projections: vec![Projection::Deref],
                        })),
                        span,
                    },
                ],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::u8(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: layouts,
    }
}

fn u32_u8() -> Ty {
    Ty::Tuple(vec![Ty::u32(), Ty::u8()])
}

/// Rustc's layout of `(u32, u8)` on aarch64: size 8, align 4, offsets [0, 4].
fn u32_u8_row() -> TupleLayouts {
    TupleLayouts::from_rows(
        Some(LayoutTarget {
            triple: "aarch64-apple-darwin".into(),
            pointer_size: 8,
            little_endian: true,
        }),
        vec![TupleLayoutInfo {
            tuple: u32_u8(),
            size: 8,
            align: 4,
            field_offsets: vec![0, 4],
            field_sizes: vec![4, 1],
            field_aligns: vec![4, 1],
        }],
    )
}

/// The `undef u64` a GEP of the only function uses as its index, if any.
fn offset_undef(module: &Module) -> Option<ValueId> {
    let function = &module.functions[0];
    let undefs: Vec<ValueId> = function
        .blocks
        .iter()
        .flat_map(|block| &block.body)
        .filter(|node| matches!(node.inst, Inst::Undef { ty: IrTy::U64 }))
        .filter_map(|node| node.results.first().copied())
        .collect();
    function.blocks.iter().flat_map(|block| &block.body).find_map(|node| match &node.inst {
        Inst::GEP { indices, .. } => indices.iter().copied().find(|index| undefs.contains(index)),
        _ => None,
    })
}

#[test]
fn an_unknown_offset_field_address_is_refused_by_the_converter() {
    let layout_less_struct = Ty::adt("S", vec![("a".into(), Ty::u32()), ("b".into(), Ty::u8())]);
    for base in [u32_u8(), layout_less_struct] {
        let module = trust_ir_bridge::lower_to_trust_ir(&field_through_pointer(
            base.clone(),
            Default::default(),
        ))
        .expect("a layout-less field address lowers, as an unknown offset");
        let undef = offset_undef(&module)
            .unwrap_or_else(|| panic!("{base:?}: the address must name no offset\n{module}"));
        match lower_module_to_lir(&module, module.functions[0].id) {
            Err(ModuleLirError::UnsupportedUndef { detail, .. }) => assert!(
                detail.contains(&format!("Undef value {} ", undef.index())),
                "{base:?}: the refusal must name the offset's own undef (value {}), got {detail}",
                undef.index()
            ),
            Err(other) => panic!(
                "{base:?}: the converter must refuse the UNKNOWN OFFSET, not something before \
                 it (otherwise this row measures nothing): {other}\n{module}"
            ),
            Ok(_) => panic!(
                "{base:?}: the converter lowered an address whose offset is unknown — it chose \
                 an offset nobody computed\n{module}"
            ),
        }
    }
}

#[test]
fn a_laid_out_tuple_field_address_is_not_where_the_converter_stops() {
    // THE CONTROL — the same pointer-parameter body over a tuple carrying rustc's row. The
    // address is now a constant byte offset (4) and the converter gets PAST it; it stops
    // at the load instead, because it models no provenance for a pointer PARAMETER
    // (measured 2026-09-29: "memory op uses pointer value 0 with unsupported
    // provenance"). That is what makes the refusal above a statement about the OFFSET.
    let module = trust_ir_bridge::lower_to_trust_ir(&field_through_pointer(u32_u8(), u32_u8_row()))
        .expect("a laid-out tuple field address lowers");
    assert_eq!(offset_undef(&module), None, "rustc's layout names the offset\n{module}");
    match lower_module_to_lir(&module, module.functions[0].id) {
        Err(ModuleLirError::UnsupportedUndef { detail, .. }) => {
            panic!("a declared offset must not be refused as an undef: {detail}\n{module}")
        }
        Err(other) => assert!(
            other.to_string().contains("unsupported provenance"),
            "the converter must get past the declared offset and stop at the parameter \
             pointer's provenance, got: {other}\n{module}"
        ),
        Ok(_) => {}
    }
}
