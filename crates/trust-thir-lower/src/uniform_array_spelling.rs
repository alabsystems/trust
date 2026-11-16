//! Trust (trust-ir v50, `docs/SPEC_RATIFICATIONS.md` §3.1): the one spelling of a uniform
//! constant array.
//!
//! From wire v50 the validator refuses a constant array of two or more equal elements spelled as
//! a list (`NonCanonicalUniformArray`): at an array type, a `Constant::Array` or
//! `Constant::Aggregate` whose elements are all equal, and a raw `Constant::Bytes { utf8: false }`
//! of one repeated byte, are spelled `Constant::Splat`. This producer builds its array constants
//! as lists throughout lowering — the zero and seed lanes, repeat expressions, byte globals — and
//! every reader inside the crate pairs `Ty::Array` with that list (the interpreter pairing, the
//! string-global ledger, the differential's initializer comparison). So the assembled crate
//! module is respelled here, ONCE, as the last step of assembly: before any append, obligation,
//! license stamp or digest binds to it, and after every in-crate reader of the lists has run.
//!
//! The walk mirrors the validator's typed walk (`trust-ir-build`'s `constant_values.rs`): the
//! rule applies only at an array type, and a nested array is reached through the element type of
//! an array and the field types of a struct, tuple or record. Uniformity is decided by
//! `Constant::array`, the sanctioned constructor, which identifies the list spellings of one
//! array exactly as the validator does. A constant this walk has no type for (an enum payload,
//! an unresolvable type id) is left as written, so the validator — not this pass — stays the
//! judge of it.

use trust_ir::{Constant, Inst, Module, Ty};

/// Respell every uniform constant array of `module` — `Inst::Const` values and global
/// initializers — in its canonical `Constant::Splat` spelling.
pub(crate) fn respell_uniform_arrays(module: &mut Module) {
    let mut edits = Vec::new();
    for (fi, function) in module.functions.iter().enumerate() {
        for (bi, block) in function.blocks.iter().enumerate() {
            for (ni, node) in block.body.iter().enumerate() {
                if let Inst::Const { ty, value } = &node.inst {
                    if let Some(respelled) = respell(module, value, ty) {
                        edits.push((fi, bi, ni, respelled));
                    }
                }
            }
        }
    }
    for (fi, bi, ni, respelled) in edits {
        if let Inst::Const { value, .. } = &mut module.functions[fi].blocks[bi].body[ni].inst {
            *value = respelled;
        }
    }
    let globals: Vec<(usize, Constant)> = module
        .globals
        .iter()
        .enumerate()
        .filter_map(|(gi, global)| {
            let init = global.initializer.as_ref()?;
            Some((gi, respell(module, init, &global.ty)?))
        })
        .collect();
    for (gi, respelled) in globals {
        module.globals[gi].initializer = Some(respelled);
    }
}

/// The canonical spelling of `constant` at `ty`, or `None` when it already is canonical (or is
/// a shape this walk has no type for).
fn respell(module: &Module, constant: &Constant, ty: &Ty) -> Option<Constant> {
    match (constant, ty) {
        (Constant::Array(values) | Constant::Aggregate(values), Ty::Array(id, len))
            if values.len() as u64 == *len =>
        {
            let elem_ty = module.ty(*id)?;
            let (children, changed) = respell_children(module, values, |_| Some(elem_ty));
            match Constant::array(children) {
                splat @ Constant::Splat { .. } => Some(splat),
                Constant::Array(children) if changed => Some(match constant {
                    Constant::Aggregate(_) => Constant::Aggregate(children),
                    _ => Constant::Array(children),
                }),
                _ => None,
            }
        }
        (Constant::Bytes { data, utf8 }, Ty::Array(..)) if Constant::is_uniform_bytes(data, *utf8) => {
            Some(Constant::splat(Constant::Int(i128::from(data[0])), data.len() as u64))
        }
        (Constant::Splat { elem, len }, Ty::Array(id, _)) => {
            let respelled = respell(module, elem, module.ty(*id)?)?;
            Some(Constant::Splat { elem: Box::new(respelled), len: *len })
        }
        (Constant::Aggregate(fields), Ty::Struct(id)) => {
            let def = module.struct_def(*id)?;
            let (children, changed) = respell_children(module, fields, |i| Some(&def.fields.get(i)?.ty));
            changed.then_some(Constant::Aggregate(children))
        }
        (Constant::Aggregate(fields), Ty::Tuple(tys)) => {
            let (children, changed) = respell_children(module, fields, |i| tys.get(i));
            changed.then_some(Constant::Aggregate(children))
        }
        (Constant::Record(fields), Ty::Record(id)) => {
            let def = module.record_def(*id)?;
            let mut changed = false;
            let respelled = fields
                .iter()
                .enumerate()
                .map(|(i, (name, value))| {
                    let field_ty = def.fields.get(i).map(|f| &f.ty);
                    match field_ty.and_then(|t| respell(module, value, t)) {
                        Some(new) => {
                            changed = true;
                            (name.clone(), new)
                        }
                        None => (name.clone(), value.clone()),
                    }
                })
                .collect();
            changed.then_some(Constant::Record(respelled))
        }
        _ => None,
    }
}

/// Respell each child at the type `child_ty` gives its index; a child with no type is kept.
fn respell_children<'t>(
    module: &Module,
    children: &[Constant],
    child_ty: impl Fn(usize) -> Option<&'t Ty>,
) -> (Vec<Constant>, bool) {
    let mut changed = false;
    let respelled = children
        .iter()
        .enumerate()
        .map(|(i, child)| match child_ty(i).and_then(|t| respell(module, child, t)) {
            Some(new) => {
                changed = true;
                new
            }
            None => child.clone(),
        })
        .collect();
    (respelled, changed)
}

#[cfg(test)]
mod tests {
    use trust_ir::{BlockId, FuncId, FuncTy, FuncTyId, InstrNode, ValueId};

    use super::*;

    fn module_with_const(ty_of: impl FnOnce(&mut Module) -> Ty, value: Constant) -> Module {
        let mut module = Module::new("t");
        let ty = ty_of(&mut module);
        module.func_types.push(FuncTy {
            params: vec![],
            returns: vec![ty.clone()],
            is_vararg: false,
            abi: None,
        });
        let mut f = trust_ir::Function::new(FuncId::new(0), "f", FuncTyId::new(0), BlockId::new(0));
        let mut block = trust_ir::Block::new(BlockId::new(0));
        block.body = vec![
            InstrNode::new(Inst::Const { ty, value }).with_result(ValueId::new(0)),
            InstrNode::new(Inst::Return { values: vec![ValueId::new(0)] }),
        ];
        f.blocks.push(block);
        module.functions.push(f);
        module
    }

    fn const_of(module: &Module) -> &Constant {
        match &module.functions[0].blocks[0].body[0].inst {
            Inst::Const { value, .. } => value,
            other => panic!("expected a const, got {other:?}"),
        }
    }

    fn ints(values: &[i128]) -> Vec<Constant> {
        values.iter().map(|v| Constant::Int(*v)).collect()
    }

    #[test]
    fn a_uniform_list_becomes_a_splat_and_the_module_validates() {
        let mut module = module_with_const(
            |m| Ty::Array(m.add_type(Ty::U8).expect("Module::add_type: test fixture"), 4),
            Constant::Array(ints(&[0, 0, 0, 0])),
        );
        assert!(!trust_ir_build::validate_module(&module).is_empty(), "the list is refused");
        respell_uniform_arrays(&mut module);
        assert_eq!(const_of(&module), &Constant::splat(Constant::Int(0), 4));
        let errors = trust_ir_build::validate_module(&module);
        assert!(errors.is_empty(), "{errors:?}");
    }

    #[test]
    fn a_non_uniform_list_and_the_short_lists_are_left_as_written() {
        for values in [ints(&[1, 2, 1]), ints(&[7]), ints(&[])] {
            let n = values.len() as u64;
            let mut module = module_with_const(
                |m| Ty::Array(m.add_type(Ty::U8).expect("Module::add_type: test fixture"), n),
                Constant::Array(values.clone()),
            );
            respell_uniform_arrays(&mut module);
            assert_eq!(const_of(&module), &Constant::Array(values));
        }
    }

    #[test]
    fn nested_arrays_respell_bottom_up_and_bytes_of_one_value_are_a_splat() {
        let mut module = module_with_const(
            |m| {
                let byte = m.add_type(Ty::U8).expect("Module::add_type: test fixture");
                let row = m.add_type(Ty::Array(byte, 2)).expect("Module::add_type: test fixture");
                Ty::Array(row, 2)
            },
            Constant::Array(vec![
                Constant::Bytes { data: vec![9, 9], utf8: false },
                Constant::Array(ints(&[9, 9])),
            ]),
        );
        respell_uniform_arrays(&mut module);
        let row = Constant::splat(Constant::Int(9), 2);
        assert_eq!(const_of(&module), &Constant::splat(row, 2));
        let errors = trust_ir_build::validate_module(&module);
        assert!(errors.is_empty(), "{errors:?}");
    }

    #[test]
    fn an_array_inside_a_tuple_is_reached_and_a_utf8_payload_is_not_an_array() {
        let mut module = module_with_const(
            |m| {
                Ty::Tuple(vec![
                    Ty::I32,
                    Ty::Array(m.add_type(Ty::I32).expect("Module::add_type: test fixture"), 3),
                ])
            },
            Constant::Aggregate(vec![Constant::Int(1), Constant::Array(ints(&[5, 5, 5]))]),
        );
        respell_uniform_arrays(&mut module);
        assert_eq!(
            const_of(&module),
            &Constant::Aggregate(vec![Constant::Int(1), Constant::splat(Constant::Int(5), 3)])
        );
        let text = Constant::Bytes { data: b"aa".to_vec(), utf8: true };
        let mut module = module_with_const(
            |m| Ty::Array(m.add_type(Ty::U8).expect("Module::add_type: test fixture"), 2),
            text.clone(),
        );
        respell_uniform_arrays(&mut module);
        assert_eq!(const_of(&module), &text);
    }
}
