//! Actual Rustc const/layout answers required by the S consumer. These answers
//! grant no body, conservation, ABI, codegen or proof authority. Full S admission
//! still needs its independent evidence, type-table and protected appender route.

use rustc_hir::def::DefKind;
use rustc_middle::mir;
use rustc_middle::ty::{self, TyCtxt, TypeVisitableExt};
use trust_ir::template::HostKey;
use trust_ir::{Constant, Ty};

use super::{Result, err};
use crate::template_key::{HoleKey, KeyConstItem};

fn normalized<'tcx, T>(tcx: TyCtxt<'tcx>, value: T) -> Result<T>
where
    T: ty::TypeFoldable<TyCtxt<'tcx>>,
{
    crate::producer_try_normalize(tcx, ty::TypingEnv::fully_monomorphized(), value)
        .map_err(|_| err("template const host source normalization failed"))
}

/// Resolve original-owner terms under the actual concrete Rust instance. The
/// key's full positional map is reconstructed by the existing checked key codec;
/// no value, field offset, type or symbol is guessed from an IR signature.
pub fn resolve<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
    key: &HostKey,
    expected: &Ty,
) -> Result<Constant> {
    crate::instance_admission::refuse_inside_producer_lowering()
        .map_err(|_| err("template const evaluation is unavailable during source lowering"))?;
    if !matches!(instance.def, ty::InstanceKind::Item(_))
        || !matches!(tcx.def_kind(instance.def_id()), DefKind::Fn | DefKind::AssocFn)
        || instance.args.len() != tcx.generics_of(instance.def_id()).count()
        || instance.args.has_non_region_param()
        || instance.args.has_non_region_infer()
        || instance.args.has_escaping_bound_vars()
    {
        return Err(err("template const host requires a concrete actual Rust Item"));
    }
    // Public host callers must not be able to forge a same-length Instance
    // argument list with different positional kinds or const declared types.
    crate::template_key::rustc::checked_call_key(
        tcx, instance.def_id(), instance.args, instance.def_id(),
    ).map_err(|e| err(e.to_string()))?;
    if !trust_ir::template::is_template_scalar(expected) {
        return Err(err("template const answer has a non-scalar requested type"));
    }
    let decoded = crate::template_key::decode(key).map_err(|e| err(e.to_string()))?;
    let HoleKey::Const(term) = &decoded else {
        return Err(err("template const host received a different hole-key kind"));
    };
    let env = ty::TypingEnv::fully_monomorphized();
    match &term {
        KeyConstItem::Assoc { .. } => {
            let (definition, args) = crate::template_key::rustc::associated_const_of_key(
                tcx,
                &decoded,
                instance.def_id(),
            )
            .map_err(|e| err(e.to_string()))?;
            let args = normalized(
                tcx,
                ty::EarlyBinder::bind(tcx, args)
                    .instantiate(tcx, instance.args)
                    .skip_normalization(),
            )?;
            if args.has_non_region_param()
                || args.has_non_region_infer()
                || args.has_escaping_bound_vars()
            {
                return Err(err("template associated constant arguments remain symbolic"));
            }
            let source = normalized(
                tcx,
                tcx.type_of(definition).instantiate(tcx, args).skip_normalization(),
            )?;
            if crate::scalar_ret_ty(source).as_ref() != Some(expected) {
                return Err(err(
                    "template associated constant actual Rust type differs from requested IR type",
                ));
            }
            // Rustc resolves the selected impl and evaluates its real constant.
            // CTFE remains permitted here until compile-path step9; no MIR body
            // is consumed as verification/codegen IR.
            let value = tcx
                .const_eval_resolve(
                    env,
                    mir::UnevaluatedConst { def: definition, args, promoted: None },
                    rustc_span::DUMMY_SP,
                )
                .map_err(|e| err(format!("template associated constant CTFE refused: {e:?}")))?;
            let scalar = value.try_to_scalar_int().ok_or_else(|| {
                err("template associated constant is not a provenance-free scalar")
            })?;
            let layout = tcx
                .layout_of(env.as_query_input(source))
                .map_err(|e| err(format!("template scalar layout: {e:?}")))?;
            if scalar.size() != layout.size {
                return Err(err("template scalar CTFE width differs from its actual Rust layout"));
            }
            scalar_bits(expected, scalar.to_bits(layout.size), layout.size.bits() as u32)
        }
        KeyConstItem::FieldOffset { adt, variant, field } => {
            if expected != &Ty::Usize {
                return Err(err("template field offset must have the target usize type"));
            }
            let source = crate::template_key::rustc::ty_of_key(tcx, adt, instance.def_id())
                .map_err(|e| err(e.to_string()))?;
            let source = normalized(
                tcx,
                ty::EarlyBinder::bind(tcx, source)
                    .instantiate(tcx, instance.args)
                    .skip_normalization(),
            )?;
            if source.has_non_region_param()
                || source.has_non_region_infer()
                || source.has_escaping_bound_vars()
            {
                return Err(err("template field-offset type remains symbolic"));
            }
            let ty::Adt(definition, _) = source.kind() else {
                return Err(err("template field offset does not name an actual Rust ADT"));
            };
            if !definition.is_struct() || *variant != 0 {
                return Err(err(
                    "template enum/union payload offsets require their qualified layout transport",
                ));
            }
            let field = *field as usize;
            if field >= definition.non_enum_variant().fields.len() {
                return Err(err("template field offset names an absent declared field"));
            }
            let layout = tcx
                .layout_of(env.as_query_input(source))
                .map_err(|e| err(format!("template field layout: {e:?}")))?;
            if layout.fields.count() != definition.non_enum_variant().fields.len() {
                return Err(err("template Rust field layout population mismatch"));
            }
            Ok(Constant::u128(u128::from(layout.fields.offset(field).bytes())))
        }
    }
}

/// The producer's integer spelling and the pinned IR float carrier semantics;
/// width, bool/char range and float payload roundtrips are checked explicitly.
fn scalar_bits(ty: &Ty, raw: u128, bits: u32) -> Result<Constant> {
    let bad = || err("template scalar value/width has no exact requested carrier");
    let fixed = match ty {
        Ty::I8 | Ty::U8 => Some(8),
        Ty::I16 | Ty::U16 => Some(16),
        Ty::I32 | Ty::U32 => Some(32),
        Ty::I64 | Ty::U64 => Some(64),
        Ty::I128 | Ty::U128 => Some(128),
        _ => None,
    };
    if fixed.is_some_and(|width| width != bits)
        || bits == 0
        || bits > 128
        || (bits < 128 && raw >> bits != 0)
        || (matches!(ty, Ty::Isize | Ty::Usize) && !matches!(bits, 32 | 64))
    {
        return Err(bad());
    }
    Ok(match ty {
        Ty::Bool if bits == 8 && raw <= 1 => Constant::Bool(raw == 1),
        Ty::Char if bits == 32 && u32::try_from(raw).ok().and_then(char::from_u32).is_some() => {
            Constant::Int(raw as i128)
        }
        Ty::I8 | Ty::I16 | Ty::I32 | Ty::I64 | Ty::I128 | Ty::Isize => {
            crate::integer_constant_from_bits(raw, true, bits)
        }
        Ty::U8 | Ty::U16 | Ty::U32 | Ty::U64 | Ty::U128 | Ty::Usize => {
            crate::integer_constant_from_bits(raw, false, bits)
        }
        Ty::F16 if bits == 16 => {
            let value = trust_ir::interpret::f16_bits_to_f64(raw as u16);
            if trust_ir::interpret::f64_to_f16_bits(value) != raw as u16 {
                return Err(bad());
            }
            Constant::Float(value)
        }
        Ty::F32 if bits == 32 => {
            let value = f64::from(f32::from_bits(raw as u32));
            if (value as f32).to_bits() != raw as u32 {
                return Err(bad());
            }
            Constant::Float(value)
        }
        Ty::F64 if bits == 64 => Constant::Float(f64::from_bits(raw as u64)),
        _ => return Err(bad()),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn scalar_types_widths_and_signedness_are_not_interchangeable() {
        assert_eq!(scalar_bits(&Ty::I8, 255, 8).unwrap(), Constant::Int(-1));
        assert_eq!(scalar_bits(&Ty::U8, 255, 8).unwrap(), Constant::Int(255));
        assert!(scalar_bits(&Ty::U8, 255, 64).is_err());
        assert!(scalar_bits(&Ty::U8, 256, 8).is_err());
        assert!(scalar_bits(&Ty::Bool, 2, 8).is_err());
        assert!(scalar_bits(&Ty::Char, 0xd800, 32).is_err());
        assert!(scalar_bits(&Ty::Usize, 1, 16).is_err());
        assert_eq!(scalar_bits(&Ty::U128, u128::MAX, 128).unwrap(), Constant::u128(u128::MAX));
    }
    #[test]
    fn f16_values_keep_exact_ieee_bits_and_signaling_nan_refuses() {
        for (raw, expected) in [
            (0x0000, 0u64),
            (0x8000, 0x8000000000000000),
            (0x3c00, 0x3ff0000000000000),
            (0xc000, 0xc000000000000000),
            (0x0001, 0x3e70000000000000),
            (0x7c00, 0x7ff0000000000000),
            (0x7e01, 0x7ff8040000000000),
        ] {
            let Constant::Float(value) = scalar_bits(&Ty::F16, raw, 16).unwrap() else {
                panic!("float carrier")
            };
            assert_eq!(value.to_bits(), expected);
        }
        assert!(
            scalar_bits(&Ty::F16, 0x7c01, 16).is_err(),
            "the IR narrowing quiets this signaling NaN"
        );
    }
}
