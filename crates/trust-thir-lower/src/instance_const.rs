//! Trust: transport an actual, already evaluated scalar const argument into source IR.
//! No MIR body, evaluation fallback, default value, admission token or proof authority.

use rustc_abi::Size;
use rustc_middle::ty::{self, TypeVisitableExt};
use rustc_span::def_id::DefId;

use super::{Constant, LowerCx, RustcTy, Ty, int_scalar_bits, integer_constant_from_bits};

impl<'a, 'tcx> LowerCx<'a, 'tcx> {
    pub(super) fn instance_const_value(
        &mut self,
        expr_ty: RustcTy<'tcx>,
        def_id: DefId,
        index: u32,
    ) -> Result<(Ty, Constant), &'static str> {
        let args = self.mono_args.ok_or("ConstParam(no instance arguments)")?;
        if self.template.is_some() || args.has_non_region_param() {
            return Err("ConstParam(instance arguments incomplete)");
        }
        let tcx = self.tcx;
        let generics = tcx.generics_of(self.body_def);
        let position = index as usize;
        if args.len() != generics.count()
            || position >= generics.count()
            || generics.param_def_id_to_index(tcx, def_id) != Some(index)
        {
            return Err("ConstParam(instance parameter binding)");
        }
        // param_at includes inherited owner parameters, and is only indexed after the bound.
        let parameter = generics.param_at(position, tcx);
        if parameter.def_id != def_id
            || parameter.index != index
            || !matches!(parameter.kind, ty::GenericParamDefKind::Const { .. })
        {
            return Err("ConstParam(instance parameter kind or owner)");
        }
        let argument = args
            .get(position)
            .and_then(|argument| argument.as_const())
            .ok_or("ConstParam(instance argument kind)")?;
        // A parameter, unevaluated/alias expression, inference or error value is not a literal.
        // In particular, do not evaluate a different definition or substitute zero on failure.
        let value = argument.try_to_value().ok_or("ConstParam(instance value unavailable)")?;
        let expected = self.monomorphize(expr_ty);
        let declared = tcx.type_of(def_id).instantiate_identity().skip_normalization();
        let declared = self.monomorphize(declared);
        if expected.has_non_region_param()
            || declared.has_non_region_param()
            || declared != expected
            || value.ty != expected
        {
            return Err("ConstParam(instance source type disagreement)");
        }
        let source_bits = match expected.kind() {
            ty::Bool => 8,
            ty::Char => 32,
            ty::Int(ty::IntTy::I8) | ty::Uint(ty::UintTy::U8) => 8,
            ty::Int(ty::IntTy::I16) | ty::Uint(ty::UintTy::U16) => 16,
            ty::Int(ty::IntTy::I32) | ty::Uint(ty::UintTy::U32) => 32,
            ty::Int(ty::IntTy::I64) | ty::Uint(ty::UintTy::U64) => 64,
            ty::Int(ty::IntTy::I128) | ty::Uint(ty::UintTy::U128) => 128,
            ty::Int(ty::IntTy::Isize) | ty::Uint(ty::UintTy::Usize) => {
                tcx.data_layout.pointer_size().bits()
            }
            _ => return Err("ConstParam(instance non-scalar source type)"),
        };
        let mapped =
            super::scalar_ret_ty(expected).ok_or("ConstParam(instance scalar type mapping)")?;
        let leaf = value.try_to_leaf().ok_or("ConstParam(instance non-scalar value)")?;
        let constant = scalar_value(&mapped, leaf, source_bits)?;
        Ok((mapped, constant))
    }
}

/// ScalarInt's stored width, the concrete source type and the IR value model must all agree.
/// Reuse the producer's canonical signed/u128 constructor only after checking that boundary.
fn scalar_value(ty: &Ty, value: ty::ScalarInt, source_bits: u64) -> Result<Constant, &'static str> {
    let model_bits = match ty {
        Ty::Bool => 8,
        Ty::Char => 32,
        _ => u64::from(int_scalar_bits(ty).ok_or("ConstParam(instance non-scalar IR type)")?.0),
    };
    if source_bits != model_bits || value.size().bits() != source_bits {
        return Err("ConstParam(instance scalar width disagreement)");
    }
    let raw = value.to_bits(Size::from_bits(source_bits));
    match ty {
        Ty::Bool => match raw {
            0 => Ok(Constant::Bool(false)),
            1 => Ok(Constant::Bool(true)),
            _ => Err("ConstParam(instance invalid bool value)"),
        },
        Ty::Char => u32::try_from(raw)
            .ok()
            .and_then(char::from_u32)
            .map(|_| Constant::Int(raw as i128))
            .ok_or("ConstParam(instance invalid char value)"),
        _ => {
            let (bits, signed) = int_scalar_bits(ty).ok_or("ConstParam(instance integer type)")?;
            Ok(integer_constant_from_bits(raw, signed, bits))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn leaf(raw: u128, bits: u64) -> ty::ScalarInt {
        ty::ScalarInt::try_from_uint(raw, Size::from_bits(bits)).unwrap()
    }

    #[test]
    fn concrete_integer_values_keep_width_sign_and_upper_u128() {
        for value in [0, 7, 19, u64::MAX] {
            assert_eq!(
                scalar_value(&Ty::U64, leaf(u128::from(value), 64), 64),
                Ok(Constant::Int(i128::from(value)))
            );
        }
        assert_eq!(scalar_value(&Ty::I8, leaf(255, 8), 8), Ok(Constant::Int(-1)));
        assert_eq!(scalar_value(&Ty::U8, leaf(255, 8), 8), Ok(Constant::Int(255)));
        assert_eq!(scalar_value(&Ty::I128, leaf(1 << 127, 128), 128), Ok(Constant::Int(i128::MIN)));
        assert_eq!(
            scalar_value(&Ty::U128, leaf(u128::MAX, 128), 128),
            Ok(Constant::u128(u128::MAX))
        );
    }

    #[test]
    fn bool_and_char_values_require_their_valid_domain() {
        assert_eq!(scalar_value(&Ty::Bool, leaf(0, 8), 8), Ok(Constant::Bool(false)));
        assert_eq!(scalar_value(&Ty::Bool, leaf(1, 8), 8), Ok(Constant::Bool(true)));
        assert!(scalar_value(&Ty::Bool, leaf(2, 8), 8).is_err());
        assert_eq!(scalar_value(&Ty::Char, leaf(0x10ffff, 32), 32), Ok(Constant::Int(0x10ffff)));
        for invalid in [0xd800, 0xdfff, 0x110000] {
            assert!(scalar_value(&Ty::Char, leaf(invalid, 32), 32).is_err());
        }
    }

    #[test]
    fn unknown_carriers_and_width_disagreements_never_supply_a_constant() {
        for ty in [Ty::Unit, Ty::Ptr, Ty::F64] {
            assert!(scalar_value(&ty, leaf(7, 64), 64).is_err());
        }
        assert!(scalar_value(&Ty::U64, leaf(7, 32), 64).is_err());
        assert!(scalar_value(&Ty::U8, leaf(7, 64), 8).is_err());
        assert!(scalar_value(&Ty::U64, leaf(7, 64), 32).is_err());
        assert!(scalar_value(&Ty::Usize, leaf(7, 32), 32).is_err());
        assert!(scalar_value(&Ty::U8, leaf(7, 8), 0).is_err());
    }
}
