//! Runtime-only scalar ABI comparison through the complete native classifier.
//! This is neither an original-source witness nor call-event placement P.
//! In particular, FP and stack locations have no representation in P and earn no proof.

use trust_cg_lower::abi::{AArch64AbiVariant, AppleAArch64ABI, ArgLocation, PReg, gpr};
use trust_cg_lower::types::Type;
use trust_ir::Ty;

/// Demand on the integer and shared f32/f64 banks, including overflow arguments.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct RegisterUse {
    /// Integer/pointer arguments; floating-point arguments never count here.
    pub gpr: usize,
    /// Floating-point arguments; f32/f64 alias the same bank.
    pub fp: usize,
}

const INTEGER_ARGS: [PReg; 8] =
    [gpr::X0, gpr::X1, gpr::X2, gpr::X3, gpr::X4, gpr::X5, gpr::X6, gpr::X7];

fn scalar(ty: &Ty) -> Result<Type, String> {
    match ty {
        Ty::I8 | Ty::U8 => Ok(Type::I8),
        Ty::I16 | Ty::U16 => Ok(Type::I16),
        Ty::I32 | Ty::U32 | Ty::Char => Ok(Type::I32),
        Ty::I64 | Ty::U64 | Ty::Isize | Ty::Usize | Ty::Ptr => Ok(Type::I64),
        Ty::F32 => Ok(Type::F32),
        Ty::F64 => Ok(Type::F64),
        _ => Err("source scalar ABI profile requires direct integer/pointer/f32/f64 scalars".into()),
    }
}

fn check_locations(
    types: &[Type],
    actual: &[ArgLocation],
    result: bool,
) -> Result<RegisterUse, String> {
    if types.len() != actual.len() || (result && types.len() > 1) {
        return Err("native scalar classifier changed the explicit signature population".into());
    }
    let mut used = RegisterUse::default();
    let mut stack = 0i64;
    for (ty, location) in types.iter().zip(actual) {
        let register = match ty {
            Type::F32 => {
                let reg = AppleAArch64ABI::s_arg_regs().get(used.fp).copied();
                used.fp += 1;
                reg
            }
            Type::F64 => {
                let reg = AppleAArch64ABI::d_arg_regs().get(used.fp).copied();
                used.fp += 1;
                reg
            }
            Type::I8 | Type::I16 | Type::I32 if result => {
                used.gpr += 1;
                Some(gpr::W0)
            }
            Type::I8 | Type::I16 | Type::I32 | Type::I64 => {
                let reg = INTEGER_ARGS.get(used.gpr).copied();
                used.gpr += 1;
                reg
            }
            _ => {
                return Err("native scalar classifier received an unsupported source carrier".into());
            }
        };
        let expected = if let Some(reg) = register {
            ArgLocation::Reg(reg)
        } else if !result {
            // Darwin fixed scalar arguments use their natural size/alignment,
            // in source order across both independently exhausted banks. This
            // comparison deliberately does not reuse the classifier's packing
            // helper: an AAPCS64 eight-byte-slot result must fail here.
            let bytes = i64::from(ty.bytes());
            stack = stack.checked_add(bytes - 1)
                .map(|offset| offset / bytes * bytes)
                .ok_or("source scalar stack offset overflow")?;
            let offset = stack;
            stack = stack.checked_add(bytes).ok_or("source scalar stack extent overflow")?;
            ArgLocation::Stack { offset, size: ty.bytes() }
        } else {
            return Err("source scalar result cannot use a stack argument slot".into());
        };
        if expected != *location {
            return Err("native scalar ABI differs in bank, width, position or stack packing".into());
        }
    }
    Ok(used)
}

/// Compare a source-checked direct-scalar signature with the selected native
/// Darwin classifier, including both banks, naturally packed fixed stack
/// arguments and the result's typed register. The caller independently validates
/// actual rustc source types/FnAbi, attributes, convention, target and immutable
/// source/module identity. Pair, aggregate and indirect carriers stay refused.
pub fn darwin_scalar(target: &str, params: &[Ty], returns: &[Ty]) -> Result<RegisterUse, String> {
    if target != "aarch64-apple-darwin" {
        return Err("source scalar ABI is not qualified for this target".into());
    }
    let variant = AArch64AbiVariant::from_target_triple(target).map_err(|e| e.to_string())?;
    let params = params.iter().map(scalar).collect::<Result<Vec<_>, _>>()?;
    let returns = returns.iter().map(scalar).collect::<Result<Vec<_>, _>>()?;
    let used =
        check_locations(&params, &AppleAArch64ABI::classify_params_with(variant, &params), false)?;
    check_locations(&returns, &AppleAArch64ABI::classify_returns(&returns), true)?;
    Ok(used)
}

#[cfg(test)]
mod tests;
