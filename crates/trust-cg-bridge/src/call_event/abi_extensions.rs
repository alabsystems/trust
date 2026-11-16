//! The bounded Darwin A64 C-u8/C-u16/C-i8/C-i16 physical extension contract.
//!
//! A source scalar value alone imposes NO condition on the rest of an incoming
//! register. Only a C boundary, qualified target and exact P(width8-or16,Zext-or-Sext)
//! authorize the 32-bit contract below. This small-integer contract does not
//! restrict Rust AbiExt::None; Bool call results are refused independently of P.
//! No helper here grants a grade: the caller must connect every entry/call/
//! return boundary, include the model equations in the kernel conjunction,
//! retain the memory Unknown guard and close all ordinary CER obligations.
//! A Rust `bool` result (P {Gpr0,32,Zext}) is not part of that contract: its
//! definition's own certificate must prove its 0/1 range (BOOL-RET-EDGE-1 C2).
//! Bool call-edge transport remains refused pending a Lean-owned relation;
//! no constructed post-call state is substituted for that missing relation.

use std::collections::BTreeSet;

use trust_ir::{CallingConv, Endianness, Module, Ty};
use trust_machine_sem::MachineState;
use trust_types::{Formula, Sort};

use super::{AbiExt, FnPlacement, ParamPlace, ReturnPlace, ScalarPlace, Slot};

fn b(f: Formula) -> Box<Formula> {
    Box::new(f)
}
fn bv(value: u64, width: u32) -> Formula {
    Formula::BitVec { value: i128::from(value), width }
}
fn extract(f: Formula, high: u32, low: u32) -> Formula {
    Formula::BvExtract { inner: b(f), high, low }
}
fn check_width(f: &Formula, width: u32) -> Result<(), String> {
    match trust_types::smt_logic::check_formula_sort(f) {
        Ok(Sort::BitVec(w)) if w == width => Ok(()),
        other => Err(format!("ABI value is not exactly BV{width}: {other:?}")),
    }
}

/// One physical obligation retained alongside the exact placement digest.
#[derive(Clone, Debug, serde::Serialize)]
pub struct SlotContract {
    pub parameter: Option<usize>,
    pub slot: Slot,
    pub declared_width: u32,
    pub required_width: u32,
    pub extension: AbiExt,
}

/// Explicit ABI/domain evidence; this record is not itself a certificate.
#[derive(Clone, Debug, serde::Serialize)]
pub struct ContractRecord {
    pub schema: &'static str,
    pub target: String,
    pub calling_convention: &'static str,
    pub placement_sha256: String,
    pub slots: Vec<SlotContract>,
    pub entry_condition: &'static str,
    pub entry_parameterization: &'static str,
    pub upper_32_bits: &'static str,
}

/// Qualified only by the producer convention, recorded target and P. Reading P
/// from the actual source FnAbi remains the existing F1-OUTPUT-TV trust boundary.
/// Nothing synthesizes/rewrites a FnAbi or erases its width/extension flags.
#[derive(Clone, Debug, Default)]
pub(super) struct Plan {
    parameters: Vec<(u8, u32, AbiExt)>,
    record: Option<ContractRecord>,
}

pub(super) fn qualified_target(module: &Module) -> bool {
    module.target_info.as_ref().is_some_and(|target| {
        matches!(target.triple.as_str(), "aarch64-apple-darwin" | "arm64-apple-macosx")
            && target.pointer_size == 8
            && target.endianness == Endianness::Little
            && target.abi.is_none()
    })
}

/// Exact supported unsigned types; wider extension contracts remain
/// outside this model. Width and extension flags are never rewritten.
pub(super) fn unsigned_small_width(ty: &Ty) -> Option<u32> {
    match ty {
        Ty::U8 => Some(8),
        Ty::U16 => Some(16),
        _ => None,
    }
}
pub(super) fn supports_zext(module: &Module, conv: CallingConv, ty: &Ty, width: u32) -> bool {
    conv == CallingConv::C && qualified_target(module) && unsigned_small_width(ty) == Some(width)
}

pub(super) fn signed_small_width(ty: &Ty) -> Option<u32> {
    match ty {
        Ty::I8 => Some(8),
        Ty::I16 => Some(16),
        _ => None,
    }
}
pub(super) fn supports_sext(module: &Module, conv: CallingConv, ty: &Ty, width: u32) -> bool {
    conv == CallingConv::C && qualified_target(module) && signed_small_width(ty) == Some(width)
}
fn small_contract(ty: &Ty) -> Option<(u32, AbiExt)> {
    unsigned_small_width(ty)
        .map(|w| (w, AbiExt::Zext))
        .or_else(|| signed_small_width(ty).map(|w| (w, AbiExt::Sext)))
}

impl Plan {
    /// Read the full boundary BEFORE any physical-width helper can be used.
    /// Unsupported extended pairs, signed/other widths and absent target facts
    /// refuse. A known Darwin C small scalar boundary must retain its actual extension flag.
    pub fn new(
        module: &Module,
        conv: CallingConv,
        params: &[Ty],
        returns: &[Ty],
        placement: &FnPlacement,
        is_definition: bool,
    ) -> Result<Self, String> {
        if params.len() != placement.params.len() {
            return Err(format!(
                "{} parameter(s) but P places {}",
                params.len(),
                placement.params.len()
            ));
        }
        // Refusal-only: generic AbiExt::None transport supplies no Lean-owned
        // relation from a Bool callee's C1/C2 to its caller. Check the logical
        // result before reading P so stripping an extension cannot reopen it.
        if !is_definition && returns.contains(&Ty::Bool) {
            return Err("Bool call results require a Lean-owned callee-to-caller relation \
                 (BOOL-RET-EDGE-1 withdrawn)"
                .into());
        }
        let qualified = qualified_target(module);
        let mut slots = Vec::new();
        let mut parameters = Vec::new();
        let mut read = |ty: &Ty,
                        scalar: &ScalarPlace,
                        parameter: Option<usize>|
         -> Result<(), String> {
            let declared = small_contract(ty);
            let declared_width = declared.map(|(width, _)| width);
            let required_extension = declared.map(|(_, extension)| extension);
            let is_c_small = conv == CallingConv::C && declared.is_some();
            if is_c_small && module.target_info.is_none() {
                return Err("a C-small-scalar boundary has no recorded target ABI authority".into());
            }
            let darwin = module.target_info.as_ref().is_some_and(|target| {
                matches!(target.triple.as_str(), "aarch64-apple-darwin" | "arm64-apple-macosx")
            });
            if is_c_small && darwin && !qualified {
                return Err("Darwin C-small-scalar target metadata is inconsistent".into());
            }
            if is_c_small && qualified && Some(scalar.ext) != required_extension {
                return Err("Darwin C small scalar P lacks its actual extension contract".into());
            }
            if scalar.ext == AbiExt::None {
                return Ok(());
            }
            // Legacy own-definition Bool result only, with its C2 obligation.
            // Call edges never receive this exemption.
            if is_definition
                && parameter.is_none()
                && *ty == Ty::Bool
                && scalar.width == 32
                && scalar.ext == AbiExt::Zext
            {
                return Ok(());
            }
            if !is_c_small
                || !qualified
                || declared_width != Some(scalar.width)
                || Some(scalar.ext) != required_extension
            {
                return Err(
                    "only qualified Darwin C unsigned/signed8/16 extension to32 is modeled".into(),
                );
            }
            let Slot::Gpr(register) = scalar.slot else {
                return Err("C-small-scalar extension requires a scalar integer register".into());
            };
            if register >= 8 || (parameter.is_none() && register != 0) {
                return Err(
                    "C-small-scalar extension is outside the audited register boundary".into()
                );
            }
            if parameter.is_some() {
                parameters.push((register, scalar.width, scalar.ext));
            }
            slots.push(SlotContract {
                parameter,
                slot: scalar.slot,
                declared_width: scalar.width,
                required_width: 32,
                extension: scalar.ext,
            });
            Ok(())
        };
        for (index, (ty, place)) in params.iter().zip(&placement.params).enumerate() {
            match place {
                ParamPlace::Scalar(s) => read(ty, s, Some(index))?,
                ParamPlace::Pair(a, c) if a.ext != AbiExt::None || c.ext != AbiExt::None => {
                    return Err(
                        "extended aggregate lanes are not C-small-scalar scalar boundaries".into(),
                    );
                }
                _ => {}
            }
        }
        match (returns, &placement.ret) {
            ([ty], ReturnPlace::Scalar(s)) => read(ty, s, None)?,
            (_, ReturnPlace::Scalar(s)) if s.ext != AbiExt::None => {
                return Err("extended result does not have one declared logical value".into());
            }
            _ => {}
        }
        if slots.is_empty() {
            return Ok(Self::default());
        }
        // Do not let one qualified unsigned projection also constrain another
        // logical parameter through malformed duplicate/overlapping P slots.
        let mut registers = BTreeSet::new();
        for place in &placement.params {
            let scalars = match place {
                ParamPlace::Ignore => vec![],
                ParamPlace::Scalar(s) => vec![s],
                ParamPlace::Pair(a, c) => vec![a, c],
            };
            for scalar in scalars {
                let regs = match scalar.slot {
                    Slot::Gpr(r) => vec![r],
                    Slot::GprPair { lo, hi } => vec![lo, hi],
                    _ => {
                        return Err(
                            "C-small-scalar contract does not cover stack/indirect placement"
                                .into(),
                        );
                    }
                };
                for register in regs {
                    if !registers.insert(register) {
                        return Err("overlapping ABI argument slots".into());
                    }
                }
            }
        }
        let target = module
            .target_info
            .as_ref()
            .ok_or("C-small-scalar contract target is absent")?
            .triple
            .clone();
        Ok(Self {
            parameters,
            record: Some(ContractRecord {
                schema: if slots
                    .iter()
                    .all(|slot| slot.extension == AbiExt::Sext && slot.declared_width == 8)
                {
                    "trust-cg-bridge.darwin-c-i8-extension.v1"
                } else if slots
                    .iter()
                    .all(|slot| slot.extension == AbiExt::Sext && slot.declared_width == 16)
                {
                    "trust-cg-bridge.darwin-c-i16-extension.v1"
                } else if slots.iter().any(|slot| slot.extension == AbiExt::Sext) {
                    "trust-cg-bridge.darwin-c-small-extension.v1"
                } else if slots.iter().all(|slot| slot.declared_width == 8) {
                    "trust-cg-bridge.darwin-c-u8-extension.v1"
                } else {
                    "trust-cg-bridge.darwin-c-u16-extension.v1"
                },
                target,
                calling_convention: "C",
                placement_sha256: placement.digest(),
                entry_condition: if slots.iter().any(|s| s.extension == AbiExt::Sext) {
                    "each listed parameter low32 equals its declared Zext/Sext value"
                } else {
                    "each listed parameter Xr[31:declared_width] == 0"
                },
                entry_parameterization: if slots.iter().any(|s| s.extension == AbiExt::Sext) {
                    "preserve raw high32; replace low32 with exact declared Zext/Sext (both sides)"
                } else {
                    "Xr & (0xffffffff00000000 | low_declared_width_mask) (both sides)"
                },
                slots,
                upper_32_bits: "unrestricted at entry and after a call",
            }),
        })
    }

    pub fn record(&self) -> Option<ContractRecord> {
        self.record.clone()
    }

    /// The range is exactly all legal C-small-scalar register inputs. In particular the
    /// mask does not narrow high32. See the kernel equations below.
    fn project(value: Formula, width: u32, extension: AbiExt) -> Formula {
        if extension == AbiExt::Sext {
            return Formula::BvOr(
                b(Formula::BvAnd(b(value.clone()), b(bv(0xffff_ffff_0000_0000, 64)), 64)),
                b(Formula::BvZeroExt(
                    b(Formula::BvSignExt(b(extract(value, width - 1, 0)), 32 - width)),
                    32,
                )),
                64,
            );
        }
        let mask = 0xffff_ffff_0000_0000 | ((1u64 << width) - 1);
        Formula::BvAnd(b(value), b(bv(mask, 64)), 64)
    }

    pub fn apply_entry(&self, state: &mut MachineState) {
        for (register, width, extension) in &self.parameters {
            state.gpr[usize::from(*register)] =
                Self::project(state.gpr[usize::from(*register)].clone(), *width, *extension);
        }
    }

    pub fn source_entry(&self, formula: Formula) -> Formula {
        formula.map(&mut |term| {
            let parameter = match &term {
                Formula::Var(name, Sort::BitVec(64)) => {
                    self.parameters.iter().find(|(r, _, _)| name == &format!("X{r}"))
                }
                _ => None,
            };
            match parameter {
                Some((_, width, extension)) => Self::project(term, *width, *extension),
                None => term,
            }
        })
    }

    /// Unconditional kernel equations: the projection produces valid entries,
    /// preserves the declared low bits/high32, and FIXES EVERY legal input. Thus it
    /// cannot hide an invalid-input counterexample by shrinking the legal domain.
    pub fn entry_equations(&self) -> Vec<(Formula, Formula)> {
        let mut equations = Vec::new();
        for (register, width, extension) in &self.parameters {
            let raw = Formula::Var(format!("X{register}"), Sort::BitVec(64));
            let projected = Self::project(raw.clone(), *width, *extension);
            let physical = if *extension == AbiExt::Sext {
                Formula::BvSignExt(b(extract(raw.clone(), *width - 1, 0)), 32 - *width)
            } else {
                Formula::BvZeroExt(b(extract(raw.clone(), *width - 1, 0)), 32 - *width)
            };
            let signed = *extension == AbiExt::Sext;
            let valid = if signed {
                Formula::Eq(b(extract(raw.clone(), 31, 0)), b(physical.clone()))
            } else {
                Formula::Eq(b(extract(raw.clone(), 31, *width)), b(bv(0, 32 - *width)))
            };
            let validity_equation = if signed {
                (extract(projected.clone(), 31, 0), physical)
            } else {
                (extract(projected.clone(), 31, *width), bv(0, 32 - *width))
            };
            equations.extend([
                validity_equation,
                (extract(projected.clone(), *width - 1, 0), extract(raw.clone(), *width - 1, 0)),
                (extract(projected.clone(), 63, 32), extract(raw.clone(), 63, 32)),
                // Equivalent to valid(raw) => project(raw)==raw, and stronger:
                // the fixed points are EXACTLY the legal C input domain. The
                // one-bit equality avoids a redundant64-bit mux proof.
                (
                    Formula::Ite(b(Formula::Eq(b(projected), b(raw))), b(bv(1, 1)), b(bv(0, 1))),
                    Formula::Ite(b(valid), b(bv(1, 1)), b(bv(0, 1))),
                ),
            ]);
        }
        equations
    }
}

/// Only call after Plan/check_placement has authenticated the complete boundary.
/// P's declared width stays8/16; the contract makes32 physical bits observable.
pub(super) fn physical_width(scalar: &ScalarPlace) -> u32 {
    if matches!(scalar.width, 8 | 16) && matches!(scalar.ext, AbiExt::Zext | AbiExt::Sext) {
        32
    } else {
        scalar.width
    }
}

pub(super) fn physical_value(scalar: &ScalarPlace, logical: Formula) -> Result<Formula, String> {
    check_width(&logical, scalar.width)?;
    Ok(if physical_width(scalar) == scalar.width {
        logical
    } else {
        if scalar.ext == AbiExt::Sext {
            Formula::BvSignExt(b(logical), 32 - scalar.width)
        } else {
            Formula::BvZeroExt(b(logical), 32 - scalar.width)
        }
    })
}

/// Shared logical R8/R16 plus the callee's full W0 promise. X0[63:32] remains fresh;
/// zeroing it would silently strengthen the external/CoEmitted ABI assumption.
pub(super) fn post_call_unsigned(
    result: Formula,
    high: Formula,
    width: u32,
) -> Result<Formula, String> {
    if !matches!(width, 8 | 16) {
        return Err("unsupported unsigned result width".into());
    }
    check_width(&result, width)?;
    check_width(&high, 64)?;
    Ok(Formula::BvOr(
        b(Formula::BvAnd(b(high), b(bv(0xffff_ffff_0000_0000, 64)), 64)),
        b(Formula::BvZeroExt(b(result), 64 - width)),
        64,
    ))
}

/// Signed C returns promise low W0 sign extension only; upper X0 remains fresh.
pub(super) fn post_call_signed(
    result: Formula,
    high: Formula,
    width: u32,
) -> Result<Formula, String> {
    if !matches!(width, 8 | 16) {
        return Err("unsupported signed result width".into());
    }
    check_width(&result, width)?;
    check_width(&high, 64)?;
    Ok(Formula::BvOr(
        b(Formula::BvAnd(b(high), b(bv(0xffff_ffff_0000_0000, 64)), 64)),
        b(Formula::BvZeroExt(b(Formula::BvSignExt(b(result), 32 - width)), 32)),
        64,
    ))
}

/// The own-definition Bool result shape that requires the C2 range item.
/// Recognizing this shape grants no call-edge transport.
pub(super) fn is_bool_result(ret: &ReturnPlace) -> bool {
    matches!(
        ret,
        ReturnPlace::Scalar(ScalarPlace { slot: Slot::Gpr(0), width: 32, ext: AbiExt::Zext })
    )
}

#[cfg(test)]
#[path = "abi_extensions/tests.rs"]
mod tests;

/// The same logical low value under Rust/other unextended small returns. Every
/// padding bit stays independently fresh; neither48 nor56 bits acquire a C
/// extension guarantee.
pub(super) fn post_call_unextended_small(
    result: Formula,
    high: Formula,
    width: u32,
) -> Result<Formula, String> {
    if !matches!(width, 8 | 16) {
        return Err("unsupported unextended result width".into());
    }
    check_width(&result, width)?;
    check_width(&high, 64)?;
    Ok(Formula::BvOr(
        b(Formula::BvAnd(b(high), b(bv(!((1u64 << width) - 1), 64)), 64)),
        b(Formula::BvZeroExt(b(result), 64 - width)),
        64,
    ))
}

/// A bare tail branch cannot repair unspecified padding from a weaker return
/// contract. Refuse this abstraction rather than invent an extension guarantee.
pub(super) fn check_tail_transport(own: &ReturnPlace, callee: &ReturnPlace) -> Result<(), String> {
    if is_bool_result(own) && !is_bool_result(callee) {
        return Err("bool tail return cannot inherit its 0/1 zero extension from an unspecified \
                    callee result"
            .into());
    }
    if let ReturnPlace::Scalar(own) = own {
        if matches!(own.width, 8 | 16) && matches!(own.ext, AbiExt::Zext | AbiExt::Sext) {
            let ReturnPlace::Scalar(callee) = callee else {
                return Err("C-small-scalar tail return has no scalar callee contract".into());
            };
            if callee.slot != Slot::Gpr(0) || callee.width != own.width || callee.ext != own.ext {
                return Err(if own.ext == AbiExt::Zext {
                    "C-u8/u16 tail return cannot inherit zero extension from unspecified callee padding"
                } else {
                    "C-i8/i16 tail return cannot inherit sign extension from unspecified callee padding"
                }.into());
            }
        }
    }
    Ok(())
}

/// Havocked result padding is permitted by the callee ABI but is not a
/// constructive observation of its actual bytes. A SAT depending on it is an
/// unclosed abstraction, not automatically a concrete miscompile.
pub(super) fn observes_callee_padding(formula: &Formula) -> bool {
    let mut found = false;
    formula.visit(&mut |term| {
        if let Formula::Var(name, _) = term {
            found |= name.starts_with("CER_RHI@");
        }
    });
    found
}

#[cfg(test)]
#[path = "abi_extensions/u16_tests.rs"]
mod u16_tests;

#[cfg(test)]
#[path = "abi_extensions/signed_tests.rs"]
mod signed_tests;

#[cfg(test)]
#[path = "abi_extensions/bool_edge_tests.rs"]
mod bool_edge_tests;
