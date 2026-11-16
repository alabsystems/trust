//! Trust: source ABI agreement for the full Trust-IR native consumer.
//!
//! Read rustc's exact instance FnAbi and compare it with the unchanged emitted
//! signature and observed capture frame. No MIR lowering, ABI rewriting, layout
//! synthesis, source-license promotion or proof-grade change occurs here.

use rustc_abi::{BackendRepr, CanonAbi, Primitive};
use rustc_middle::ty::{self, Ty, TyCtxt};
use rustc_target::callconv::{ArgAbi, ArgAttribute, ArgAttributes, ArgExtension, FnAbi, PassMode};
use trust_ir::{CallingConv, FuncId, Module, Producer, Ty as IrTy};

#[path = "source_abi/agreement.rs"]
mod agreement;
#[path = "source_abi/module_carrier.rs"]
mod module_carrier;
#[path = "source_abi/foreign_declarations.rs"]
mod foreign_declarations;
pub(crate) use foreign_declarations::check as check_foreign_declarations;
use agreement::{Extension, Lane, ObservedFrame, RegisterUse, Scalar, Transport};

/// Retain the complete borrowed FnAbi, including pointee/value attributes.
/// They are Rust value preconditions, not permission to discard an extension
/// or change the placement. The native proof/output gate remains independent.
pub(crate) struct SourceAbiAgreement<'tcx, 'module> {
    source: &'module Module,
    function: FuncId,
    pub(crate) fn_abi: &'tcx FnAbi<'tcx, Ty<'tcx>>,
    pub(crate) placement: Option<trust_cg_bridge::call_event::FnPlacement>,
}

impl SourceAbiAgreement<'_, '_> {
    pub(crate) fn param_extensions(&self, tcx: TyCtxt<'_>) -> trust_cg_bridge::AbiParamExtensions {
        trust_cg_bridge::AbiParamExtensions {
            per_param: self
                .fn_abi
                .args
                .iter()
                .map(|arg| match &arg.mode {
                    PassMode::Direct(attrs) => Some(match attrs.arg_ext {
                        ArgExtension::None => trust_cg_bridge::AbiArgExtension::None,
                        ArgExtension::Zext => trust_cg_bridge::AbiArgExtension::Zext,
                        ArgExtension::Sext => trust_cg_bridge::AbiArgExtension::Sext,
                    }),
                    _ => None,
                })
                .collect(),
            caller_extends_to_bits: crate::caller_small_arg_extension_bits(&tcx.sess.target),
        }
    }
}

fn scalar(tcx: TyCtxt<'_>, value: rustc_abi::Scalar) -> Result<Scalar, String> {
    if !matches!(value, rustc_abi::Scalar::Initialized { .. }) {
        return Err("source ABI scalar is not initialized".into());
    }
    match value.primitive() {
        Primitive::Pointer(_) if value.size(&tcx).bits() == 64 => Ok(Scalar::Pointer),
        Primitive::Int(_, signed) if matches!(value.size(&tcx).bits(), 8 | 16 | 32 | 64) => {
            Ok(Scalar::Int { bits: value.size(&tcx).bits() as u32, signed })
        }
        Primitive::Float(rustc_abi::Float::F32) => Ok(Scalar::Float { bits: 32 }),
        Primitive::Float(rustc_abi::Float::F64) => Ok(Scalar::Float { bits: 64 }),
        _ => Err("source ABI has no audited native integer/pointer/f32/f64 scalar".into()),
    }
}

fn lane(tcx: TyCtxt<'_>, value: rustc_abi::Scalar, attrs: &ArgAttributes) -> Result<Lane, String> {
    Ok(Lane {
        scalar: scalar(tcx, value)?,
        extension: match attrs.arg_ext {
            ArgExtension::None => Extension::None,
            ArgExtension::Zext => Extension::Zext,
            ArgExtension::Sext => Extension::Sext,
        },
        inreg: attrs.contains(ArgAttribute::InReg),
    })
}

/// Source references and raw pointers must really have the observed thin
/// pointer representation. This is transport agreement only: the complete
/// original FnAbi retains their different validity and pointee attributes.
/// Wide pointers, aliases/newtypes and non-f32/f64 floating carriers stay refused.
fn source_scalar<'tcx>(tcx: TyCtxt<'tcx>, source: Ty<'tcx>) -> Result<Scalar, String> {
    let layout = tcx
        .layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(source))
        .map_err(|e| format!("source scalar layout failed: {e:?}"))?;
    let BackendRepr::Scalar(value) = layout.backend_repr else {
        return Err(format!("source type `{source}` is not a thin scalar"));
    };
    let actual = scalar(tcx, value)?;
    match (source.kind(), actual) {
        // Trust: an incoming raw address has the same physical pointer lane,
        // without acquiring any reference validity, aliasing or borrow rights.
        (ty::Ref(..) | ty::RawPtr(..), Scalar::Pointer)
            if layout.size.bytes() == 8 && layout.align.bytes() == 8 =>
        {
            Ok(actual)
        }
        (ty::Int(_) | ty::Uint(_) | ty::Char, Scalar::Int { .. }) => Ok(actual),
        (ty::Float(ty::FloatTy::F32), Scalar::Float { bits: 32 })
            if layout.size.bytes() == 4 && layout.align.bytes() == 4 => Ok(actual),
        (ty::Float(ty::FloatTy::F64), Scalar::Float { bits: 64 })
            if layout.size.bytes() == 8 && layout.align.bytes() == 8 => Ok(actual),
        _ => Err(format!("source ABI type `{source}` is outside the native source scalar lane")),
    }
}

fn closure_arg<'tcx>(
    tcx: TyCtxt<'tcx>,
    module: &Module,
    ir: &IrTy,
    arg: &ArgAbi<'tcx, Ty<'tcx>>,
) -> Result<usize, String> {
    // This is the measured two-word AArch64 transport. Other target classifiers
    // remain refused until their source aggregate placement is cross-checked.
    if tcx.sess.opts.target_triple.tuple() != "aarch64-apple-darwin" {
        return Err("source closure ABI transport is not qualified for this target".into());
    }
    let (IrTy::Closure(id), ty::Closure(_, args)) = (ir, arg.layout.ty.kind()) else {
        return Err("source closure environment is not an emitted by-value closure".into());
    };
    if args.as_closure().kind() != ty::ClosureKind::FnOnce {
        return Err("native source environment is not an FnOnce closure".into());
    }
    let captures = args.as_closure().upvar_tys();
    if captures.len() != arg.layout.fields.count() {
        return Err("rustc closure fields do not cover the source captures".into());
    }
    let observed = ObservedFrame {
        size: arg.layout.size.bytes(),
        align: arg.layout.align.bytes(),
        offsets: (0..captures.len()).map(|i| arg.layout.fields.offset(i).bytes()).collect(),
        captures: captures.iter().map(|ty| source_scalar(tcx, ty)).collect::<Result<_, _>>()?,
    };
    let transport = match (&arg.mode, arg.layout.backend_repr) {
        (PassMode::Direct(attrs), BackendRepr::Scalar(value)) => {
            Transport::Direct(lane(tcx, value, attrs)?)
        }
        (PassMode::Pair(a, b), BackendRepr::ScalarPair { a: x, b: y, .. }) => {
            Transport::Pair([lane(tcx, x, a)?, lane(tcx, y, b)?])
        }
        _ => {
            return Err(format!(
                "source closure has unsupported environment pass mode {:?}",
                arg.mode
            ));
        }
    };
    agreement::closure_transport(module, *id, &observed, &transport)
}

fn scalar_arg<'tcx>(
    tcx: TyCtxt<'tcx>,
    ir: &IrTy,
    arg: &ArgAbi<'tcx, Ty<'tcx>>,
    apple_c: bool,
) -> Result<RegisterUse, String> {
    let expected = source_scalar(tcx, arg.layout.ty)?;
    let (PassMode::Direct(attrs), BackendRepr::Scalar(value)) =
        (&arg.mode, arg.layout.backend_repr)
    else {
        return Err(format!("source scalar has unsupported pass mode {:?}", arg.mode));
    };
    let actual = lane(tcx, value, attrs)?;
    if actual.scalar != expected {
        return Err("rustc source scalar and FnAbi primitive disagree".into());
    }
    agreement::scalar_transport(ir, actual, apple_c)
}

/// P describes the original producer parameters, not a flattened replacement
/// signature. An unsupported target has no P entry (the gate must say Unknown).
fn aarch64_placement<'tcx>(
    tcx: TyCtxt<'tcx>,
    abi: &FnAbi<'tcx, Ty<'tcx>>,
) -> Option<trust_cg_bridge::call_event::FnPlacement> {
    use trust_cg_bridge::call_event::{
        AbiExt, FnPlacement, ParamPlace, ReturnPlace, ScalarPlace, Slot,
    };
    if tcx.sess.opts.target_triple.tuple() != "aarch64-apple-darwin" {
        return None;
    }
    let place = |reg, value, attrs: &ArgAttributes| {
        let scalar = scalar(tcx, value).ok()?;
        // P models integer registers only. Runtime FP transport is not a
        // license to invent a GPR observation or weaken the strict CER gate.
        if matches!(scalar, Scalar::Float { .. }) { return None; }
        Some(ScalarPlace {
            slot: Slot::Gpr(reg),
            width: u32::try_from(scalar.bytes() * 8).ok()?,
            ext: match attrs.arg_ext {
                ArgExtension::None => AbiExt::None,
                ArgExtension::Zext => AbiExt::Zext,
                ArgExtension::Sext => AbiExt::Sext,
            },
        })
    };
    let mut next = 0u8;
    let mut params = Vec::with_capacity(abi.args.len());
    for arg in &abi.args {
        match (&arg.mode, arg.layout.backend_repr) {
            (PassMode::Direct(attrs), BackendRepr::Scalar(value)) if next < 8 => {
                params.push(ParamPlace::Scalar(place(next, value, attrs)?));
                next += 1;
            }
            (PassMode::Pair(a, b), BackendRepr::ScalarPair { a: x, b: y, .. }) if next + 2 <= 8 => {
                if arg.layout.fields.count() != 2 {
                    return None;
                }
                let first = place(next, x, a)?;
                let second = place(next + 1, y, b)?;
                let (a, b) = (arg.layout.fields.offset(0), arg.layout.fields.offset(1));
                // ParamPlace::Pair is in declaration/capture order. Rustc's
                // two ABI scalars follow physical order, which may be reversed.
                params.push(if a < b {
                    ParamPlace::Pair(first, second)
                } else if b < a {
                    ParamPlace::Pair(second, first)
                } else {
                    return None;
                });
                next += 2;
            }
            _ => return None,
        }
    }
    let ret = match (&abi.ret.mode, abi.ret.layout.backend_repr) {
        (PassMode::Ignore, _) => ReturnPlace::Void,
        (PassMode::Direct(attrs), BackendRepr::Scalar(value)) => {
            ReturnPlace::Scalar(place(0, value, attrs)?)
        }
        _ => return None,
    };
    Some(FnPlacement { params, ret })
}

/// Attach only after exact source body/symbol selection, before the full
/// native Compiler consumes this same module. The caller retains source and
/// adapter licenses and independently enforces its output/proof policy.
pub(crate) fn validate_module_instance<'tcx, 'module>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
    module: &'module Module,
    id: FuncId,
) -> Result<SourceAbiAgreement<'tcx, 'module>, String> {
    let function = module.function_by_id(id).ok_or("source ABI function is missing")?;
    if function.name != tcx.symbol_name(instance).name
        || function.is_declaration()
        || function.producer != Some(Producer::TRust)
    {
        return Err("source ABI function does not match its exact body-bearing instance".into());
    }
    let signature = module.func_type(function.ty).ok_or("source ABI signature is missing")?;
    if signature.is_vararg || signature.abi.is_some() {
        return Err("source ABI requires its original non-variadic, unrewritten signature".into());
    }
    let entry = function.block(function.entry).ok_or("source ABI entry is missing")?;
    if entry.params.iter().map(|(_, ty)| ty).ne(signature.params.iter()) {
        return Err("source ABI entry parameters disagree with its signature".into());
    }
    let target = module.target_info.as_ref().ok_or("source ABI target is missing")?;
    if target.triple != tcx.sess.target.llvm_target.to_string()
        || target.pointer_size != 8
        || tcx.sess.target.pointer_width != 64
        || target.endianness != trust_ir::Endianness::Little
        || tcx.sess.target.endian != rustc_abi::Endian::Little
    {
        return Err(
            "source ABI target differs from the compiler's exact 64-bit little-endian target"
                .into(),
        );
    }
    let fn_abi =
        crate::fn_abi_preconditions_with_source(tcx, instance, signature.params.len(), true)?;
    let expected_conv = match fn_abi.conv {
        CanonAbi::Rust => CallingConv::Rust,
        CanonAbi::C => CallingConv::C,
        _ => return Err("source ABI canonical convention is unsupported".into()),
    };
    if function.calling_conv != expected_conv {
        return Err("source ABI calling convention disagrees with the emitted function".into());
    }
    let apple_c = fn_abi.conv == CanonAbi::C
        && crate::caller_small_arg_extension_bits(&tcx.sess.target) == Some(32);
    let closure_instance =
        matches!(instance.ty(tcx, ty::TypingEnv::fully_monomorphized()).kind(), ty::Closure(..));
    let mut registers = RegisterUse::default();
    for (index, (arg, ir)) in fn_abi.args.iter().zip(&signature.params).enumerate() {
        let words = if matches!(arg.layout.ty.kind(), ty::Closure(..)) {
            if index != 0 || !closure_instance {
                return Err(
                    "source closure environment is not its instance's leading argument".into()
                );
            }
            closure_arg(tcx, module, ir, arg).map(RegisterUse::integer)
        } else {
            scalar_arg(tcx, ir, arg, apple_c)
        };
        registers.add(words.map_err(|e| format!("source ABI argument {index}: {e}"))?);
    }
    let cap = crate::scalar_register_argument_limit(tcx.sess.opts.target_triple.tuple())
        .ok_or("source ABI target has no audited integer argument placement")?;
    match signature.returns.as_slice() {
        [] if crate::ignored_return_abi_ty_supported(&fn_abi.ret) => {}
        [ir] => {
            scalar_arg(tcx, ir, &fn_abi.ret, apple_c)
                .map_err(|e| format!("source ABI return: {e}"))?;
        }
        _ => return Err("source ABI result shape disagrees with rustc".into()),
    }
    let has_fp = registers.fp != 0 || signature.returns.iter().any(|ty| matches!(ty, IrTy::F32 | IrTy::F64));
    // Trust: the complete Darwin scalar classifier also checks natural stack
    // packing after either bank overflows. Closures/pairs retain their existing
    // register boundary because this path requires every parameter to be scalar.
    // This is runtime transport agreement only: P remains absent for stack/FP.
    if has_fp || registers.gpr > cap {
        let classified = trust_cg_bridge::source_scalar_abi::darwin_scalar(
            tcx.sess.opts.target_triple.tuple(), &signature.params, &signature.returns,
        )?;
        if (classified.gpr, classified.fp) != (registers.gpr, registers.fp) {
            return Err("source FnAbi and complete native classifier disagree on scalar banks".into());
        }
    }
    Ok(SourceAbiAgreement {
        source: module,
        function: id,
        fn_abi,
        placement: if has_fp { None } else { aarch64_placement(tcx, fn_abi) },
    })
}

/// Trust: these agreements can only be minted by the actual FnAbi check above.
/// They borrow the exact source image, so another module cannot inherit them.
/// The pure boundary additionally checks the complete unchanged module and every
/// aggregate signature before selecting native C carriers for the codegen copy.
pub(crate) fn classify_native_module(
    source: &Module,
    codegen: &mut Module,
    agreements: &[SourceAbiAgreement<'_, '_>],
) -> Result<(), String> {
    let checked: Vec<_> = agreements.iter().map(|a| (a.source, a.function)).collect();
    module_carrier::classify(source, codegen, &checked)
}
