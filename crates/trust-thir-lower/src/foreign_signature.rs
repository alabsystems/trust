//! Physical scalar prototypes read from the original foreign item at finalization.
//!
//! These are untrusted, digest-bearing ABI claims, not proof or admission tokens.
//! Source arguments and their lowered carriers are deliberately kept distinct;
//! this first producer profile requires one complete direct carrier per argument.
//! Pair/cast/indirect, Rust-call and function-pointer adaptation remain unavailable.

use std::fmt::Write as _;

use rustc_abi::{BackendRepr, CanonAbi, ExternAbi, RegKind};
use rustc_hir::def::DefKind;
use rustc_middle::ty::{self, TyCtxt, TypeVisitableExt};
use rustc_span::def_id::DefId;
use rustc_target::callconv::{ArgAbi, ArgAttribute, ArgAttributes, ArgExtension, PassMode};
use rustc_target::json::ToJson as _;
use trust_ir::signature_abi::*;
use trust_ir::{FuncTy, Ty};

/// Read only once source lowering has ended. The source definition and actual
/// concrete Item instance, rather than call operands or a display path, own the
/// prototype. Metadata-loaded foreign items take the same query path as locals.
pub(crate) fn read(tcx: TyCtxt<'_>, callee: &crate::CalleeRef) -> Option<FuncTy> {
    crate::instance_admission::refuse_inside_producer_lowering().ok()?;
    if !matches!(tcx.def_kind(callee.def_id), DefKind::Fn | DefKind::AssocFn)
        || !tcx.is_foreign_item(callee.def_id)
        || callee.force_havoc
        || callee.params.is_withdrawn()
        || callee.ret_ty_conflict
    {
        return None;
    }
    if callee.concrete_key.as_ref().is_some_and(|key|
        key.instance_kind() != crate::lineage::ConcreteInstanceKind::Item)
    { return None; }
    let args = source_args(tcx, callee)?;
    let encoded = crate::encode_site_args(tcx, args)?;
    if callee.concrete_key.as_ref() != Some(&crate::lineage::ConcreteCalleeKey::from_site_args(
        tcx, callee.def_id, crate::lineage::ConcreteInstanceKind::Item, &encoded))
    { return None; }
    read_instance(tcx, callee.def_id, args, callee.abi)
}

pub(crate) fn check_observation(signature: &FuncTy, abi: crate::calling_convention::FunctionAbi,
    params: &crate::ParamSignature,
    ret: Option<&Ty>, ret_conflict: bool, has_call_site: bool) -> Result<(), &'static str>
{
    if params.is_withdrawn() { return Err("parameter list withdrawn"); }
    if ret_conflict { return Err("call sites disagree on the result type"); }
    if !has_call_site { return Err("no direct call site binds this foreign prototype"); }
    let crate::calling_convention::AbiSource::Declared { abi: source, c_variadic } = abi.source()
    else { return Err("foreign prototype has no exact declared source ABI"); };
    if signature.is_vararg != c_variadic || signature.abi.as_ref().is_none_or(|record|
        record.source_abi != source.as_str() || abi.calling_conv().ok() != Some(record.lowered_convention))
    { return Err("foreign prototype disagrees with the original source ABI or variadicity"); }
    if params.signature().is_some_and(|p| p != &signature.params)
        || ret.is_some_and(|r| signature.returns.as_slice() != [r.clone()])
    { return Err("original foreign prototype disagrees with recorded call types"); }
    Ok(())
}

fn source_args<'tcx>(tcx: TyCtxt<'tcx>, callee: &crate::CalleeRef) -> Option<ty::GenericArgs<'tcx>> {
    let args = match &callee.instance_args {
        Some(encoded) => crate::to_mir::rebuild_site_args(tcx, encoded)?,
        None => ty::GenericArgs::identity_for_item(tcx, callee.def_id),
    };
    (!args.has_non_region_param() && !args.has_infer() && !args.has_escaping_bound_vars()).then_some(args)
}

/// Same-session reconstruction facts. Only the canonical finalizer creates
/// these; they are retained beside the complete immutable declaration image.
/// They confer neither a body licence nor a proof about an external callee.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ForeignSource {
    definition: DefId,
    arguments: Vec<crate::SiteArg>,
    abi: crate::calling_convention::FunctionAbi,
}

impl ForeignSource {
    pub(crate) fn capture(tcx: TyCtxt<'_>, callee: &crate::CalleeRef) -> Option<Self> {
        let arguments = crate::encode_site_args(tcx, source_args(tcx, callee)?)?;
        Some(Self { definition: callee.def_id, arguments, abi: callee.abi })
    }

    pub(crate) fn recheck<'tcx>(&self, tcx: TyCtxt<'tcx>, signature: &FuncTy)
        -> Result<ty::Instance<'tcx>, String>
    {
        crate::instance_admission::refuse_inside_producer_lowering()
            .map_err(|_| "foreign source ABI is unavailable during body lowering")?;
        if !tcx.is_foreign_item(self.definition)
            || crate::calling_convention::FunctionAbi::of_definition(tcx, self.definition) != self.abi
        { return Err("foreign declaration does not name its original source ABI".into()); }
        let args = crate::to_mir::rebuild_site_args(tcx, &self.arguments)
            .ok_or("foreign declaration source arguments no longer reconstruct")?;
        if read_instance(tcx, self.definition, args, self.abi).as_ref() != Some(signature) {
            return Err("foreign declaration differs from its original source FnAbi".into());
        }
        Ok(ty::Instance::new_raw(self.definition, tcx.erase_and_anonymize_regions(args)))
    }

    pub(crate) fn concrete_key(&self, tcx: TyCtxt<'_>) -> crate::lineage::ConcreteCalleeKey {
        crate::lineage::ConcreteCalleeKey::from_site_args(tcx, self.definition,
            crate::lineage::ConcreteInstanceKind::Item, &self.arguments)
    }
}

fn read_instance<'tcx>(tcx: TyCtxt<'tcx>, definition: DefId, args: ty::GenericArgs<'tcx>,
    abi: crate::calling_convention::FunctionAbi) -> Option<FuncTy>
{
    let crate::calling_convention::AbiSource::Declared { abi: source_abi, c_variadic } = abi.source()
    else { return None; };
    if !matches!(source_abi, ExternAbi::C { .. } | ExternAbi::System { .. }
        | ExternAbi::Cdecl { .. } | ExternAbi::SysV64 { .. } | ExternAbi::Aapcs { .. })
        || args.has_non_region_param() || args.has_infer() || args.has_escaping_bound_vars()
    { return None; }
    let env = ty::TypingEnv::fully_monomorphized();
    let source = tcx.fn_sig(definition).instantiate(tcx, args);
    let source = crate::producer_try_normalize(tcx, env, source).ok()?.skip_normalization();
    if source.bound_vars().iter().any(|v| !matches!(v, ty::BoundVariableKind::Region(_))) {
        return None;
    }
    let source = tcx.instantiate_bound_regions_with_erased(source);
    if source.abi() != source_abi || source.c_variadic() != c_variadic
        || source.fn_sig_kind.splatted().is_some()
    {
        return None;
    }
    let instance = ty::Instance::new_raw(definition, tcx.erase_and_anonymize_regions(args));
    let physical = tcx.fn_abi_of_instance_no_deduced_attrs(
        env.as_query_input((instance, ty::List::empty())),
    ).ok()?;
    if !matches!(physical.conv, CanonAbi::C | CanonAbi::X86(rustc_abi::X86Call::SysV64)
        | CanonAbi::Arm(rustc_abi::ArmCall::Aapcs))
        || physical.c_variadic != c_variadic
        || physical.fixed_count as usize != source.inputs().len()
        || physical.args.len() != source.inputs().len()
        || physical.ret.layout.ty != source.output()
    {
        return None;
    }
    let mut params = Vec::with_capacity(physical.args.len());
    let mut arguments = Vec::with_capacity(physical.args.len());
    for (index, (arg, input)) in physical.args.iter().zip(source.inputs()).enumerate() {
        if arg.layout.ty != *input { return None; }
        let (carrier, placement) = direct(arg, AbiBindingPlace::Parameter(index.try_into().ok()?))?;
        params.push(carrier);
        arguments.push(placement);
    }
    let (returns, result) = if source.output().is_unit() {
        if !matches!(physical.ret.mode, PassMode::Ignore) || physical.ret.layout.size.bytes() != 0 {
            return None;
        }
        (Vec::new(), AbiArgument {
            size: 0, align: physical.ret.layout.align.bytes(),
            mode: AbiPassMode::Ignore, bindings: Vec::new(),
        })
    } else {
        let (carrier, placement) = direct(&physical.ret, AbiBindingPlace::Result(0))?;
        (vec![carrier], placement)
    };
    let target = &tcx.sess.target;
    let mut features: Vec<_> = tcx.sess.internal_target_features.iter()
        .map(|feature| feature.to_string()).collect();
    features.sort();
    features.dedup();
    let mut signature = FuncTy { params, returns, is_vararg: c_variadic, abi: None };
    let placement = SignatureAbi {
        target: AbiTarget {
            triple: target.llvm_target.to_string(), data_layout: target.data_layout.to_string(),
            abi: target.llvm_abiname.desc().to_string(),
            cpu: tcx.sess.opts.cg.target_cpu.as_deref().unwrap_or(&target.cpu).to_string(),
            features,
            target_spec: target_spec_digest(&target.to_json().to_string()),
            pointer_bytes: (target.pointer_width / 8).try_into().ok()?,
            little_endian: target.endian == rustc_abi::Endian::Little,
        },
        frontend: AbiFrontend {
            name: "trust-thir-lower/rustc-fn-abi".into(),
            revision: format!("{}:{}", env!("CARGO_PKG_VERSION"),
                option_env!("CFG_VER_HASH").unwrap_or("source-revision-unavailable")),
        },
        convention: physical.conv.to_string(), lowered_convention: abi.calling_conv().ok()?,
        source_abi: source_abi.as_str().to_string(), can_unwind: physical.can_unwind,
        variadic: physical.c_variadic, fixed_count: physical.fixed_count, arguments, result,
    };
    placement.validate(&signature).ok()?;
    placement.validate_target(Some(&crate::crate_module::source_target_info(tcx))).ok()?;
    signature.abi = Some(placement);
    Some(signature)
}

fn direct(arg: &ArgAbi<'_, ty::Ty<'_>>, place: AbiBindingPlace) -> Option<(Ty, AbiArgument)> {
    let PassMode::Direct(attributes) = &arg.mode else { return None; };
    let BackendRepr::Scalar(scalar) = arg.layout.backend_repr else { return None; };
    // Reuse the producer's table-free spelling; a thin pointer additionally
    // has to be an actual scalar layout, never a source-kind guess about DSTs.
    let carrier = crate::scalar_ret_ty(arg.layout.ty)?;
    if !matches!(carrier, Ty::Bool | Ty::I8 | Ty::I16 | Ty::I32 | Ty::I64 | Ty::Isize
        | Ty::U8 | Ty::U16 | Ty::U32 | Ty::U64 | Ty::Usize | Ty::F32 | Ty::F64 | Ty::Ptr)
    { return None; }
    let size = arg.layout.size.bytes();
    let class = match RegKind::from_primitive(scalar.primitive()) {
        RegKind::Integer => AbiRegisterClass::Integer,
        RegKind::Float => AbiRegisterClass::Float,
        _ => return None,
    };
    let value_bits = if carrier == Ty::Bool { 1 } else { u16::try_from(size.checked_mul(8)?).ok()? };
    Some((carrier, AbiArgument {
        size, align: arg.layout.align.bytes(),
        mode: AbiPassMode::Direct(AbiScalar {
            register: AbiRegister { class, bytes: size }, source_offset: 0,
            source_bytes: size, value_bits, attributes: lower_attributes(attributes),
        }),
        bindings: vec![AbiBinding {
            place, source_offset: 0, source_bytes: size, carrier_offset: 0, carrier_bytes: size,
        }],
    }))
}

fn lower_attributes(attrs: &ArgAttributes) -> AbiAttributes {
    let has = |flag| attrs.regular.contains(flag);
    AbiAttributes {
        extension: match attrs.arg_ext {
            ArgExtension::None => AbiExtension::None,
            ArgExtension::Sext => AbiExtension::Sign,
            ArgExtension::Zext => AbiExtension::Zero,
        },
        in_reg: has(ArgAttribute::InReg), no_alias: has(ArgAttribute::NoAlias),
        nonnull: has(ArgAttribute::NonNull), readonly: has(ArgAttribute::ReadOnly),
        no_undef: has(ArgAttribute::NoUndef), writable: has(ArgAttribute::Writable),
        no_free: has(ArgAttribute::NoFree),
        capture: if has(ArgAttribute::CapturesNone) { AbiCapture::None }
            else if has(ArgAttribute::CapturesAddress) { AbiCapture::Address }
            else if has(ArgAttribute::CapturesReadOnly) { AbiCapture::ReadOnly }
            else { AbiCapture::Any },
        pointee_size: attrs.pointee_size.bytes(), pointee_align: attrs.pointee_align.map(|a| a.bytes()),
    }
}

fn target_spec_digest(spec: &str) -> String {
    let digest = trust_ir::ProofDigest::sha256_domain("trust.thir.foreign-abi.target.v1", spec.as_bytes());
    let mut identity = String::from("sha256:");
    for byte in digest.bytes { let _ = write!(identity, "{byte:02x}"); }
    identity
}


// Trust: keep executable unit controls in the conventional test module.
#[cfg(test)]
mod tests;
