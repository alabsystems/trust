//! Concrete Rust callable headers in the canonical construction namespace.
//!
//! Semantic IR types and physical FnAbi are separate. The source converter and
//! ordinary table merger place the former; the latter is retained verbatim from
//! rustc, including ignored slots, pass modes and value/pointee attributes. This
//! is no source refinement, native ABI agreement or admission capability.

extern crate rustc_target;

use std::sync::Arc;

use rustc_data_structures::fingerprint::Fingerprint;
use rustc_data_structures::stable_hash::{StableHash, StableHasher};
use rustc_hir::def::DefKind;
use rustc_middle::middle::codegen_fn_attrs::CodegenFnAttrFlags;
use rustc_middle::ty::{self, TyCtxt, TypeVisitableExt};
use rustc_target::callconv::FnAbi;
use trust_ir::{BodyGate, CallingConv, FuncAttrs, FuncId, FuncTy, Module};

use crate::concrete_type_transport::ConcreteTypes;

/// Only actual source queries construct this immutable header. Its semantic
/// roots are indexed in `image`, never in a caller's unrelated module.
pub(crate) struct ConcreteCallable<'tcx> {
    instance: ty::Instance<'tcx>,
    symbol: String,
    image: ConcreteTypes<'tcx>,
    parameters: usize,
    returns_unit: bool,
    fn_abi: &'tcx FnAbi<'tcx, ty::Ty<'tcx>>,
    abi_fingerprint: [u8; 16],
}

// Cache custody compares the complete source-derived image and the actual
// Rust FnAbi object, never just its fingerprint or a substituted IR signature.
// Exhaustive patterns force a new retained field to join this comparison.
impl PartialEq for ConcreteCallable<'_> {
    fn eq(&self, other: &Self) -> bool {
        let Self { instance, symbol, image, parameters, returns_unit, fn_abi, abi_fingerprint } = self;
        let Self {
            instance: other_instance,
            symbol: other_symbol,
            image: other_image,
            parameters: other_parameters,
            returns_unit: other_returns_unit,
            fn_abi: other_fn_abi,
            abi_fingerprint: other_abi_fingerprint,
        } = other;
        instance == other_instance
            && symbol == other_symbol
            && image == other_image
            && parameters == other_parameters
            && returns_unit == other_returns_unit
            && std::ptr::eq(*fn_abi, *other_fn_abi)
            && abi_fingerprint == other_abi_fingerprint
    }
}

impl<'tcx> ConcreteCallable<'tcx> {
    pub(crate) fn read(tcx: TyCtxt<'tcx>, instance: ty::Instance<'tcx>) -> Result<Self, String> {
        crate::instance_admission::refuse_inside_producer_lowering()
            .map_err(|_| "callable header is unavailable during source lowering")?;
        if !matches!(instance.def, ty::InstanceKind::Item(_))
            || !matches!(tcx.def_kind(instance.def_id()), DefKind::Fn | DefKind::AssocFn)
            || instance.args.len() != tcx.generics_of(instance.def_id()).count()
            || instance.args.has_non_region_param()
            || instance.args.has_non_region_infer()
            || instance.args.has_escaping_bound_vars()
        {
            return Err("callable header requires a concrete ordinary source function".into());
        }
        let attrs = tcx.codegen_instance_attrs(instance.def);
        if attrs.flags.intersects(
            CodegenFnAttrFlags::TRACK_CALLER
                | CodegenFnAttrFlags::NAKED
                | CodegenFnAttrFlags::OFFLOAD_KERNEL
                | CodegenFnAttrFlags::FOREIGN_ITEM
                | CodegenFnAttrFlags::EXTERNALLY_IMPLEMENTABLE_ITEM,
        ) || !attrs.target_features.is_empty()
            || attrs.safe_target_features
            || attrs.instruction_set.is_some()
        {
            return Err("template callable requires explicit source attribute transport".into());
        }
        let signature = tcx.fn_sig(instance.def_id()).instantiate(tcx, instance.args);
        let signature =
            crate::producer_try_normalize(tcx, ty::TypingEnv::fully_monomorphized(), signature)
                .map_err(|_| "template instance signature normalization")?
                .skip_normalization();
        if signature.bound_vars().iter().any(|v| !matches!(v, ty::BoundVariableKind::Region(_))) {
            return Err("template instance nonregion signature binder".into());
        }
        let signature = tcx.instantiate_bound_regions_with_erased(signature);
        if signature.abi() != rustc_abi::ExternAbi::Rust
            || signature.c_variadic()
            || signature.fn_sig_kind.splatted().is_some()
            || instance.def.requires_caller_location(tcx)
        {
            return Err("template instance callable convention requires an adapter".into());
        }
        let abi = tcx
            .fn_abi_of_instance(
                ty::TypingEnv::fully_monomorphized().as_query_input((instance, ty::List::empty())),
            )
            .map_err(|e| format!("template source FnAbi computation failed: {e:?}"))?;
        if abi.conv != rustc_abi::CanonAbi::Rust
            || abi.c_variadic
            || abi.fixed_count as usize != signature.inputs().len()
            || abi.args.len() != signature.inputs().len()
            || abi.args.iter().zip(signature.inputs()).any(|(arg, source)| arg.layout.ty != *source)
            || abi.ret.layout.ty != signature.output()
        {
            return Err("template source signature and actual FnAbi census disagree".into());
        }
        let mut sources = signature.inputs().to_vec();
        // Match the producer's return convention, including the uninhabited
        // return. No Unit value or return carrier is invented for Never.
        if !signature.output().is_unit() && !signature.output().is_never() {
            sources.push(signature.output());
        }
        let image = crate::concrete_type_transport::lower(tcx, instance, &sources)?;
        let fingerprint: Fingerprint = tcx.with_stable_hashing_context(|mut hcx| {
            let mut hasher = StableHasher::new();
            hcx.while_hashing_spans(false, |hcx| abi.stable_hash(hcx, &mut hasher));
            hasher.finish()
        });
        Ok(Self {
            instance,
            symbol: tcx.symbol_name(instance).name.to_string(),
            image,
            parameters: signature.inputs().len(),
            returns_unit: signature.output().is_unit(),
            fn_abi: abi,
            abi_fingerprint: fingerprint.to_le_bytes(),
        })
    }

    pub(crate) fn image(&self) -> &ConcreteTypes<'tcx> {
        &self.image
    }

    pub(crate) fn signature(&self, roots: &[trust_ir::Ty]) -> Result<FuncTy, String> {
        if roots.len() != self.image.roots().len() || self.parameters > roots.len() {
            return Err("template callable type roots changed population".into());
        }
        // These are source-semantic carriers. `None` remains explicitly
        // unrecorded physical ABI metadata; actual FnAbi is retained separately.
        Ok(FuncTy::unrecorded(
            roots[..self.parameters].to_vec(),
            roots[self.parameters..].to_vec(),
            false,
        ))
    }

    /// Reconcile only the source language's Unit-return convention. The format
    /// still instantiates a genuine Unit value; this private plan must be fully
    /// applied before any callable/source binding or constructed image escapes.
    pub(super) fn reconcile_signature(
        &self, roots: &[trust_ir::Ty], declared: &FuncTy, function: FuncId,
    ) -> Result<Option<UnitReturnPlan<'tcx>>, String> {
        let expected = self.signature(roots)?;
        if declared == &expected { return Ok(None); }
        let mut erased = declared.clone();
        erased.returns.clear();
        if self.returns_unit && self.fn_abi.ret.layout.ty.is_unit()
            && matches!(self.fn_abi.ret.mode, rustc_target::callconv::PassMode::Ignore)
            && declared.returns == [trust_ir::Ty::Unit] && erased == expected
        {
            return Ok(Some(UnitReturnPlan {
                function, symbol: self.symbol.clone(), before: declared.clone(), after: expected,
                instance: self.instance, fn_abi: self.fn_abi,
            }));
        }
        Err("template substituted source signature mismatch".into())
    }

    pub(crate) fn bind(
        self,
        module: &Module,
        function: FuncId,
    ) -> Result<CallableBinding<'tcx>, String> {
        let binding = CallableBinding { callable: Arc::new(self), function };
        binding.validate(module)?;
        Ok(binding)
    }
}

/// Temporary actual-Rust custody, never a caller-supplied Unit flag or a
/// general signature-coercion door. Only `ConcreteCallable` constructs it.
pub(super) struct UnitReturnPlan<'tcx> {
    function: FuncId,
    symbol: String,
    before: FuncTy,
    after: FuncTy,
    instance: ty::Instance<'tcx>,
    fn_abi: &'tcx FnAbi<'tcx, ty::Ty<'tcx>>,
}
impl UnitReturnPlan<'_> {
    pub(super) fn shape(&self) -> Result<(FuncId, &str, &FuncTy, &FuncTy), String> {
        if !matches!(self.instance.def, ty::InstanceKind::Item(_))
            || !self.fn_abi.ret.layout.ty.is_unit()
            || !matches!(self.fn_abi.ret.mode, rustc_target::callconv::PassMode::Ignore)
        { return Err("Unit return plan lost actual ordinary Rust Unit custody".into()); }
        Ok((self.function, &self.symbol, &self.before, &self.after))
    }
}

/// Actual instance/FnAbi custody for one body in an unlicensed constructed
/// graph. Private fields prevent fabricating an instance/FnAbi association.
/// Header validation does not authenticate the body's source or semantics.
#[derive(Clone, PartialEq)]
pub struct CallableBinding<'tcx> {
    callable: Arc<ConcreteCallable<'tcx>>,
    function: FuncId,
}

impl<'tcx> CallableBinding<'tcx> {
    pub fn function(&self) -> FuncId {
        self.function
    }
    pub fn instance(&self) -> ty::Instance<'tcx> {
        self.callable.instance
    }
    pub fn fn_abi(&self) -> &'tcx FnAbi<'tcx, ty::Ty<'tcx>> {
        self.callable.fn_abi
    }
    pub fn abi_fingerprint(&self) -> [u8; 16] {
        self.callable.abi_fingerprint
    }

    pub fn validate(&self, module: &Module) -> Result<(), String> {
        let function =
            module.function_by_id(self.function).ok_or("template callable body is absent")?;
        if function.is_declaration()
            || function.name != self.callable.symbol
            || function.calling_conv != CallingConv::Rust
            || function.attrs != FuncAttrs::default()
            || function.body_gate != Some(BodyGate::Ungated)
        {
            return Err(
                "template callable header no longer matches its actual Rust instance".into()
            );
        }
        // Reuse the canonical merger for every nested type and table ID. The
        // donor's local IDs are never compared with the graph's IDs directly.
        let placed = super::type_host::merge(module, self.callable.image())?;
        let expected = self.callable.signature(placed.roots())?;
        if module.func_type(function.ty) != Some(&expected) {
            return Err("template callable signature differs from actual source types".into());
        }
        Ok(())
    }

    pub(crate) fn rebound(mut self, module: &Module, function: FuncId) -> Result<Self, String> {
        self.function = function;
        self.validate(module)?;
        Ok(self)
    }
}
