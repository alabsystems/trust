//! Construction of a closed monomorphic IR graph from authenticated S inputs.
//!
//! No InstanceBody/admission token or codegen license is created here. Every
//! body remains Ungated. Supported ordinary generic callees import their real
//! instantiated template body through the canonical module merger; an unresolved
//! declaration, raw closure symbol, unsupported adapter or drop never escapes.

use rustc_hir::def::DefKind;
use rustc_middle::ty::{self, TyCtxt, TypeVisitableExt};
use rustc_span::def_id::DefId;
use trust_ir::proof::ProofDigest;
use trust_ir::template::{
    Destructor, GlobalAnswer, HostKey, InstArg, InstanceHeader, LinkAnswer, TemplateParam,
    TupleLayout,
};
use trust_ir::{
    BodyGate, CallingConv, Constant, FuncAttrs, FuncId, FuncTy, HoleId, Linkage, Module, Ty,
    Visibility,
};
use trust_ir_build::RetainedImage;
use trust_ir_build::template::{HostRefusal, InstantiationHost};

use super::callable_header::{CallableBinding, ConcreteCallable, UnitReturnPlan};
use super::{AuthenticatedTemplate, Result, SlotKind, SourceRetention, err};
use crate::effect_conservation::thir_source::binding::{self, ChildBinding, SourceCheck};
use crate::effect_conservation::thir_source::concrete;

/// Inputs may come only from an expected-owner authenticated read. Construction
/// rechecks the requested Rust owner/map, so a provider cannot substitute a
/// different same-shaped artifact. The default reads the actual crate store.
pub trait TemplateProvider<'tcx> {
    fn load(&mut self, tcx: TyCtxt<'tcx>, owner: DefId) -> Result<AuthenticatedTemplate>;
}
pub struct CrateMetadata;
impl<'tcx> TemplateProvider<'tcx> for CrateMetadata {
    fn load(&mut self, tcx: TyCtxt<'tcx>, owner: DefId) -> Result<AuthenticatedTemplate> {
        super::rustc::load_upstream(tcx, owner)
    }
}

#[derive(Clone)]
pub struct ConstructedInstance<'tcx> {
    image: RetainedImage,
    instance_key: HostKey,
    input_digest: [u8; 32],
    graph_digest: ProofDigest,
    callables: Vec<CallableBinding<'tcx>>,
    source_checks: Option<Vec<SourceCheck>>,
}
impl<'tcx> ConstructedInstance<'tcx> {
    /// Actual source instance/FnAbi records, one per body. These grant no admission.
    pub fn callables(&self) -> &[CallableBinding<'tcx>] {
        &self.callables
    }
    pub fn module(&self) -> &Module {
        self.image.module()
    }
    pub fn entry(&self) -> FuncId {
        FuncId::new(0)
    }
    pub fn instance_key(&self) -> &HostKey {
        &self.instance_key
    }
    pub fn input_digest(&self) -> [u8; 32] {
        self.input_digest
    }
    /// Actual source consistency inputs for every final body, when required.
    /// Neither these records nor FnAbi custody grants a body/proof license.
    pub fn source_checks(&self) -> Option<&[SourceCheck]> {
        self.source_checks.as_deref()
    }
    pub fn graph_digest(&self) -> ProofDigest {
        self.graph_digest
    }

    // Every field of an actually checked construction participates. This is
    // origin custody, not a validation shortcut or a semantic digest lookup.
    fn same_checked_inputs(&self, other: &Self) -> bool {
        let Self { image, instance_key, input_digest, graph_digest, callables, source_checks } =
            self;
        let Self {
            image: other_image,
            instance_key: other_instance_key,
            input_digest: other_input_digest,
            graph_digest: other_graph_digest,
            callables: other_callables,
            source_checks: other_source_checks,
        } = other;
        image.module() == other_image.module()
            && instance_key == other_instance_key
            && input_digest == other_input_digest
            && graph_digest == other_graph_digest
            && callables == other_callables
            && source_checks == other_source_checks
    }
}

pub fn construct<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
) -> Result<ConstructedInstance<'tcx>> {
    construct_with(tcx, instance, &mut CrateMetadata)
}
pub fn construct_with<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
    provider: &mut dyn TemplateProvider<'tcx>,
) -> Result<ConstructedInstance<'tcx>> {
    construct_mode(tcx, instance, provider, false)
}

/// Require retained original source facts for every body, beside actual FnAbi.
/// S1 remains unlicensed data and cannot satisfy this source-required API.
pub fn construct_source_checked_with<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
    provider: &mut dyn TemplateProvider<'tcx>,
) -> Result<ConstructedInstance<'tcx>> {
    construct_mode(tcx, instance, provider, true)
}
fn construct_mode<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
    provider: &mut dyn TemplateProvider<'tcx>,
    require_source: bool,
) -> Result<ConstructedInstance<'tcx>> {
    crate::instance_admission::refuse_inside_producer_lowering()
        .map_err(|_| err("template construction is unavailable during source lowering"))?;
    let mut budget = Budget {
        active: Vec::new(),
        remaining: 128,
        symbols: std::collections::BTreeMap::new(),
        checked: Vec::new(),
    };
    build(tcx, instance, provider, &mut budget, require_source)
}
struct Budget<'tcx> {
    active: Vec<HostKey>,
    remaining: usize,
    symbols: std::collections::BTreeMap<String, HostKey>,
    checked: Vec<(ty::Instance<'tcx>, bool, ConstructedInstance<'tcx>)>,
}

fn key<'tcx>(tcx: TyCtxt<'tcx>, instance: ty::Instance<'tcx>) -> Result<HostKey> {
    let key = crate::template_key::rustc::checked_call_key(
        tcx,
        instance.def_id(),
        instance.args,
        instance.def_id(),
    )
    .map_err(|e| err(e.to_string()))?;
    crate::template_key::encode(&key).map_err(|e| err(e.to_string()))
}
fn supported_instance<'tcx>(tcx: TyCtxt<'tcx>, instance: ty::Instance<'tcx>) -> Result<()> {
    if !matches!(instance.def, ty::InstanceKind::Item(_))
        || !matches!(tcx.def_kind(instance.def_id()), DefKind::Fn | DefKind::AssocFn)
    {
        return Err(err("template callee requires a real closure/function-item shim or adapter"));
    }
    if instance.args.has_non_region_param() || instance.args.has_non_region_infer() {
        return Err(err("template instance arguments are not concrete"));
    }
    if tcx.instantiate_and_check_impossible_clauses((instance.def_id(), instance.args)) {
        return Err(err("template instance has impossible source predicates"));
    }
    if tcx.intrinsic(instance.def_id()).is_some() {
        return Err(err("template intrinsic has no source template body"));
    }
    if instance.def.requires_caller_location(tcx) {
        return Err(err("template instance requires caller-location transport"));
    }
    if !tcx.codegen_fn_attrs(instance.def_id()).target_features.is_empty() {
        return Err(err("template instance target features require explicit transport"));
    }
    Ok(())
}

/// The template-module tables an instance cannot transport yet; `Some` names the refusal.
pub(super) fn untransported_template_tables<X>(
    module: &trust_ir::ModuleG<X>,
) -> Option<&'static str> {
    if !module.globals.is_empty()
        || !module.structs.is_empty()
        || !module.enums.is_empty()
        || !module.records.is_empty()
        || !module.closure_types.is_empty()
    {
        return Some("template instance requires unsupported nominal/global/capture transport");
    }
    // trust-ir v70 tensor weight blobs: no template carries one (`escape_check` requires the
    // table empty), and an instance has no transport for one.
    if !module.blobs.is_empty() {
        return Some("template instance requires unsupported tensor weight-blob transport");
    }
    None
}

fn build<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
    provider: &mut dyn TemplateProvider<'tcx>,
    budget: &mut Budget<'tcx>,
    require_source: bool,
) -> Result<ConstructedInstance<'tcx>> {
    supported_instance(tcx, instance)?;
    let instance_key = key(tcx, instance)?;
    if budget.remaining == 0 || budget.active.len() >= 64 {
        return Err(err("template instance graph budget"));
    }
    if budget.active.contains(&instance_key) {
        return Err(err("recursive template instance requires SCC body linkage"));
    }
    let symbol = tcx.symbol_name(instance).name.to_string();
    if let Some(prior) = budget.symbols.insert(symbol, instance_key.clone()) {
        if prior != instance_key {
            return Err(err("different typed template instances collide at a link symbol"));
        }
    }
    budget.remaining -= 1;
    budget.active.push(instance_key.clone());
    let result = (|| {
        let artifact = provider.load(tcx, instance.def_id())?;
        let expected = super::rustc::owner_bindings(tcx, instance.def_id())?;
        if artifact.bindings() != &expected {
            return Err(err("template provider returned a mismatched requested owner/map"));
        }
        if artifact.overflow_checks() != tcx.sess.overflow_checks() {
            return Err(err("template instance overflow mode mismatch"));
        }
        let source = match artifact.source() {
            Some(SourceRetention::Captured(source)) => {
                Some(concrete::instantiate(tcx, instance, source).map_err(|e| err(e.0))?)
            }
            Some(SourceRetention::Unavailable(reason)) => {
                return Err(err(format!("template source capture unavailable: {reason}")));
            }
            None if require_source => {
                return Err(err("template lacks retained original THIR source facts"));
            }
            None => None,
        };
        let t = artifact.template();
        if t.module.target_info.as_ref() != Some(&crate::crate_module::source_target_info(tcx)) {
            return Err(err("template instance target mismatch"));
        }
        if let Some(why) = untransported_template_tables(&t.module) {
            return Err(err(why));
        }
        for f in t.module.functions.iter().skip(1) {
            if !t
                .header
                .holes
                .iter()
                .any(|h| matches!(h.kind,trust_ir::template::HoleKind::Callee{decl}if decl==f.id))
            {
                return Err(err("ground callee requires authenticated instance/body transport"));
            }
        }
        let mut host = RustHost {
            tcx,
            instance,
            artifact: &artifact,
            provider,
            budget,
            callees: Vec::new(),
            source_children: Vec::new(),
            require_source: require_source || source.is_some(),
            types: Vec::new(),
            callable: None,
            unit_returns: Vec::new(),
        };
        let instantiated = trust_ir_build::template::instantiate(t, &mut host)
            .map_err(|e| err(format!("template instantiation: {e}")))?;
        // The format's checked substitution is unchanged. Apply the separately
        // retained actual-Rust convention before source/header/image custody.
        let module = super::unit_return::adapt(instantiated.module, &host.unit_returns)
            .map_err(err)?;
        let header = host
            .callable
            .take()
            .ok_or_else(|| err("template instance has no actual source callable header"))?;
        let mut callables = vec![header.bind(&module, FuncId::new(0)).map_err(err)?];
        let mut source_checks = if let Some(source) = source {
            Some(vec![
                binding::bind(source, &artifact, &module, &host.source_children)
                    .map_err(|e| err(e.0))?,
            ])
        } else {
            None
        };
        let mut image =
            RetainedImage::new(module).map_err(|e| err(format!("template original image: {e}")))?;
        let mut dependency_digests = Vec::with_capacity(host.callees.len());
        if host.source_children.len() != host.callees.len() {
            return Err(err("source child/body population mismatch"));
        }
        for (child, body) in host.source_children.into_iter().zip(host.callees) {
            dependency_digests.push(body.graph_digest.bytes);
            let module = image.module();
            if source_checks.is_some() {
                let decl = module
                    .function_by_id(child.declaration)
                    .ok_or_else(|| err("source declaration disappeared before canonical merge"))?;
                let entry = body
                    .module()
                    .function_by_id(body.entry())
                    .ok_or_else(|| err("actual child body is absent"))?;
                let retained_body = decl.is_declaration()
                    || source_checks.as_ref().is_some_and(|records| {
                        records.iter().any(|r| {
                            r.body() == decl.id
                                && r.instance_key() == &child.instance_key
                                && r.input_digest() == body.input_digest()
                        })
                    });
                if !retained_body
                    || decl.name != entry.name
                    || &child.instance_key != body.instance_key()
                    || !body.source_checks.as_ref().is_some_and(|records| {
                        records.iter().any(|r| {
                            r.body() == body.entry()
                                && r.instance_key() == &child.instance_key
                                && r.input_digest() == body.input_digest()
                        })
                    })
                {
                    return Err(err("typed source declaration differs from actual child origin"));
                }
                // Parent and donor FuncTy IDs live in different namespaces.
                // Canonical merge validates the remapped declaration/body ABI;
                // the actual child callable is rebound and revalidated below.
            }
            let (merged, remap) = image
                .merge(&body.image, &trust_ir_build::merge::MergePolicy::VERIFICATION_IMAGE)
                .map_err(|e| err(format!("template source body merge: {e}")))?;
            image = merged;
            let module = image.module();
            if let Some(records) = &mut source_checks {
                if remap.func(body.entry()) != Some(child.declaration) {
                    return Err(err(
                        "canonical child entry did not relink its original source declaration",
                    ));
                }
                let child_records = body
                    .source_checks
                    .as_ref()
                    .ok_or_else(|| err("source graph child lacks original source facts"))?;
                for record in child_records {
                    let mapped = record.remap(&remap).map_err(|e| err(e.0))?;
                    if let Some(old) = records.iter().find(|r| r.body() == mapped.body()) {
                        if old != &mapped {
                            return Err(err(
                                "merged body has conflicting original source provenance",
                            ));
                        }
                    } else {
                        records.push(mapped);
                    }
                }
            }
            for binding in body.callables {
                let id = remap
                    .func(binding.function())
                    .ok_or_else(|| err("template callable body has no canonical function remap"))?;
                let binding = binding.rebound(module, id).map_err(err)?;
                if let Some(prior) = callables.iter().find(|old| old.function() == id) {
                    if prior.instance() != binding.instance() || prior.fn_abi() != binding.fn_abi()
                    {
                        return Err(err(
                            "different source callable instances collide after canonical merge",
                        ));
                    }
                } else {
                    callables.push(binding);
                }
            }
        }
        let module = image.module();
        if module.functions.iter().any(|f| f.is_declaration()) {
            return Err(err("template instance has an unlinked callee body"));
        }
        let errors = trust_ir_build::validate::validate_module(&module);
        if !errors.is_empty() {
            return Err(err(format!("linked template graph invalid: {errors:?}")));
        }
        if module.functions.iter().any(|f| f.body_gate != Some(BodyGate::Ungated)) {
            return Err(err("template construction gained an unauthorized body gate"));
        }
        callables.sort_by_key(|binding| binding.function());
        if callables.len() != module.functions.len() {
            return Err(err(
                "template linked graph lacks an actual callable record for every body",
            ));
        }
        for binding in &callables {
            binding.validate(&module).map_err(err)?;
        }
        if let Some(records) = &mut source_checks {
            binding::check_graph(&module, records).map_err(|e| err(e.0))?;
            records.sort_by_key(|r| r.body());
            for record in records.iter() {
                let callable = callables
                    .iter()
                    .find(|b| b.function() == record.body())
                    .ok_or_else(|| err("source body lacks actual callable custody"))?;
                if key(tcx, callable.instance())? != *record.instance_key() {
                    return Err(err("source and FnAbi records name different actual instances"));
                }
            }
        }
        // Rust cache identity must bind authenticated input/evidence and every
        // linked dependency, beyond the format's semantic IR instance digest.
        let mut preimage = Vec::new();
        preimage.extend_from_slice(&artifact.digest());
        preimage.extend_from_slice(&(instance_key.namespace.len() as u64).to_le_bytes());
        preimage.extend_from_slice(instance_key.namespace.as_bytes());
        preimage.extend_from_slice(&(instance_key.bytes.len() as u64).to_le_bytes());
        preimage.extend_from_slice(&instance_key.bytes);
        preimage.extend_from_slice(&module.stable_digest().bytes);
        preimage.extend_from_slice(&(dependency_digests.len() as u64).to_le_bytes());
        for digest in dependency_digests {
            preimage.extend_from_slice(&digest);
        }
        preimage.extend_from_slice(&(callables.len() as u64).to_le_bytes());
        for binding in &callables {
            preimage.extend_from_slice(&binding.function().index().to_le_bytes());
            preimage.extend_from_slice(&binding.abi_fingerprint());
            let identity = key(tcx, binding.instance())?;
            preimage.extend_from_slice(&(identity.namespace.len() as u64).to_le_bytes());
            preimage.extend_from_slice(identity.namespace.as_bytes());
            preimage.extend_from_slice(&(identity.bytes.len() as u64).to_le_bytes());
            preimage.extend_from_slice(&identity.bytes);
        }
        match &source_checks {
            None => preimage.push(0),
            Some(records) => {
                preimage.push(1);
                preimage.extend_from_slice(&(records.len() as u64).to_le_bytes());
                for record in records {
                    preimage.extend_from_slice(&record.cache_digest().map_err(|e| err(e.0))?.bytes);
                }
            }
        }
        let graph_digest =
            ProofDigest::sha256_domain("trust.rmeta.template-source-callable-graph.v2", &preimage);
        Ok(ConstructedInstance {
            image,
            instance_key: instance_key.clone(),
            input_digest: artifact.digest(),
            graph_digest,
            callables,
            source_checks,
        })
    })();
    budget.active.pop();
    let completed = result?;
    // Reconstruct and revalidate BEFORE consulting custody. Every provider
    // read, including transitive inputs, and every existing owner/target/mode,
    // source/header/body check above still runs. Keys/digests alone never
    // create an origin or recover one from a raw module.
    if let Some((_, _, prior)) = budget
        .checked
        .iter()
        .find(|(actual, required, _)| *actual == instance && *required == require_source)
    {
        if !completed.same_checked_inputs(prior) {
            return Err(err("template checked input changed while constructing its graph"));
        }
        return Ok(prior.clone());
    }
    budget.checked.push((instance, require_source, completed.clone()));
    Ok(completed)
}

struct RustHost<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
    artifact: &'a AuthenticatedTemplate,
    provider: &'a mut dyn TemplateProvider<'tcx>,
    budget: &'a mut Budget<'tcx>,
    callees: Vec<ConstructedInstance<'tcx>>,
    source_children: Vec<ChildBinding>,
    require_source: bool,
    types: Vec<(Ty, ty::Ty<'tcx>)>,
    callable: Option<ConcreteCallable<'tcx>>,
    unit_returns: Vec<UnitReturnPlan<'tcx>>,
}
impl<'tcx> RustHost<'_, 'tcx> {
    fn placed(
        &mut self,
        cx: &mut Module,
        image: &crate::concrete_type_transport::ConcreteTypes<'tcx>,
    ) -> std::result::Result<Vec<Ty>, HostRefusal> {
        if image.roots().len() != image.sources().len() {
            return Err(HostRefusal("source type image root/binding population mismatch".into()));
        }
        let merged = super::type_host::merge(cx, image).map_err(HostRefusal)?;
        let mut bindings = self.types.clone();
        for (mapped, &source) in merged.roots().iter().zip(image.sources()) {
            if bindings.iter().any(|(old, actual)| old == mapped && *actual != source) {
                return Err(HostRefusal(
                    "distinct Rust source types collide in the installed IR representation".into(),
                ));
            }
            if !bindings.iter().any(|(old, actual)| old == mapped && *actual == source) {
                bindings.push((mapped.clone(), source));
            }
        }
        let (module, roots) = merged.into_parts();
        *cx = module;
        self.types = bindings;
        Ok(roots)
    }
    fn mapped(&mut self, cx: &mut Module, t: ty::Ty<'tcx>) -> std::result::Result<Ty, HostRefusal> {
        let image = crate::concrete_type_transport::lower(self.tcx, self.instance, &[t])
            .map_err(HostRefusal)?;
        self.placed(cx, &image)?
            .into_iter()
            .next()
            .ok_or_else(|| HostRefusal("source type converter returned no requested root".into()))
    }
}
impl<'tcx> InstantiationHost for RustHost<'_, 'tcx> {
    fn arguments(
        &mut self,
        cx: &mut Module,
        params: &[TemplateParam],
    ) -> std::result::Result<Vec<InstArg>, HostRefusal> {
        let mut out = Vec::with_capacity(params.len());
        for (i, slot) in self.artifact.bindings().slots.iter().enumerate() {
            match &slot.kind {
                SlotKind::Lifetime => {}
                SlotKind::Type(_) => {
                    let t = self.instance.args[i]
                        .as_type()
                        .ok_or_else(|| HostRefusal("template source type slot mismatch".into()))?;
                    let t = self.mapped(cx, t)?;
                    out.push(InstArg::Type(t));
                }
                SlotKind::Const { ty, .. } => {
                    let c = self.instance.args[i]
                        .as_const()
                        .ok_or_else(|| HostRefusal("template source const slot mismatch".into()))?;
                    let k = crate::template_key::rustc::key_of_call(
                        self.tcx,
                        self.instance.def_id(),
                        self.instance.args,
                    )
                    .map_err(|e| HostRefusal(e.to_string()))?;
                    let crate::template_key::HoleKey::Callee { args, .. } = k else {
                        unreachable!()
                    };
                    let Some(crate::template_key::KeyArg::Const(
                        crate::template_key::KeyConst::Value { bits, bytes, ty: source_ty },
                    )) = args.get(i)
                    else {
                        return Err(HostRefusal(
                            "template const argument is not an evaluated scalar".into(),
                        ));
                    };
                    let value = match &**source_ty {
                        crate::template_key::KeyTy::Bool => Constant::Bool(*bits != 0),
                        crate::template_key::KeyTy::Char => Constant::Int(*bits as i128),
                        crate::template_key::KeyTy::Int(_) => {
                            let width = u32::from(*bytes) * 8;
                            let signed = if width == 128 {
                                *bits as i128
                            } else {
                                ((*bits << (128 - width)) as i128) >> (128 - width)
                            };
                            Constant::Int(signed)
                        }
                        crate::template_key::KeyTy::Uint(_) => Constant::u128(*bits),
                        _ => {
                            return Err(HostRefusal(
                                "unsupported template scalar const kind".into(),
                            ));
                        }
                    };
                    let _ = ty;
                    let _ = c;
                    out.push(InstArg::Const(value));
                }
            }
        }
        Ok(out)
    }
    fn type_hole(
        &mut self,
        cx: &mut Module,
        _: HoleId,
        key: &HostKey,
        _: &[InstArg],
    ) -> std::result::Result<Ty, HostRefusal> {
        let image = crate::concrete_type_transport::from_key(self.tcx, self.instance, key)
            .map_err(HostRefusal)?;
        self.placed(cx, &image)?
            .into_iter()
            .next()
            .ok_or_else(|| HostRefusal("source type hole returned no requested root".into()))
    }
    fn const_hole(
        &mut self,
        _: &mut Module,
        _: HoleId,
        key: &HostKey,
        _: &[InstArg],
        expected: &Ty,
    ) -> std::result::Result<Constant, HostRefusal> {
        super::const_host::resolve(self.tcx, self.instance, key, expected)
            .map_err(|e| HostRefusal(e.0))
    }
    fn callee_hole(
        &mut self,
        cx: &mut Module,
        hole_id: HoleId,
        key: &HostKey,
        _: &[InstArg],
        sig: &FuncTy,
    ) -> std::result::Result<LinkAnswer, HostRefusal> {
        let hole = self
            .artifact
            .template()
            .header
            .holes
            .get(hole_id.as_usize())
            .filter(|h| &h.key == key)
            .ok_or_else(|| {
                HostRefusal("callee answer is detached from its original typed hole".into())
            })?;
        let trust_ir::template::HoleKind::Callee { decl } = hole.kind else {
            return Err(HostRefusal("callee answer names a non-callee hole".into()));
        };
        let term = crate::template_key::decode(key).map_err(|e| HostRefusal(e.to_string()))?;
        let (item, args) =
            crate::template_key::rustc::call_of_key(self.tcx, &term, self.instance.def_id())
                .map_err(|e| HostRefusal(e.to_string()))?;
        let args = ty::EarlyBinder::bind(self.tcx, args).instantiate(self.tcx, self.instance.args);
        let args =
            crate::producer_try_normalize(self.tcx, ty::TypingEnv::fully_monomorphized(), args)
                .map_err(|_| HostRefusal("template callee argument normalization".into()))?
                .skip_normalization();
        let resolved =
            ty::Instance::try_resolve(self.tcx, ty::TypingEnv::fully_monomorphized(), item, args)
                .map_err(|_| HostRefusal("template callee resolution error".into()))?
                .ok_or_else(|| HostRefusal("template callee is unresolved".into()))?;
        supported_instance(self.tcx, resolved).map_err(|e| HostRefusal(e.0))?;
        let header = ConcreteCallable::read(self.tcx, resolved).map_err(HostRefusal)?;
        let roots = self.placed(cx, header.image())?;
        if let Some(plan) = header.reconcile_signature(&roots, sig, decl).map_err(HostRefusal)? {
            self.unit_returns.push(plan);
        }
        let body = build(self.tcx, resolved, self.provider, self.budget, self.require_source)
            .map_err(|e| HostRefusal(e.0))?;
        let f = &body.module().functions[0];
        // The child's own callable check uses its own namespace. Its signature
        // is rechecked in this graph after the canonical module merge below.
        let answer = LinkAnswer::rust(f.name.clone());
        self.source_children.push(ChildBinding {
            hole: hole_id,
            declaration: decl,
            original_key: key.clone(),
            instance_key: body.instance_key().clone(),
        });
        self.callees.push(body);
        Ok(answer)
    }
    fn global_hole(
        &mut self,
        _: &mut Module,
        _: HoleId,
        _: &HostKey,
        _: &[InstArg],
        _: &Ty,
        _: bool,
    ) -> std::result::Result<GlobalAnswer, HostRefusal> {
        Err(HostRefusal("Rust template global body transport unavailable".into()))
    }
    fn instance(
        &mut self,
        cx: &mut Module,
        sig: &FuncTy,
    ) -> std::result::Result<InstanceHeader, HostRefusal> {
        if self.callable.is_some() {
            return Err(HostRefusal("template instance asked for its header twice".into()));
        }
        let header = ConcreteCallable::read(self.tcx, self.instance).map_err(HostRefusal)?;
        let roots = self.placed(cx, header.image())?;
        if let Some(plan) = header.reconcile_signature(&roots, sig, FuncId::new(0)).map_err(HostRefusal)? {
            self.unit_returns.push(plan);
        }
        self.callable = Some(header);
        Ok(InstanceHeader {
            symbol: self.tcx.symbol_name(self.instance).name.to_string(),
            linkage: Linkage::Internal,
            visibility: Visibility::Default,
            calling_conv: CallingConv::Rust,
            attrs: FuncAttrs::default(),
            display_path: None,
            body_gate: BodyGate::Ungated,
        })
    }
    fn destructor(
        &mut self,
        _: &mut Module,
        t: &Ty,
    ) -> std::result::Result<Destructor, HostRefusal> {
        let source = self
            .types
            .iter()
            .find(|(mapped, _)| mapped == t)
            .map(|(_, source)| *source)
            .ok_or_else(|| {
            HostRefusal("template destructor has no source type binding".into())
        })?;
        if crate::cycle_safe_needs_drop(self.tcx, ty::TypingEnv::fully_monomorphized(), source) {
            return Err(HostRefusal(
                "template destructor requires actual glue body linkage".into(),
            ));
        }
        Ok(Destructor::NoDestructor)
    }
    fn tuple_layout(
        &mut self,
        _: &mut Module,
        _: &Ty,
    ) -> std::result::Result<Option<TupleLayout>, HostRefusal> {
        Err(HostRefusal("Rust template tuple layout transport unavailable".into()))
    }
}
