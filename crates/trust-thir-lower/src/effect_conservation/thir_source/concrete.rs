//! Instantiate genuine source facts using Rust metadata, not constructed IR.
//! No MIR query is used. The initial complete drop argument is deliberately
//! narrow: every recorded source value type must need no drop. A real drop or
//! an incomplete by-value type walk refuses rather than losing its facts.

use std::collections::{BTreeSet, HashSet};

use rustc_hir::def::DefKind;
use rustc_middle::ty::{self, TyCtxt, TypeVisitableExt};
use trust_ir::template::HostKey;

use crate::rmeta_entry::StableDef;

use super::{CapturedSource, Result, SourceEffect, SourceRoot, MAX_SOURCE_DEPTH, refuse};

pub struct ConcreteCall<'tcx> {
    pub(super) expression: u32,
    original_key: HostKey,
    pub(super) raw_definition: StableDef,
    pub(super) raw_site: String,
    resolved: ty::Instance<'tcx>,
    resolved_key: HostKey,
    pub(super) enum_arguments: Vec<bool>,
    pub(super) enum_result: bool,
    original: Option<crate::rmeta_entry::EvidenceCall>,
}
impl<'tcx> ConcreteCall<'tcx> {
    pub fn source_expression(&self) -> u32 { self.expression }
    pub fn original_key(&self) -> &HostKey { &self.original_key }
    pub fn resolved(&self) -> ty::Instance<'tcx> { self.resolved }
    pub fn resolved_key(&self) -> &HostKey { &self.resolved_key }
    /// Original ordinary FnDef/site and raw enum facts, before substitution.
    /// None explicitly requires unsupported associated/trait-call transport.
    pub fn original_call(&self) -> Option<&crate::rmeta_entry::EvidenceCall> { self.original.as_ref() }
}

pub enum ConcreteEffect<'tcx> {
    Call(ConcreteCall<'tcx>),
    Store { expression: u32, root: SourceRoot, value_class: u8, exact_argument: Option<u32> },
}

/// Reconstructed original (pre-substitution) Rust facts. These are produced
/// from retained type/callee keys and actual Rust metadata, never constructed IR.
#[derive(Clone, Debug)]
pub(super) struct OriginalFacts {
    pub argument_enum: Vec<bool>, pub return_enum: bool,
    pub calls: Vec<crate::rmeta_entry::EvidenceCall>,
    pub stores: Vec<(u32,u8,Option<u32>)>,
    pub unsupported_call: bool,
}
/// Read-only concrete metadata. This is not a source-refinement theorem or a
/// body/admission token; the actual constructed body still has to be judged.
pub struct ConcreteSource<'tcx> {
    instance: ty::Instance<'tcx>,
    key: HostKey,
    source: CapturedSource,
    argument_enum: Vec<bool>,
    return_enum: bool,
    enum_types: BTreeSet<u128>,
    effects: Vec<ConcreteEffect<'tcx>>,
    pub(super) original: OriginalFacts,
}
impl<'tcx> ConcreteSource<'tcx> {
    pub fn instance(&self) -> ty::Instance<'tcx> { self.instance }
    pub fn instance_key(&self) -> &HostKey { &self.key }
    pub fn source(&self) -> &CapturedSource { &self.source }
    pub fn argument_enum(&self) -> &[bool] { &self.argument_enum }
    pub fn return_enum(&self) -> bool { self.return_enum }
    pub fn enum_types(&self) -> &BTreeSet<u128> { &self.enum_types }
    pub fn effects(&self) -> &[ConcreteEffect<'tcx>] { &self.effects }
    pub fn original_argument_enum(&self) -> &[bool] { &self.original.argument_enum }
    pub fn original_store_facts(&self) -> &[(u32,u8,Option<u32>)] { &self.original.stores }
}

fn actual_item<'tcx>(tcx: TyCtxt<'tcx>, instance: ty::Instance<'tcx>) -> Result<HostKey> {
    if !matches!(instance.def, ty::InstanceKind::Item(_))
        || !matches!(tcx.def_kind(instance.def_id()), DefKind::Fn | DefKind::AssocFn)
        || instance.args.len() != tcx.generics_of(instance.def_id()).count()
        || instance.args.has_non_region_param() || instance.args.has_non_region_infer()
        || instance.args.has_escaping_bound_vars()
    {
        return Err(refuse("concrete source requires an actual closed Rust Item"));
    }
    let key = crate::template_key::rustc::checked_call_key(tcx, instance.def_id(),
        instance.args, instance.def_id()).map_err(|e| refuse(e.to_string()))?;
    if tcx.instantiate_and_check_impossible_clauses((instance.def_id(), instance.args)) {
        return Err(refuse("concrete source has impossible Rust predicates"));
    }
    crate::template_key::encode(&key).map_err(|e| refuse(e.to_string()))
}

fn normalize<'tcx, T>(tcx: TyCtxt<'tcx>, value: T) -> Result<T>
where T: ty::TypeFoldable<TyCtxt<'tcx>> {
    crate::producer_try_normalize(tcx, ty::TypingEnv::fully_monomorphized(), value)
        .map_err(|_| refuse("concrete source normalization"))
}

fn by_value_enums<'tcx>(tcx: TyCtxt<'tcx>, source: ty::Ty<'tcx>, depth: usize,
    seen: &mut HashSet<ty::Ty<'tcx>>, enums: &mut BTreeSet<u128>) -> Result<()>
{
    if depth >= MAX_SOURCE_DEPTH { return Err(refuse("complete by-value type footprint depth")); }
    let source = normalize(tcx, source)?;
    if source.has_non_region_param() || source.has_non_region_infer() || source.has_escaping_bound_vars() {
        return Err(refuse("symbolic type in complete source footprint"));
    }
    if !seen.insert(source) { return Ok(()); }
    let fields: Vec<_> = match source.kind() {
        ty::Adt(adt, _) if adt.is_union() => return Err(refuse("union source footprint needs its semantics")),
        ty::Adt(adt, args) if !adt.is_box() => {
            if super::super::is_valued_enum(tcx, source) { enums.insert(tcx.type_id_hash(source).as_u128()); }
            adt.all_fields().map(|field| field.ty(tcx, *args).skip_normalization()).collect()
        }
        ty::Tuple(fields) => fields.iter().collect(),
        ty::Array(element, _) | ty::Slice(element) => vec![*element],
        ty::Closure(..) | ty::CoroutineClosure(..) | ty::Coroutine(..) =>
            return Err(refuse("closure/coroutine source footprint needs its semantics")),
        // A pointer or function item does not hold its pointee/type arguments
        // by value. Their actual evaluated source expressions have own rows.
        ty::Bool | ty::Char | ty::Int(_) | ty::Uint(_) | ty::Float(_) | ty::Never
            | ty::Str | ty::Ref(..) | ty::RawPtr(..) | ty::FnDef(..) | ty::FnPtr(..) => Vec::new(),
        ty::Adt(adt, _) if adt.is_box() => Vec::new(),
        _ => return Err(refuse("unsupported/unresolved type in complete source footprint")),
    };
    for field in fields { by_value_enums(tcx, field, depth + 1, seen, enums)?; }
    Ok(())
}

/// Substitute every original source key under the actual full Rust Instance.
/// All enum/value/drop answers below come from this independently retained
/// source footprint, never from a type or census guessed out of constructed IR.
pub fn instantiate<'tcx>(tcx: TyCtxt<'tcx>, instance: ty::Instance<'tcx>,
    source: &CapturedSource) -> Result<ConcreteSource<'tcx>>
{
    let key = actual_item(tcx, instance)?;
    let expected = crate::template_metadata::rustc::owner_bindings(tcx, instance.def_id())
        .map_err(|e| refuse(e.0))?;
    if &expected != source.bindings() { return Err(refuse("actual source owner/full positional map differs")); }
    if source.target != crate::crate_module::source_target_info(tcx) {
        return Err(refuse("source target differs from the actual Rust target"));
    }
    if source.overflow_checks != tcx.sess.overflow_checks() { return Err(refuse("source overflow mode differs")); }
    let mut types = Vec::with_capacity(source.types.len());
    let mut raw_types = Vec::with_capacity(source.types.len());
    let mut enum_types = BTreeSet::new(); let mut seen = HashSet::new();
    for key in &source.types {
        let crate::template_key::HoleKey::Type(term) = crate::template_key::decode(key)
            .map_err(|e| refuse(e.to_string()))? else { return Err(refuse("source footprint key is not a type")); };
        let original = crate::template_key::rustc::ty_of_key(tcx, &term, instance.def_id())
            .map_err(|e| refuse(e.to_string()))?;
        if original.walk().any(|a|a.as_type().is_some_and(|t|matches!(t.kind(),
            ty::Alias(..)|ty::Infer(..)|ty::Bound(..)|ty::Placeholder(..)))) {
            return Err(refuse("original source alias/inference facts require typed semantic transport"));
        }
        raw_types.push(original);
        let actual = normalize(tcx, ty::EarlyBinder::bind(tcx, original).instantiate(tcx, instance.args).skip_normalization())?;
        if crate::cycle_safe_needs_drop(tcx, ty::TypingEnv::fully_monomorphized(), actual) {
            return Err(refuse("actual source value needs complete drop/scope transport"));
        }
        by_value_enums(tcx, actual, 0, &mut seen, &mut enum_types)?;
        types.push(actual);
    }
    let get = |index: u32| types.get(index as usize).copied().ok_or_else(|| refuse("source type index is absent"));
    let args = source.argument_types.iter().map(|&i| get(i)).collect::<Result<Vec<_>>>()?;
    let ret = get(source.return_type)?;
    let signature = normalize(tcx, tcx.fn_sig(instance.def_id()).instantiate(tcx, instance.args).skip_normalization())?;
    if signature.bound_vars().iter().any(|v| !matches!(v, ty::BoundVariableKind::Region(_))) {
        return Err(refuse("source signature has nonregion bound variables"));
    }
    let signature = tcx.instantiate_bound_regions_with_erased(signature);
    if signature.inputs() != args || signature.output() != ret {
        return Err(refuse("retained source signature differs from actual Rust metadata"));
    }
    let mut effects = Vec::with_capacity(source.effects.len());
    for effect in &source.effects {
        match effect {
            SourceEffect::Call { expression, key, argument_types, result_type } => {
                let term = crate::template_key::decode(key).map_err(|e| refuse(e.to_string()))?;
                let (raw_def, raw_args) = crate::template_key::rustc::call_of_key(tcx, &term, instance.def_id())
                    .map_err(|e| refuse(e.to_string()))?;
                let original = if tcx.def_kind(raw_def)==DefKind::Fn {
                    let site=crate::encode_site_args(tcx,raw_args).map(|encoded|
                        crate::lineage::ConcreteCalleeKey::from_site_args(tcx,raw_def,
                            crate::lineage::ConcreteInstanceKind::Item,&encoded).symbol_suffix());
                    Some(crate::rmeta_entry::EvidenceCall{ids:vec![crate::template_key::rustc::stable_def(tcx,raw_def)],
                        site,equivalence:None,
                        enum_result:super::super::is_valued_enum(tcx,raw_types[*result_type as usize]),
                        enum_args:argument_types.iter().map(|&i|super::super::is_valued_enum(tcx,raw_types[i as usize])).collect()})
                } else { None };
                let raw_args = normalize(tcx, ty::EarlyBinder::bind(tcx, raw_args).instantiate(tcx, instance.args).skip_normalization())?;
                let raw_args = tcx.erase_and_anonymize_regions(raw_args);
                if raw_args.has_non_region_param() || raw_args.has_non_region_infer() || raw_args.has_escaping_bound_vars() {
                    return Err(refuse("source callee retains symbolic arguments"));
                }
                let resolved = ty::Instance::try_resolve(tcx, ty::TypingEnv::fully_monomorphized(), raw_def, raw_args)
                    .map_err(|_| refuse("source callee resolution"))?.ok_or_else(|| refuse("source callee is unresolved"))?;
                let resolved_key = actual_item(tcx, resolved)?;
                let sig = normalize(tcx, tcx.fn_sig(raw_def).instantiate(tcx, raw_args).skip_normalization())?;
                if sig.bound_vars().iter().any(|v| !matches!(v, ty::BoundVariableKind::Region(_))) {
                    return Err(refuse("source callee has nonregion bound variables"));
                }
                let sig = tcx.instantiate_bound_regions_with_erased(sig);
                let actual_args = argument_types.iter().map(|&i| get(i)).collect::<Result<Vec<_>>>()?;
                if sig.inputs() != actual_args || sig.output() != get(*result_type)? {
                    return Err(refuse("source call arguments/result differ from actual Rust signature"));
                }
                let encoded = crate::encode_site_args(tcx, raw_args)
                    .ok_or_else(|| refuse("source callee typed site is not encodable"))?;
                let raw_site = crate::lineage::ConcreteCalleeKey::from_site_args(tcx, raw_def,
                    crate::lineage::ConcreteInstanceKind::Item, &encoded).symbol_suffix();
                effects.push(ConcreteEffect::Call(ConcreteCall { expression: *expression,
                    original_key: key.clone(), original, raw_definition: crate::template_key::rustc::stable_def(tcx, raw_def),
                    raw_site, resolved, resolved_key,
                    enum_arguments: actual_args.iter().map(|&t| super::super::is_valued_enum(tcx, t)).collect(),
                    enum_result: super::super::is_valued_enum(tcx, sig.output()) }));
            }
            SourceEffect::Store { expression, root, value_type, exact_argument } => {
                let ty = get(*value_type)?;
                let value_class = if super::super::is_valued_enum(tcx, ty) { 0 }
                    else if ty.is_bool() || ty.is_unit() { 1 } else { 2 };
                effects.push(ConcreteEffect::Store { expression: *expression, root: root.clone(),
                    value_class, exact_argument: *exact_argument });
            }
        }
    }
    let mut original=OriginalFacts{argument_enum:source.argument_types.iter().map(|&i|
        super::super::is_valued_enum(tcx,raw_types[i as usize])).collect(),
        return_enum:super::super::is_valued_enum(tcx,raw_types[source.return_type as usize]),
        calls:Vec::new(),stores:Vec::new(),unsupported_call:false};
    for (source_effect,concrete_effect) in source.effects.iter().zip(&effects){match(source_effect,concrete_effect){
        (_,ConcreteEffect::Call(call))=>match &call.original{Some(call)=>original.calls.push(call.clone()),None=>original.unsupported_call=true},
        (SourceEffect::Store{root,value_type,exact_argument,..},ConcreteEffect::Store{..})=>{
            let ty=raw_types[*value_type as usize];let class=if super::super::is_valued_enum(tcx,ty){0}else if ty.is_bool()||ty.is_unit(){1}else{2};
            let code=match root{SourceRoot::Argument(i)=>*i,SourceRoot::Indirect=>u32::MAX};
            original.stores.push((code,class,if code==u32::MAX{*exact_argument}else{None}));
        }
        _=>return Err(refuse("original/concrete source effect association differs")),
    }}
    Ok(ConcreteSource { instance, key, source: source.clone(), original,
        argument_enum: args.iter().map(|&t| super::super::is_valued_enum(tcx, t)).collect(),
        return_enum: super::super::is_valued_enum(tcx, ret), enum_types, effects })
}
