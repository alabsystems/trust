//! Typed source-to-construction custody. Original source keys/ExprIds never
//! become IR-derived facts. Only the canonical merger's actual Remap transports
//! constructed body/declaration IDs. No admission, grade or source theorem.
use std::collections::{BTreeMap, BTreeSet};
use trust_ir::{FuncId, Module};
use trust_ir::template::{HoleKind, HostKey};
use crate::rmeta_entry::{Evidence, EvidenceCall, EvidenceEffectKind, EvidenceLedgerRow};
use crate::template_metadata::AuthenticatedTemplate;
use super::{CapturedSource, Result, SourceRoot, refuse};
use super::concrete::{ConcreteEffect, ConcreteSource};

/// Actual resolved child identity, attached to the original typed hole/decl by
/// RustHost before the format instantiator can rename/coalesce declarations.
#[derive(Clone)]
pub(crate) struct ChildBinding {
    pub hole: trust_ir::HoleId,
    pub declaration: FuncId,
    pub original_key: HostKey,
    pub instance_key: HostKey,
}

/// A retained consistency input for one known body. This is data, never a
/// capability. A closed graph must retain and rejudge every body after merges.
#[derive(Clone, Debug, PartialEq)]
pub struct SourceCheck {
    body: FuncId,
    instance_key: HostKey,
    input_digest: [u8;32],
    source: CapturedSource,
    evidence: Evidence,
}
impl SourceCheck {
    pub fn body(&self)->FuncId {self.body}
    pub fn instance_key(&self)->&HostKey {&self.instance_key}
    pub fn input_digest(&self)->[u8;32] {self.input_digest}
    pub fn source(&self)->&CapturedSource {&self.source}
    /// Content binding for the actual final source input, never a proof token.
    pub(crate) fn cache_digest(&self)->Result<trust_ir::proof::ProofDigest>{
        let mut bytes=Vec::new();
        bytes.extend_from_slice(&self.body.index().to_le_bytes());bytes.extend_from_slice(&self.input_digest);
        for part in [self.instance_key.namespace.as_bytes(),self.instance_key.bytes.as_slice()] {
            bytes.extend_from_slice(&(part.len()as u64).to_le_bytes());bytes.extend_from_slice(part);
        }
        let source=super::wire::encode(&self.source)?;
        let evidence=crate::rmeta_entry::encode_evidence(&self.evidence);
        for part in [&source,&evidence]{bytes.extend_from_slice(&(part.len()as u64).to_le_bytes());bytes.extend_from_slice(part);}
        Ok(trust_ir::proof::ProofDigest::sha256_domain("trust.rmeta.thir-source-consistency-input.v1",&bytes))
    }
    pub(crate) fn remap(&self, map:&trust_ir_build::merge::Remap)->Result<Self>{
        let mut out=self.clone();
        out.body=map.func(self.body).ok_or_else(||refuse("canonical merge lost a source body"))?;
        for row in &mut out.evidence.ledger {
            row.func_id=map.func(FuncId::new(row.func_id))
                .ok_or_else(||refuse("canonical merge lost a source callee binding"))?.index();
        }
        // This scope refuses producer collapse/degraded/union/placeholder rows
        // before binding, so Evidence has no nominal IR row IDs to remap.
        // Original Rust Type keys/ExprIds remain in their original owner scope.
        Ok(out)
    }
    pub(crate) fn judge(&self,module:&Module)->Result<()> {
        let judged=super::super::retained::judge_source(module,self.body,&self.evidence)
            .map_err(|e|refuse(e.0))?;
        if !judged.tags().is_empty(){return Err(refuse(format!("concrete source consistency tags: {:?}",judged.tags())))}
        let shape=judged.shape();
        let calls=self.evidence.effects.iter().filter(|(e,_)|matches!(e,EvidenceEffectKind::Call(_))).count();
        let stores=self.evidence.effects.iter().filter(|(e,_)|matches!(e,EvidenceEffectKind::Store(_))).count();
        // D28 is deliberately asymmetric. In this closed THIR scope every
        // source call/store must match and the complete cardinalities must
        // agree: extra IR calls/effects cannot be blessed by the asymmetry.
        if shape.direct_calls!=calls || shape.escaping_stores!=stores
            || shape.indirect_calls!=0 || shape.drops!=0 || shape.undefs!=0
            || shape.asm!=0 || shape.suspends!=0 || shape.asserts!=0
        {return Err(refuse("constructed effect population differs from complete closed source scope"))}
        Ok(())
    }
}
fn identity(k:&HostKey)->(String,Vec<u8>){(k.namespace.clone(),k.bytes.clone())}

/// Preserve the original effect input independently of the new THIR claim.
/// This first scope has only unambiguous direct source calls and stores. It
/// refuses other original effects/aliases rather than silently discarding them.
pub(super) fn original_population(original:&Evidence, expected:&super::concrete::OriginalFacts)->Result<()> {
    if expected.unsupported_call {
        return Err(refuse("original associated/trait call association requires typed semantic transport"));
    }
    if original.arg_count as usize!=expected.argument_enum.len()
        || original.arg_enum!=expected.argument_enum || original.ret_enum!=expected.return_enum {
        return Err(refuse("original argument/return value facts differ from actual source metadata"));
    }
    if !original.enum_types.is_empty(){
        return Err(refuse("original enum footprint requires typed semantic transport"));
    }
    let call_key=|c:&EvidenceCall|(c.ids.clone(),c.site.clone(),c.enum_args.clone(),c.enum_result);
    let mut expected_calls=expected.calls.iter().map(call_key).collect::<Vec<_>>();
    let mut original_calls=Vec::new();let mut original_stores=Vec::new();let mut store_index=0;
    let mut exact=BTreeMap::new();
    for &(effect,arg)in &original.exact_store_args{
        let index=usize::try_from(effect).map_err(|_|refuse("original store ordinal exceeds usize"))?;
        if !matches!(original.effects.get(index),Some((EvidenceEffectKind::Store(u32::MAX),_)))
            || arg>=original.arg_count || exact.insert(index,arg).is_some(){
            return Err(refuse("original exact-store fact has no unique indirect source effect"));
        }
    }
    for(index,(effect,_))in original.effects.iter().enumerate(){match effect{
        EvidenceEffectKind::Call(call)=>{
            if call.ids.len()!=1 || call.equivalence.is_some(){
                return Err(refuse("original call alias/equivalence facts require typed semantic transport"));
            }
            original_calls.push(call_key(call));
        }
        EvidenceEffectKind::Store(root)=>{
            let Some(&(value_root,class))=original.store_values.get(store_index)else{return Err(refuse("original store value population is incomplete"))};
            if value_root!=*root{return Err(refuse("original store value is detached from its source root"))}
            original_stores.push((*root,class,exact.get(&index).copied()));store_index+=1;
        }
        _=>return Err(refuse("original non-call/store effects require typed semantic transport")),
    }}
    let mut expected_stores=expected.stores.clone();
    expected_calls.sort();original_calls.sort();expected_stores.sort();original_stores.sort();
    if expected_calls!=original_calls || expected_stores!=original_stores
        || store_index!=original.store_values.len(){
        return Err(refuse("original effect identity/site/value/population differs from actual retained source facts"));
    }
    Ok(())
}

pub(crate) fn bind(source:ConcreteSource<'_>, artifact:&AuthenticatedTemplate,
    module:&Module, children:&[ChildBinding])->Result<SourceCheck>
{
    let original=artifact.evidence();
    original_population(original,&source.original)?;
    // Preserve the original producer limitations explicitly. They are neither
    // converted to false nor inferred away from a newly constructed IR graph.
    if !original.collapsed_enum_types.is_empty() || !original.degraded_structs.is_empty()
        || original.union_lane || original.enum_param_lane
        || original.drop_oracle.as_ref().is_some_and(|d|!d.is_empty())
        || !original.drop_dead_blocks.is_empty()
        || original.drop_claim.as_ref().is_some_and(|(d,n,destructors)|!d.is_empty() || *n!=0 || !destructors.is_empty())
    {return Err(refuse("original producer abstraction/drop facts require typed semantic transport"))}
    let mut holes=BTreeMap::new();let mut declarations=BTreeSet::new();
    for (index,hole) in artifact.template().header.holes.iter().enumerate(){
        if let HoleKind::Callee{decl}=hole.kind {
            if !declarations.insert(decl) || holes.insert(identity(&hole.key),(trust_ir::HoleId::new(index as u32),decl)).is_some(){
                return Err(refuse("duplicate source callee hole key/declaration"));
            }
        }
    }
    let mut actual_children=BTreeMap::new();
    for child in children {
        if holes.get(&identity(&child.original_key))!=Some(&(child.hole,child.declaration))
            || actual_children.insert(child.declaration,child).is_some()
        {return Err(refuse("resolved child is detached from original typed hole/declaration"))}
        if !module.function_by_id(child.declaration).is_some_and(|f|f.is_declaration()) {
            return Err(refuse("format coalesced/lost original callee identity without a retained canonical remap"));
        }
    }
    if actual_children.len()!=holes.len(){return Err(refuse("source callee holes lack complete actual child bindings"))}
    let mut evidence=Evidence {arg_count:source.argument_enum().len() as u32,
        arg_enum:source.argument_enum().to_vec(),ret_enum:source.return_enum(),
        enum_types:source.enum_types().iter().copied().collect(),
        // Complete actual source footprint was checked needs_drop=false. This
        // is not a guessed empty drop oracle from the constructed IR.
        drop_oracle:Some(Vec::new()),drop_claim:Some((Vec::new(),0,Vec::new())),
        ..Default::default()};
    let mut used=BTreeSet::new();let mut ledger=BTreeMap::new();
    for effect in source.effects(){match effect{
        ConcreteEffect::Call(call)=>{
            let key=identity(call.original_key());
            let (_,decl)=holes.get(&key).ok_or_else(||refuse("original THIR call has no exact typed callee hole"))?;
            let child=actual_children.get(decl).ok_or_else(||refuse("original THIR callee has no resolved child"))?;
            if &child.instance_key!=call.resolved_key(){return Err(refuse("actual child instance differs from retained source resolution"))}
            used.insert(key);
            let row=EvidenceLedgerRow{func_id:decl.index(),ids:vec![call.raw_definition],site:Some(call.raw_site.clone())};
            if ledger.insert(*decl,row.clone()).is_some_and(|old|old!=row){return Err(refuse("source calls disagree about a shared declaration identity"))}
            evidence.effects.push((EvidenceEffectKind::Call(EvidenceCall{ids:row.ids,site:row.site,
                equivalence:None,enum_result:call.enum_result,enum_args:call.enum_arguments.clone()}),call.expression));
        }
        ConcreteEffect::Store{expression,root,value_class,exact_argument}=>{
            let code=match root{SourceRoot::Argument(i)=>*i,SourceRoot::Indirect=>u32::MAX};
            if code==u32::MAX {if let Some(arg)=exact_argument{evidence.exact_store_args.push((evidence.effects.len() as u64,*arg));}}
            evidence.effects.push((EvidenceEffectKind::Store(code),*expression));evidence.store_values.push((code,*value_class));
        }
    }}
    if used.len()!=holes.len(){return Err(refuse("callee declaration has no original THIR source-call provenance"))}
    evidence.ledger=ledger.into_values().collect();
    let record=SourceCheck{body:FuncId::new(0),instance_key:source.instance_key().clone(),
        input_digest:artifact.digest(),source:source.source().clone(),evidence};
    // This module is still per-definition plus declarations at this point;
    // reuse the unchanged R judge as well before any body can be merged.
    let judged=super::super::retained::judge(module,&record.evidence).map_err(|e|refuse(e.0))?;
    if !judged.tags().is_empty(){return Err(refuse(format!("concrete source consistency tags: {:?}",judged.tags())))}
    record.judge(module)?;
    Ok(record)
}

pub(crate) fn check_graph(module:&Module, records:&[SourceCheck])->Result<()> {
    let mut bodies=BTreeMap::new();
    for record in records {
        if let Some(old)=bodies.insert(record.body,record){
            if old!=record{return Err(refuse("merged source body has conflicting typed origin/evidence"))}
        }
        record.judge(module)?;
    }
    let defined:BTreeSet<_>=module.functions.iter().filter(|f|!f.is_declaration()).map(|f|f.id).collect();
    if defined!=bodies.keys().copied().collect(){return Err(refuse("closed source graph has an unbound/missing body"))}
    Ok(())
}
