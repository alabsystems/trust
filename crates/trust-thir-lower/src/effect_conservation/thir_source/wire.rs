//! Bounded transport for original THIR data, nested in the expected-owner S2
//! envelope. The enclosing digest binds the complete Rust owner/slot map and
//! template/evidence bytes. Decoding is a compiler-input claim under P-TIR; it
//! does not establish that a malicious producer actually visited the source.
use std::collections::{BTreeMap, BTreeSet};
use trust_ir::{Endianness, StructPassingPolicy, TargetInfo};
use trust_ir::template::HostKey;
use super::{CapturedSource, Result, SourceEffect, SourceNode, SourceNodeKind as K,
    SourceRoot, MAX_SOURCE_DEPTH, MAX_SOURCE_NODES, SOURCE_SCHEMA, refuse};
use crate::template_metadata::OwnerBindings;
pub(super) const MAX_BYTES: usize = 32 * 1024 * 1024;

fn key(key: &HostKey, ty: bool) -> Result<()> {
    let decoded = crate::template_key::decode(key).map_err(|e| refuse(e.to_string()))?;
    if matches!(decoded, crate::template_key::HoleKey::Type(_)) != ty
        || (!ty && !matches!(decoded, crate::template_key::HoleKey::Callee { .. }))
        || crate::template_key::encode(&decoded).map_err(|e| refuse(e.to_string()))? != *key
    { return Err(refuse("source key kind/canonical encoding")); }
    Ok(())
}
/// Structural completeness inside the retained claim, distinct from the P-TIR
/// premise that the original compiler enumerated every actual source node.
pub(crate) fn validate(s: &CapturedSource) -> Result<()> {
    if s.arena_expressions == 0 || s.arena_expressions as usize > MAX_SOURCE_NODES
        || s.root >= s.arena_expressions || s.nodes.is_empty() || s.nodes.len() > MAX_SOURCE_NODES
        || s.types.is_empty() || s.types.len() > MAX_SOURCE_NODES
        || s.argument_types.len() > MAX_SOURCE_NODES || s.effects.len() > MAX_SOURCE_NODES
    { return Err(refuse("source population/root budget")); }
    let valid_type = |i:u32| if (i as usize) < s.types.len() { Ok(()) }
        else { Err(refuse("source type index is absent")) };
    valid_type(s.return_type)?;
    for &i in &s.argument_types { valid_type(i)?; }
    let mut unique_types = BTreeSet::new();
    for t in &s.types {
        key(t, true)?;
        if !unique_types.insert((t.namespace.clone(), t.bytes.clone())) {
            return Err(refuse("duplicate source type key"));
        }
    }
    let mut nodes = BTreeMap::new();
    for n in &s.nodes {
        valid_type(n.ty)?;
        if n.expression >= s.arena_expressions || nodes.insert(n.expression,n).is_some() {
            return Err(refuse("duplicate/out-of-arena source expression"));
        }
        let count = n.children.len();
        let arity = match n.kind {
            K::Literal | K::Variable(_) => count == 0,
            K::Wrapper | K::Dereference | K::NeverCoercion | K::Repeat | K::Cast | K::Not => count == 1,
            K::Bitwise | K::Compare | K::LocalAssignment(_) | K::EscapingStore => count == 2,
            K::Return => count <= 1,
            K::Call => count >= 1,
            K::Block | K::Array | K::Tuple => true,
        };
        if !arity || count > MAX_SOURCE_NODES { return Err(refuse("source node child population")); }
    }
    let mut visit = vec![(s.root,0usize)];let mut seen=BTreeSet::new();let mut preorder=Vec::new();
    while let Some((id,depth))=visit.pop() {
        if depth >= MAX_SOURCE_DEPTH || !seen.insert(id) { return Err(refuse("source graph shared/cyclic/depth")); }
        let n=nodes.get(&id).ok_or_else(||refuse("source child/root is absent"))?;
        preorder.push(id);
        for &child in n.children.iter().rev(){visit.push((child,depth+1));}
    }
    if preorder != s.nodes.iter().map(|n|n.expression).collect::<Vec<_>>()
        || nodes.get(&s.root).is_none_or(|n|n.ty != s.return_type)
    { return Err(refuse("source graph contains unrooted/reordered rows or return type differs")); }
    if s.argument_variables.len()!=s.argument_types.len(){return Err(refuse("source argument/variable population"))}
    let mut parameter_variables=BTreeMap::new();
    for (i,var) in s.argument_variables.iter().enumerate(){if let Some(v)=var{
        if parameter_variables.insert(*v,i as u32).is_some(){return Err(refuse("duplicate source parameter variable"))}
    }}
    let modified:BTreeSet<_>=s.modified_variables.iter().copied().collect();
    if modified.len()!=s.modified_variables.len() || s.nodes.iter().any(|n|matches!(n.kind,K::LocalAssignment(v)if !modified.contains(&v))){
        return Err(refuse("source assignment/modified-variable population"));
    }
    let plain_variable=|mut id:u32|->Option<u32>{for _ in 0..MAX_SOURCE_DEPTH{
        let n=nodes.get(&id)?;match n.kind{K::Wrapper=>id=*n.children.first()?,K::Variable(v)=>return Some(v),_=>return None}
    }None};
    let argument_of=|id:u32|plain_variable(id).filter(|v|!modified.contains(v))
        .and_then(|v|parameter_variables.get(&v).copied());
    for n in &s.nodes {
        if let K::Variable(v)=n.kind {
            if parameter_variables.get(&v).is_some_and(|&i|s.argument_types[i as usize]!=n.ty) {
                return Err(refuse("source parameter variable type differs from its original argument"));
            }
        }
    }
    let mut effect_index=0;
    for n in &s.nodes {
        if !matches!(n.kind,K::Call|K::EscapingStore){continue}
        match s.effects.get(effect_index) {
            Some(SourceEffect::Call{expression,key:callee,argument_types,result_type}) if n.kind==K::Call => {
                key(callee,false)?;valid_type(*result_type)?;
                if *expression != n.expression || *result_type != n.ty || n.children.len()!=argument_types.len()+1 {
                    return Err(refuse("source call is detached from its original node/types/children"));
                }
                let operand=nodes[&n.children[0]];
                let operand=crate::template_key::decode(&s.types[operand.ty as usize]).map_err(|e|refuse(e.to_string()))?;
                let crate::template_key::HoleKey::Type(crate::template_key::KeyTy::FnDef(item,args))=operand else {
                    return Err(refuse("source direct call has no original FnDef operand type"));
                };
                if crate::template_key::decode(callee).map_err(|e|refuse(e.to_string()))?
                    != (crate::template_key::HoleKey::Callee{item,args}) {
                    return Err(refuse("source callee key differs from its original FnDef operand"));
                }
                for (&i,child) in argument_types.iter().zip(n.children.iter().skip(1)) {
                    valid_type(i)?;
                    if nodes.get(child).is_none_or(|c|c.ty!=i){return Err(refuse("source call type differs from its actual argument child"))}
                }
            }
            Some(SourceEffect::Store{expression,root,value_type,exact_argument}) if n.kind==K::EscapingStore => {
                valid_type(*value_type)?;
                let mut lhs=n.children[0];
                for _ in 0..MAX_SOURCE_DEPTH{let place=nodes[&lhs];if place.kind!=K::Wrapper{break}lhs=place.children[0];}
                let place=nodes[&lhs];
                if place.kind!=K::Dereference || nodes[&n.children[1]].ty!=*value_type {
                    return Err(refuse("source store lost its original dereference/value child"));
                }
                let actual_root=argument_of(place.children[0]);
                let derived_root=actual_root.map(SourceRoot::Argument).unwrap_or(SourceRoot::Indirect);
                if *root!=derived_root || *exact_argument!=argument_of(n.children[1]) {
                    return Err(refuse("source store root/value argument differs from original variables"));
                }
                if *expression != n.expression || matches!(root,SourceRoot::Argument(i) if *i as usize>=s.argument_types.len())
                    || exact_argument.is_some_and(|i|i as usize>=s.argument_types.len())
                {return Err(refuse("source store is detached from its original node/arguments"));}
            }
            _=>return Err(refuse("source call/store population differs from complete source nodes")),
        }
        effect_index+=1;
    }
    if effect_index != s.effects.len(){return Err(refuse("extra source effect without an original source node"));}
    Ok(())
}
struct W(Vec<u8>);
impl W {
    fn u8(&mut self,x:u8){self.0.push(x)}
    fn u32(&mut self,x:u32){self.0.extend_from_slice(&x.to_le_bytes())}
    fn bytes(&mut self,x:&[u8]){self.u32(x.len() as u32);self.0.extend_from_slice(x)}
    fn key(&mut self,k:&HostKey){self.bytes(k.namespace.as_bytes());self.bytes(&k.bytes)}
    fn indices(&mut self,x:&[u32]){self.u32(x.len() as u32);for &i in x{self.u32(i)}}
}
pub(crate) fn encode(s:&CapturedSource)->Result<Vec<u8>> {
    validate(s)?;
    let mut size = s.target.triple.len().saturating_add(s.target.abi.as_ref().map_or(0,|s|s.len()))
        .saturating_add(s.nodes.len().saturating_mul(32)).saturating_add(s.types.len().saturating_mul(8))
        .saturating_add(s.argument_types.len().saturating_mul(12)).saturating_add(s.modified_variables.len().saturating_mul(4));
    for k in s.types.iter().chain(s.effects.iter().filter_map(|e|match e{SourceEffect::Call{key,..}=>Some(key),_=>None})) {
        size=size.saturating_add(k.namespace.len()).saturating_add(k.bytes.len()).saturating_add(16);
    }
    for e in &s.effects{size=size.saturating_add(match e{SourceEffect::Call{argument_types,..}=>24usize.saturating_add(argument_types.len().saturating_mul(4)),_=>24});}
    if size>MAX_BYTES{return Err(refuse("source wire byte budget"))}
    let mut w=W(Vec::with_capacity(size));w.u32(SOURCE_SCHEMA);
    w.bytes(s.target.triple.as_bytes());w.u32(s.target.pointer_size);
    w.u8(match s.target.endianness{Endianness::Little=>0,Endianness::Big=>1});
    match &s.target.abi{None=>w.u8(0),Some(a)=>{w.u8(1);w.bytes(a.as_bytes())}}
    w.u8(match s.target.struct_passing{StructPassingPolicy::NativeC=>0,StructPassingPolicy::AlwaysMemory=>1,StructPassingPolicy::Unclassified=>2});
    w.u8(u8::from(s.overflow_checks));w.u32(s.root);w.u32(s.arena_expressions);
    w.indices(&s.argument_types);
    w.u32(s.argument_variables.len() as u32);for v in &s.argument_variables{match v{None=>w.u8(0),Some(v)=>{w.u8(1);w.u32(*v)}}}
    w.indices(&s.modified_variables);w.u32(s.return_type);w.u32(s.types.len() as u32);
    for k in &s.types{w.key(k)}
    w.u32(s.nodes.len() as u32);
    for n in &s.nodes {
        w.u32(n.expression);w.u32(n.ty);
        let (tag,data)=match n.kind{K::Wrapper=>(0,None),K::Block=>(1,None),K::Literal=>(2,None),K::Variable(v)=>(3,Some(v)),K::Return=>(4,None),K::Array=>(5,None),K::Tuple=>(6,None),K::Repeat=>(7,None),K::Cast=>(8,None),K::Not=>(9,None),K::Bitwise=>(10,None),K::Compare=>(11,None),K::LocalAssignment(v)=>(12,Some(v)),K::Call=>(13,None),K::EscapingStore=>(14,None),K::Dereference=>(15,None),K::NeverCoercion=>(16,None)};
        w.u8(tag);if let Some(v)=data{w.u32(v)}w.indices(&n.children);
    }
    w.u32(s.effects.len() as u32);
    for e in &s.effects{match e{
        SourceEffect::Call{expression,key,argument_types,result_type}=>{w.u8(0);w.u32(*expression);w.key(key);w.indices(argument_types);w.u32(*result_type)}
        SourceEffect::Store{expression,root,value_type,exact_argument}=>{w.u8(1);w.u32(*expression);w.u32(match root{SourceRoot::Argument(i)=>*i,SourceRoot::Indirect=>u32::MAX});w.u32(*value_type);match exact_argument{None=>w.u8(0),Some(i)=>{w.u8(1);w.u32(*i)}}}
    }}
    if w.0.len()>MAX_BYTES{return Err(refuse("source wire byte budget"))}Ok(w.0)
}
struct R<'a>{b:&'a[u8],at:usize}
impl<'a> R<'a>{
 fn take(&mut self,n:usize)->Result<&'a[u8]>{let end=self.at.checked_add(n).ok_or_else(||refuse("source length overflow"))?;let b=self.b.get(self.at..end).ok_or_else(||refuse("truncated source facts"))?;self.at=end;Ok(b)}
 fn u8(&mut self)->Result<u8>{Ok(self.take(1)?[0])}
 fn u32(&mut self)->Result<u32>{Ok(u32::from_le_bytes(self.take(4)?.try_into().unwrap()))}
 fn count(&mut self)->Result<usize>{let n=self.u32()? as usize;if n>MAX_SOURCE_NODES || n>self.b.len().saturating_sub(self.at){return Err(refuse("source collection budget"))}Ok(n)}
 fn bytes(&mut self)->Result<&'a[u8]>{let n=self.u32()? as usize;self.take(n)}
 fn text(&mut self)->Result<String>{String::from_utf8(self.bytes()?.to_vec()).map_err(|_|refuse("source text encoding"))}
 fn key(&mut self)->Result<HostKey>{Ok(HostKey::new(self.text()?,self.bytes()?.to_vec()))}
 fn indices(&mut self)->Result<Vec<u32>>{let n=self.count()?;(0..n).map(|_|self.u32()).collect()}
}
pub(crate) fn decode(bytes:&[u8],expected:&OwnerBindings)->Result<CapturedSource>{
 if bytes.len()>MAX_BYTES{return Err(refuse("source wire byte budget"))}
 let mut r=R{b:bytes,at:0};if r.u32()?!=SOURCE_SCHEMA{return Err(refuse("source schema"))}
 let triple=r.text()?;let pointer_size=r.u32()?;
 let endianness=match r.u8()?{0=>Endianness::Little,1=>Endianness::Big,_=>return Err(refuse("source endianness"))};
 let abi=match r.u8()?{0=>None,1=>Some(r.text()?),_=>return Err(refuse("source ABI presence"))};
 let struct_passing=match r.u8()?{0=>StructPassingPolicy::NativeC,1=>StructPassingPolicy::AlwaysMemory,2=>StructPassingPolicy::Unclassified,_=>return Err(refuse("source aggregate policy"))};
 let overflow_checks=match r.u8()?{0=>false,1=>true,_=>return Err(refuse("source overflow mode"))};
 let root=r.u32()?;let arena_expressions=r.u32()?;let argument_types=r.indices()?;
 let count=r.count()?;let mut argument_variables=Vec::with_capacity(count);
 for _ in 0..count{argument_variables.push(match r.u8()?{0=>None,1=>Some(r.u32()?),_=>return Err(refuse("source argument variable presence"))});}
 let modified_variables=r.indices()?;let return_type=r.u32()?;
 let count=r.count()?;let types=(0..count).map(|_|r.key()).collect::<Result<Vec<_>>>()?;
 let count=r.count()?;let mut nodes=Vec::with_capacity(count);
 for _ in 0..count{let expression=r.u32()?;let ty=r.u32()?;let kind=match r.u8()?{0=>K::Wrapper,1=>K::Block,2=>K::Literal,3=>K::Variable(r.u32()?),4=>K::Return,5=>K::Array,6=>K::Tuple,7=>K::Repeat,8=>K::Cast,9=>K::Not,10=>K::Bitwise,11=>K::Compare,12=>K::LocalAssignment(r.u32()?),13=>K::Call,14=>K::EscapingStore,15=>K::Dereference,16=>K::NeverCoercion,_=>return Err(refuse("unknown source node kind"))};let children=r.indices()?;nodes.push(SourceNode{expression,ty,kind,children});}
 let count=r.count()?;let mut effects=Vec::with_capacity(count);
 for _ in 0..count{effects.push(match r.u8()?{
  0=>SourceEffect::Call{expression:r.u32()?,key:r.key()?,argument_types:r.indices()?,result_type:r.u32()?},
  1=>{let expression=r.u32()?;let root=match r.u32()?{u32::MAX=>SourceRoot::Indirect,i=>SourceRoot::Argument(i)};let value_type=r.u32()?;let exact_argument=match r.u8()?{0=>None,1=>Some(r.u32()?),_=>return Err(refuse("source exact argument presence"))};SourceEffect::Store{expression,root,value_type,exact_argument}},
  _=>return Err(refuse("unknown source effect kind")),
 });}
 if r.at!=bytes.len(){return Err(refuse("source trailing bytes"))}
 let s=CapturedSource{bindings:expected.clone(),target:TargetInfo{triple,pointer_size,endianness,abi,struct_passing},overflow_checks,root,arena_expressions,argument_types,argument_variables,modified_variables,return_type,types,nodes,effects};
 validate(&s)?;if encode(&s)?!=bytes{return Err(refuse("source noncanonical wire encoding"))}Ok(s)
}
