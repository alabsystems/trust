//! Authenticated Rust binding for a level-S metadata artifact.
//!
//! The digest binds content, not the honesty of the producing compiler. As for
//! level-R metadata, Rustc's loaded crate/definition is the independent source
//! of owner and positional generic identities (P-TIR). This module grants no
//! conservation, body, ABI, codegen or proof authority.

use std::collections::BTreeSet;

use trust_ir::proof::ProofDigest;
use trust_ir::template::{HoleKind, Template, TemplateArg, TemplateParam};
use trust_ir::{ConstantG, ParamId, TemplateRef, Ty, TyG};

use crate::rmeta_entry::{self, Evidence};
use crate::template_key::{self, HoleKey, StableDef};

pub mod callable_header;
mod unit_return;
pub mod const_host;
pub mod type_host;
pub mod instantiate;
/// Diagnostic template-instance equivalence TEST-ORACLE (PKG-C2d2 slice 1); no authority.
pub mod oracle;
pub mod rustc;

pub const MAGIC: &[u8; 8] = b"TRIRTMPL";
pub const SCHEMA: u32 = 1;
/// S2 adds retained typed THIR facts. S1 readers reject it at the schema gate.
pub const SOURCE_SCHEMA: u32 = 2;
const DOMAIN: &str = "trust.rmeta.template-envelope.v1";
const MAX_BYTES: usize = 64 * 1024 * 1024;
const MAX_SLOTS: usize = 65536;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OwnerBindings {
    pub owner: StableDef,
    /// Every original GenericArgs position, including erased lifetimes.
    pub slots: Vec<GenericSlot>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GenericSlot {
    pub definition: StableDef,
    pub kind: SlotKind,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SlotKind {
    Lifetime,
    Type(ParamId),
    Const { param: ParamId, ty: Ty },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MetadataError(pub String);
impl std::fmt::Display for MetadataError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}
impl std::error::Error for MetadataError {}
type Result<T> = std::result::Result<T, MetadataError>;
fn err(s: impl Into<String>) -> MetadataError {
    MetadataError(s.into())
}

/// Only an expected-owner read constructs this type; a self-reported owner is
/// never sufficient. It is an authenticated compiler-input artifact, not a
/// codegen/admission token. The level-S module cannot enter level-R consumers.
#[derive(Debug)]
pub struct AuthenticatedTemplate {
    bindings: OwnerBindings,
    template: Template,
    evidence: Evidence,
    digest: [u8; 32],
    overflow_checks: bool,
    source: Option<SourceRetention>,
}
/// Retained input data only. An unavailable capture stays a named refusal;
/// it can never be replaced by a census of the constructed module.
#[derive(Clone, Debug, PartialEq)]
pub enum SourceRetention {
    Captured(crate::effect_conservation::thir_source::CapturedSource),
    Unavailable(String),
}
impl AuthenticatedTemplate {
    pub fn bindings(&self) -> &OwnerBindings {
        &self.bindings
    }
    pub fn template(&self) -> &Template {
        &self.template
    }
    pub fn evidence(&self) -> &Evidence {
        &self.evidence
    }
    pub fn digest(&self) -> [u8; 32] {
        self.digest
    }
    pub fn source(&self) -> Option<&SourceRetention> { self.source.as_ref() }
    pub fn overflow_checks(&self) -> bool {
        self.overflow_checks
    }
}

fn scalar_tag(t: &Ty) -> Result<u8> {
    Ok(match t {
        Ty::Bool => 0,
        Ty::Char => 1,
        Ty::I8 => 2,
        Ty::I16 => 3,
        Ty::I32 => 4,
        Ty::I64 => 5,
        Ty::I128 => 6,
        Ty::Isize => 7,
        Ty::U8 => 8,
        Ty::U16 => 9,
        Ty::U32 => 10,
        Ty::U64 => 11,
        Ty::U128 => 12,
        Ty::Usize => 13,
        _ => return Err(err("template const slot has no scalar type")),
    })
}
fn scalar_ty(tag: u8) -> Result<Ty> {
    Ok(match tag {
        0 => Ty::Bool,
        1 => Ty::Char,
        2 => Ty::I8,
        3 => Ty::I16,
        4 => Ty::I32,
        5 => Ty::I64,
        6 => Ty::I128,
        7 => Ty::Isize,
        8 => Ty::U8,
        9 => Ty::U16,
        10 => Ty::U32,
        11 => Ty::U64,
        12 => Ty::U128,
        13 => Ty::Usize,
        _ => return Err(err("unknown template const slot type")),
    })
}

/// Reconstruct every dependency from the full owner map, independently of the
/// producer's compact-parameter bookkeeping. A same-kind permutation refuses.
fn dependency(bindings: &OwnerBindings, index: u32) -> Result<TemplateArg> {
    let slot = bindings
        .slots
        .get(index as usize)
        .ok_or_else(|| err("template key parameter outside owner slots"))?;
    Ok(match &slot.kind {
        SlotKind::Lifetime => return Err(err("template key uses a lifetime as a value parameter")),
        SlotKind::Type(p) => TemplateArg::Type(TyG::Ext(TemplateRef::Param(*p))),
        SlotKind::Const { param, ty } => {
            TemplateArg::Const { value: ConstantG::Ext(TemplateRef::Param(*param)), ty: ty.clone() }
        }
    })
}

pub fn validate_bindings(
    bindings: &OwnerBindings,
    template: &Template,
    evidence: &Evidence,
) -> Result<()> {
    if !template
        .module
        .functions
        .first()
        .is_some_and(|f| f.producer == Some(trust_ir::Producer::TRust))
    {
        return Err(err("Rust template body has no Rust producer binding"));
    }
    let body = &template.module.functions[0];
    let signature = template
        .module
        .func_types
        .get(body.ty.as_usize())
        .ok_or_else(|| err("Rust template body has no signature"))?;
    // The retained census and the source template describe the same ordinary
    // function inputs, before ABI lowering. Binding both counts prevents a
    // rehashed envelope from detaching argument-indexed evidence from them.
    if evidence.arg_count as usize != signature.params.len()
        || evidence.arg_enum.len() != signature.params.len()
    {
        return Err(err("template evidence argument count differs from its body signature"));
    }
    // Keep every declared edge, including declarations not reached by a call
    // instruction. A per-hole lookup alone misses extra evidence or ground
    // declarations whose ledger row was removed.
    let declarations: BTreeSet<_> = template
        .module
        .functions
        .iter()
        .filter(|f| f.blocks.is_empty())
        .map(|f| f.id.index())
        .collect();
    let mut retained = BTreeSet::new();
    for row in &evidence.ledger {
        if !declarations.contains(&row.func_id) || !retained.insert(row.func_id) {
            return Err(err("template retained ledger has an extra or duplicate declaration row"));
        }
    }
    if retained != declarations {
        return Err(err("template declaration has no retained ledger row"));
    }
    if bindings.slots.len() > MAX_SLOTS {
        return Err(err("template owner slot budget"));
    }
    let mut next = 0;
    for slot in &bindings.slots {
        let expected = match &slot.kind {
            SlotKind::Lifetime => continue,
            SlotKind::Type(p) => {
                if p.as_usize() != next {
                    return Err(err("template type slot order"));
                }
                TemplateParam::Type
            }
            SlotKind::Const { param, ty } => {
                if param.as_usize() != next {
                    return Err(err("template const slot order"));
                }
                scalar_tag(ty)?;
                TemplateParam::Const { ty: ty.clone() }
            }
        };
        if template.header.params.get(next) != Some(&expected) {
            return Err(err("template slot kind/type mismatch"));
        }
        next += 1;
    }
    if next != template.header.params.len() {
        return Err(err("template slots omit a parameter"));
    }
    for hole in &template.header.holes {
        let key =
            template_key::decode(&hole.key).map_err(|e| err(format!("template host key: {e}")))?;
        let expected = template_key::parameters(&key)
            .map_err(|e| err(e.to_string()))?
            .into_iter()
            .map(|i| dependency(bindings, i))
            .collect::<Result<Vec<_>>>()?;
        if hole.args != expected {
            return Err(err("template hole dependencies differ from owner slots"));
        }
        match (&hole.kind, key) {
            (HoleKind::Callee { decl }, HoleKey::Callee { item, .. }) => {
                let mut rows = evidence.ledger.iter().filter(|r| r.func_id == decl.index());
                let row =
                    rows.next().ok_or_else(|| err("template callee has no retained ledger row"))?;
                if rows.next().is_some() || row.ids != [item] || row.site.is_some() {
                    return Err(err("template typed callee/retained ledger mismatch"));
                }
            }
            (HoleKind::Const { ty }, HoleKey::Const(_))
                if trust_ir::template::is_template_scalar(ty) => {}
            (HoleKind::Type { .. }, HoleKey::Type(_)) => {}
            _ => return Err(err("unsupported Rust template hole kind")),
        }
    }
    let violations = trust_ir_build::template::validate_template(template);
    if !violations.is_empty() {
        return Err(err(format!("invalid level-S template: {violations:?}")));
    }
    Ok(())
}

fn u32v(out: &mut Vec<u8>, v: u32) {
    out.extend_from_slice(&v.to_le_bytes());
}
fn u64v(out: &mut Vec<u8>, v: u64) {
    out.extend_from_slice(&v.to_le_bytes());
}
fn def(out: &mut Vec<u8>, v: StableDef) {
    u64v(out, v.0);
    u64v(out, v.1);
}
fn part(out: &mut Vec<u8>, v: &[u8]) {
    u64v(out, v.len() as u64);
    out.extend_from_slice(v);
}
fn content_digest(header: &[u8], payload: &[u8]) -> [u8; 32] {
    let mut bytes = Vec::with_capacity(header.len() + payload.len());
    bytes.extend_from_slice(header);
    bytes.extend_from_slice(payload);
    ProofDigest::sha256_domain(DOMAIN, &bytes).bytes
}

/// Frame only a source-bound, independently validated S artifact. Existing R
/// entry/evidence schemas are unchanged. Evidence and every dependency live
/// inside the content digest, together with the owner/map/schema/overflow mode.
pub fn frame(
    bindings: &OwnerBindings,
    template: &Template,
    overflow_checks: bool,
    evidence_bytes: &[u8],
) -> Result<Vec<u8>> {
    frame_inner(bindings, template, overflow_checks, evidence_bytes, None)
}

/// Frame genuine source facts beside an unlicensed template. This checks data
/// custody/coverage, not source refinement. A caller still owes the actual
/// lowering, producer abstractions, concrete metadata and shared judgement.
pub fn frame_with_source(
    bindings: &OwnerBindings, template: &Template, overflow_checks: bool,
    evidence_bytes: &[u8], source: &crate::effect_conservation::thir_source::CapturedSource,
) -> Result<Vec<u8>> {
    frame_inner(bindings, template, overflow_checks, evidence_bytes,
        Some(&SourceRetention::Captured(source.clone())))
}

pub(crate) fn frame_recorded(
    tcx: rustc_middle::ty::TyCtxt<'_>, owner: rustc_span::def_id::LocalDefId,
    bindings: &OwnerBindings, template: &Template, overflow_checks: bool, evidence_bytes: &[u8],
) -> Result<Vec<u8>> {
    let source = match crate::effect_conservation::thir_source::recorded(tcx, owner) {
        Ok(s) => SourceRetention::Captured(s), Err(e) => SourceRetention::Unavailable(e.0),
    };
    frame_inner(bindings, template, overflow_checks, evidence_bytes, Some(&source))
}

fn frame_inner(bindings: &OwnerBindings, template: &Template, overflow_checks: bool,
    evidence_bytes: &[u8], source: Option<&SourceRetention>) -> Result<Vec<u8>> {
    if evidence_bytes.len() > MAX_BYTES {
        return Err(err("template evidence byte budget"));
    }
    let evidence = rmeta_entry::decode_evidence(evidence_bytes)
        .map_err(|e| err(format!("template evidence: {e}")))?;
    validate_bindings(bindings, template, &evidence)?;
    let bytes = trust_ir::binary::serialize_template(template)
        .map_err(|e| err(format!("template codec: {e}")))?;
    let digest = template.digest().map_err(|e| err(e.to_string()))?;
    let mut payload = Vec::new();
    def(&mut payload, bindings.owner);
    payload.push(u8::from(overflow_checks));
    u32v(&mut payload, bindings.slots.len() as u32);
    for slot in &bindings.slots {
        def(&mut payload, slot.definition);
        match &slot.kind {
            SlotKind::Lifetime => payload.push(0),
            SlotKind::Type(p) => {
                payload.push(1);
                u32v(&mut payload, p.index());
            }
            SlotKind::Const { param, ty } => {
                payload.push(2);
                u32v(&mut payload, param.index());
                payload.push(scalar_tag(ty)?);
            }
        }
    }
    payload.extend_from_slice(&digest.bytes);
    part(&mut payload, &bytes);
    part(&mut payload, evidence_bytes);
    if let Some(source) = source {
        match source {
            SourceRetention::Captured(s) => {
                if s.bindings() != bindings || s.overflow_checks() != overflow_checks
                    || template.module.target_info.as_ref() != Some(s.target()) {
                    return Err(err("template source owner/mode/target mismatch"));
                }
                payload.push(1);
                part(&mut payload, &crate::effect_conservation::thir_source::wire::encode(s)
                    .map_err(|e| err(e.0))?);
            }
            SourceRetention::Unavailable(reason) => { payload.push(0); part(&mut payload, reason.as_bytes()); }
        }
    }
    let mut out = MAGIC.to_vec();
    u32v(&mut out, if source.is_some() { SOURCE_SCHEMA } else { SCHEMA });
    u32v(&mut out, trust_ir::binary::VERSION);
    if payload.len() > MAX_BYTES {
        return Err(err("template metadata byte budget"));
    }
    let digest = content_digest(&out, &payload);
    out.extend_from_slice(&digest);
    part(&mut out, &payload);
    Ok(out)
}

struct Reader<'a> {
    bytes: &'a [u8],
    at: usize,
}
impl<'a> Reader<'a> {
    fn take(&mut self, n: usize) -> Result<&'a [u8]> {
        let end = self.at.checked_add(n).ok_or_else(|| err("template length overflow"))?;
        let p = self.bytes.get(self.at..end).ok_or_else(|| err("truncated template metadata"))?;
        self.at = end;
        Ok(p)
    }
    fn byte(&mut self) -> Result<u8> {
        Ok(self.take(1)?[0])
    }
    fn u32(&mut self) -> Result<u32> {
        Ok(u32::from_le_bytes(self.take(4)?.try_into().unwrap()))
    }
    fn u64(&mut self) -> Result<u64> {
        Ok(u64::from_le_bytes(self.take(8)?.try_into().unwrap()))
    }
    fn def(&mut self) -> Result<StableDef> {
        Ok((self.u64()?, self.u64()?))
    }
    fn part(&mut self) -> Result<&'a [u8]> {
        let n = usize::try_from(self.u64()?)
            .map_err(|_| err("template length exceeds target usize"))?;
        self.take(n)
    }
    fn finish(&self) -> Result<()> {
        if self.at != self.bytes.len() { Err(err("template trailing bytes")) } else { Ok(()) }
    }
}

/// Verify whole-content identity BEFORE interpreting template/evidence bytes.
/// The caller supplies bindings independently derived from the requested Rust
/// definition, never from the envelope. No unchecked/self-binding decode API.
pub fn read(
    bytes: &[u8],
    expected: &OwnerBindings,
    overflow_checks: bool,
) -> Result<AuthenticatedTemplate> {
    if bytes.len() > MAX_BYTES + 56 {
        return Err(err("template metadata byte budget"));
    }
    let mut r = Reader { bytes, at: 0 };
    if r.take(8)? != MAGIC {
        return Err(err("template magic"));
    }
    let schema = r.u32()?;
    if schema != SCHEMA && schema != SOURCE_SCHEMA { return Err(err("template schema")); }
    if r.u32()? != trust_ir::binary::VERSION {
        return Err(err("template trust-ir version"));
    }
    let digest: [u8; 32] = r.take(32)?.try_into().unwrap();
    let payload = r.part()?;
    r.finish()?;
    if content_digest(&bytes[..16], payload) != digest {
        return Err(err("template content digest"));
    }
    let mut r = Reader { bytes: payload, at: 0 };
    let owner = r.def()?;
    if owner != expected.owner {
        return Err(err("template requested owner mismatch"));
    }
    let overflow = match r.byte()? {
        0 => false,
        1 => true,
        _ => return Err(err("template overflow-check byte")),
    };
    if overflow != overflow_checks {
        return Err(err("template overflow-check mode mismatch"));
    }
    let count = r.u32()? as usize;
    if count > MAX_SLOTS || count != expected.slots.len() {
        return Err(err("template owner slot count mismatch"));
    }
    let mut slots = Vec::with_capacity(count);
    for wanted in &expected.slots {
        let definition = r.def()?;
        let kind = match r.byte()? {
            0 => SlotKind::Lifetime,
            1 => SlotKind::Type(ParamId::new(r.u32()?)),
            2 => SlotKind::Const { param: ParamId::new(r.u32()?), ty: scalar_ty(r.byte()?)? },
            _ => return Err(err("unknown template slot kind")),
        };
        let slot = GenericSlot { definition, kind };
        if &slot != wanted {
            return Err(err("template requested positional binding mismatch"));
        }
        slots.push(slot);
    }
    let template_digest: [u8; 32] = r.take(32)?.try_into().unwrap();
    let template_bytes = r.part()?;
    let evidence_bytes = r.part()?;
    let source = if schema == SOURCE_SCHEMA {
        Some(match r.byte()? {
            0 => SourceRetention::Unavailable(std::str::from_utf8(r.part()?)
                .map_err(|_| err("template source refusal text"))?.to_string()),
            1 => SourceRetention::Captured(crate::effect_conservation::thir_source::wire::decode(r.part()?, expected)
                .map_err(|e| err(e.0))?),
            _ => return Err(err("template source retention kind")),
        })
    } else { None };
    r.finish()?;
    let template = trust_ir::binary::deserialize_template(template_bytes)
        .map_err(|e| err(format!("template decode: {e:?}")))?;
    if template.digest().map_err(|e| err(e.to_string()))?.bytes != template_digest {
        return Err(err("template module digest mismatch"));
    }
    let evidence = rmeta_entry::decode_evidence(evidence_bytes)
        .map_err(|e| err(format!("template evidence: {e}")))?;
    let bindings = OwnerBindings { owner, slots };
    validate_bindings(&bindings, &template, &evidence)?;
    if let Some(SourceRetention::Captured(s)) = &source {
        if s.overflow_checks() != overflow || template.module.target_info.as_ref() != Some(s.target()) {
            return Err(err("template source mode/target mismatch"));
        }
    }
    Ok(AuthenticatedTemplate { bindings, template, evidence, digest, overflow_checks: overflow, source })
}

#[cfg(test)]
mod tests;
