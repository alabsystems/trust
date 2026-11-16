//! Re-derive D28 over a decoded level-R body and its retained source facts.
//!
//! The matcher/census/drop algorithms are the source lane's own algorithms,
//! parameterized by stable definitions, injective site tokens and span ordinals.
//! No Rustc DefId/span is fabricated and no verdict bit is imported. P-TIR is
//! still the premise that these facts came from the producing compiler; this
//! checks effect consistency, not source refinement or codegen/proof authority.

use std::collections::{BTreeMap, BTreeSet};

use trust_ir::{FuncId, Module, Producer, StructId};

use super::{
    AssertClass, Effect, EffectShape, Equivalence, IrCensus, Lane, LedgerRow, LedgeredLanes,
    MemRoot, MirCensus, MirEffect, MirEffectKind, StoreValue, Tag, TagKind,
};
use crate::rmeta_entry::{
    Evidence, EvidenceDropKey, EvidenceEffectKind, EvidenceOracleDrop, StableDef,
};

type Census = MirCensus<StableDef, String, u32, EvidenceOracleDrop>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EvidenceRefusal(pub String);
impl std::fmt::Display for EvidenceRefusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}
impl std::error::Error for EvidenceRefusal {}
type Result<T> = std::result::Result<T, EvidenceRefusal>;
fn refuse(reason: impl Into<String>) -> EvidenceRefusal {
    EvidenceRefusal(reason.into())
}

/// A consistency result only. Neither this type nor an empty tag list licenses
/// a body: the upstream reader must independently bind Rust identity/signature,
/// resolve declarations, and enter the sealed strict-output admission route.
pub struct RetainedJudgement {
    tags: Vec<Tag>,
    equivalences: BTreeMap<&'static str, usize>,
    shape: EffectShape,
}
impl RetainedJudgement {
    pub fn tags(&self) -> &[Tag] {
        &self.tags
    }
    pub fn equivalences(&self) -> &BTreeMap<&'static str, usize> {
        &self.equivalences
    }
    pub fn shape(&self) -> EffectShape {
        self.shape
    }
}

fn root(code: u32, arguments: u32) -> Result<MemRoot> {
    match code {
        u32::MAX => Ok(MemRoot::Indirect),
        n if n == u32::MAX - 1 => Ok(MemRoot::Static),
        n if n < arguments => Ok(MemRoot::Arg(n)),
        _ => Err(refuse("retained store names an absent source argument")),
    }
}
fn equivalence(code: u8) -> Result<Equivalence> {
    // Existing evidence-schema numbers, including BoolFromInteger appended at9.
    Ok(match code {
        0 => Equivalence::PureIntrinsic,
        1 => Equivalence::SliceLen,
        2 => Equivalence::RangeIntoIter,
        3 => Equivalence::RangeNext,
        4 => Equivalence::OptionDiscriminant,
        5 => Equivalence::TryBranch,
        6 => Equivalence::TryResidual,
        7 => Equivalence::BuiltinEq,
        8 => Equivalence::FormatArguments,
        9 => Equivalence::BoolFromInteger,
        _ => return Err(refuse("retained call has an unknown equivalence class")),
    })
}
fn assert_class(code: u8) -> Result<AssertClass> {
    Ok(match code {
        0 => AssertClass::Bounds,
        1 => AssertClass::Overflow,
        2 => AssertClass::Shift,
        3 => AssertClass::DivZero,
        4 => AssertClass::Other,
        _ => return Err(refuse("retained assert has an unknown class")),
    })
}
fn store_value(code: u8) -> Result<StoreValue> {
    Ok(match code {
        0 => StoreValue::ValuedEnum,
        1 => StoreValue::BoolOrUnit,
        2 => StoreValue::Other,
        _ => return Err(refuse("retained store has an unknown value class")),
    })
}
fn unique<T: Ord + Copy>(values: &[T], name: &str) -> Result<BTreeSet<T>> {
    let set: BTreeSet<_> = values.iter().copied().collect();
    if set.len() != values.len() {
        return Err(refuse(format!("retained {name} has duplicate rows")));
    }
    Ok(set)
}
fn drop_identity(identity: (u8, u32), arguments: u32) -> Result<()> {
    match identity {
        (0, n) if n < arguments => Ok(()),
        (1, _) | (2, 0) => Ok(()),
        _ => Err(refuse("retained drop has an invalid place identity")),
    }
}

fn census(e: &Evidence) -> Result<Census> {
    if e.arg_enum.len() != e.arg_count as usize {
        return Err(refuse("retained argument enum facts have the wrong population"));
    }
    let effects = e
        .effects
        .iter()
        .map(|(kind, span)| {
            let kind = match kind {
                EvidenceEffectKind::Call(call) => {
                    if call.ids.is_empty() {
                        return Err(refuse("retained direct call has no identity"));
                    }
                    MirEffectKind::Call {
                        ids: call.ids.clone(),
                        site_args: call.site.clone(),
                        equivalence: call.equivalence.map(equivalence).transpose()?,
                        enum_result: call.enum_result,
                        enum_args: call.enum_args.clone(),
                    }
                }
                EvidenceEffectKind::IndirectCall => MirEffectKind::IndirectCall,
                EvidenceEffectKind::Store(code) => MirEffectKind::Store(root(*code, e.arg_count)?),
                EvidenceEffectKind::Drop { destructor } => {
                    MirEffectKind::Drop { destructor: *destructor }
                }
                EvidenceEffectKind::Assert(code) => MirEffectKind::Assert(assert_class(*code)?),
                EvidenceEffectKind::Asm { empty_noreturn } => {
                    MirEffectKind::Asm { empty_noreturn: *empty_noreturn }
                }
                EvidenceEffectKind::Yield => MirEffectKind::Yield,
            };
            Ok(MirEffect { kind, span: *span })
        })
        .collect::<Result<Vec<_>>>()?;
    let store_values = e
        .store_values
        .iter()
        .map(|(r, v)| Ok((root(*r, e.arg_count)?, store_value(*v)?)))
        .collect::<Result<Vec<_>>>()?;
    let mut exact_store_args = BTreeMap::new();
    for &(effect, argument) in &e.exact_store_args {
        let effect = usize::try_from(effect)
            .map_err(|_| refuse("retained exact store ordinal is too large"))?;
        if argument >= e.arg_count
            || !matches!(
                effects.get(effect).map(|e| &e.kind),
                Some(MirEffectKind::Store(MemRoot::Indirect))
            )
            || exact_store_args.insert(effect, argument).is_some()
        {
            return Err(refuse("retained exact store is not bound to one indirect-store effect"));
        }
    }
    // Every real source census records one value fact for every escaping
    // store. Enforce the complete association even without exact-store facts:
    // deleting/rebinding a coarse value fact must not erase an enum-value
    // abstraction. The source matcher's legacy diagnostic inputs stay intact.
    let roots: Vec<_> = effects
        .iter()
        .filter_map(|e| match e.kind {
            MirEffectKind::Store(r) => Some(r),
            _ => None,
        })
        .collect();
    if roots.len() != store_values.len()
        || !roots.iter().zip(&store_values).all(|(r, (v, _))| r == v)
    {
        return Err(refuse("retained store values do not match the complete store-effect order"));
    }
    if let Some(oracle) = &e.drop_oracle {
        for d in oracle {
            drop_identity(d.identity, e.arg_count)?;
            if d.style.is_some_and(|s| s > 2) {
                return Err(refuse("retained drop oracle has an unknown style"));
            }
        }
    }
    if let Some((keys, _, destructor)) = &e.drop_claim {
        if destructor.len() != keys.len() {
            return Err(refuse("retained drop destructor facts have the wrong population"));
        }
        for key in keys {
            drop_identity(key.identity, e.arg_count)?;
            if key.style > 2 {
                return Err(refuse("retained drop claim has an unknown style"));
            }
        }
    }
    Ok(MirCensus {
        effects,
        arg_count: e.arg_count,
        arg_enum: e.arg_enum.clone(),
        ret_enum: e.ret_enum,
        store_values,
        exact_store_args,
        enum_types: unique(&e.enum_types, "enum type set")?,
        drop_oracle: e
            .drop_oracle
            .as_ref()
            .map(|rows| rows.iter().map(|r| (r.clone(), r.destructor)).collect()),
        drop_dead_blocks: unique(&e.drop_dead_blocks, "dead-drop block set")?,
    })
}

fn drop_tags(mir: &Census, ir: &IrCensus<StableDef, String>, e: &Evidence) -> Result<Vec<Tag>> {
    let mut tags = Vec::new();
    let Some(oracle) = &mir.drop_oracle else {
        if e.drop_claim.is_some() || ir.shape.drops > 0 {
            tags.push(Tag {
                kind: TagKind::NotConserved(Effect::Census),
                site: "the retained body carries drops without its drop oracle".into(),
            });
        }
        return Ok(tags);
    };
    for (d, _) in oracle {
        if d.style.is_some() && mir.drop_dead_blocks.contains(&d.block) {
            tags.push(Tag {
                kind: TagKind::NotConserved(Effect::Census),
                site: format!(
                    "retained drop oracle and census disagree at span ordinal {}",
                    d.span
                ),
            });
        }
    }
    let live: Vec<_> = oracle
        .iter()
        .filter_map(|(d, destructor)| {
            d.style.map(|style| {
                (
                    EvidenceDropKey { identity: d.identity, ty: d.ty, span: d.span, style },
                    *destructor,
                )
            })
        })
        .collect();
    let keys: Vec<_> = live.iter().map(|(k, _)| k.clone()).collect();
    let claim = e
        .drop_claim
        .as_ref()
        .map(|(live, emitted, _)| {
            Ok((
                live.as_slice(),
                usize::try_from(*emitted)
                    .map_err(|_| refuse("retained emitted-drop count is too large"))?,
            ))
        })
        .transpose()?;
    let compared = super::compare_drops(&keys, claim, ir.shape.drops);
    for &i in &compared.missing {
        tags.push(Tag {
            kind: TagKind::Abstracted(Lane::Drop),
            site: format!("missing retained drop at span ordinal {}", live[i].0.span),
        });
    }
    if let Some(&i) = compared.missing.iter().find(|&&i| live[i].1) {
        tags.push(Tag {
            kind: TagKind::Abstracted(Lane::Destructor),
            site: format!("missing destructor drop at span ordinal {}", live[i].0.span),
        });
    }
    for &i in &compared.extra {
        tags.push(Tag {
            kind: TagKind::NotConserved(Effect::Drop),
            site: format!("extra retained drop claim row {i}"),
        });
    }
    if e.drop_claim.is_none() && ir.shape.drops > 0 {
        tags.push(Tag {
            kind: TagKind::NotConserved(Effect::Drop),
            site: "the retained body carries drops its producer never claimed".into(),
        });
    }
    if let Some((recorded, carried)) = compared.ledger {
        if e.drop_claim.is_some() {
            tags.push(Tag {
                kind: TagKind::NotConserved(Effect::Drop),
                site: format!(
                    "retained producer recorded {recorded} drops but decoded body carries {carried}"
                ),
            });
        }
    }
    Ok(tags)
}

/// Recompute the complete effect/value-abstraction judgement of a decoded
/// per-definition R module. Identity/symbol/ABI admission belongs to its caller.
pub fn judge(module: &Module, evidence: &Evidence) -> Result<RetainedJudgement> {
    let errors = trust_ir_build::validate::validate_module(module);
    if !errors.is_empty() {
        return Err(refuse(format!("decoded entry module is invalid: {errors:?}")));
    }
    let body = module
        .functions
        .first()
        .filter(|f| {
            f.id == FuncId::new(0) && !f.is_declaration() && f.producer == Some(Producer::TRust)
        })
        .ok_or_else(|| refuse("decoded entry has no Rust body at FuncId0"))?;
    if module.functions.iter().skip(1).any(|f| !f.is_declaration()) {
        return Err(refuse("decoded per-definition entry contains another body"));
    }
    let mut ledger = BTreeMap::new();
    for row in &evidence.ledger {
        let first = row
            .ids
            .first()
            .copied()
            .ok_or_else(|| refuse("retained callee ledger row has no identity"))?;
        let id = FuncId::new(row.func_id);
        if !module.function_by_id(id).is_some_and(|f| f.is_declaration())
            || ledger
                .insert(
                    id,
                    LedgerRow { ids: row.ids.clone(), site: row.site.clone().map(|s| (first, s)) },
                )
                .is_some()
        {
            return Err(refuse("retained callee ledger has an extra or duplicate declaration row"));
        }
    }
    if module.functions.iter().skip(1).any(|f| !ledger.contains_key(&f.id)) {
        return Err(refuse("decoded declaration has no retained callee identity"));
    }
    judge_bound(module, body, evidence, &ledger)
}

/// The same protected consistency algorithms for one known Rust body in a
/// closed, unlicensed S graph. This is not the R reader: its exact FuncId0 and
/// declaration-only checks above remain unchanged. Identity/remaps are derived
/// from the typed source/header/actual-instance transport before this call.
pub(crate) fn judge_source(module: &Module, body_id: FuncId, evidence: &Evidence)
    -> Result<RetainedJudgement>
{
    let errors = trust_ir_build::validate::validate_module(module);
    if !errors.is_empty() { return Err(refuse(format!("source graph invalid: {errors:?}"))); }
    let body = module.function_by_id(body_id)
        .filter(|f| !f.is_declaration() && f.producer == Some(Producer::TRust)
            && f.body_gate == Some(trust_ir::BodyGate::Ungated))
        .ok_or_else(|| refuse("source graph has no unlicensed Rust body at the bound id"))?;
    let mut ledger = BTreeMap::new();
    for row in &evidence.ledger {
        let first = row.ids.first().copied().ok_or_else(|| refuse("source ledger has no identity"))?;
        let id = FuncId::new(row.func_id);
        if id == body_id || module.function_by_id(id).is_none()
            || row.site.is_none()
            || ledger.insert(id, LedgerRow { ids: row.ids.clone(), site: row.site.clone().map(|s| (first,s)) }).is_some()
        { return Err(refuse("source ledger has an absent/self/duplicate/unbound callee")); }
    }
    let signature = module.func_types.get(body.ty.as_usize())
        .ok_or_else(|| refuse("source graph body signature is absent"))?;
    if evidence.arg_count as usize != signature.params.len() {
        return Err(refuse("source graph argument facts differ from its bound body"));
    }
    judge_bound(module, body, evidence, &ledger)
}

fn judge_bound(module: &Module, body: &trust_ir::Function, evidence: &Evidence,
    ledger: &BTreeMap<FuncId, LedgerRow<StableDef, String>>) -> Result<RetainedJudgement>
{
    let mir = census(evidence)?;
    let collapsed = unique(&evidence.collapsed_enum_types, "collapsed enum set")?;
    if !collapsed.is_subset(&mir.enum_types) {
        return Err(refuse("retained collapsed enums are not part of the source enum population"));
    }
    let degraded = unique(&evidence.degraded_structs, "degraded struct set")?;
    if degraded.iter().any(|&i| i as usize >= module.structs.len()) {
        return Err(refuse("retained degraded struct is absent from the decoded module"));
    }
    let ir = super::ir_census_with_identities(
        module,
        body,
        ledger,
        &BTreeMap::new(),
        &degraded.iter().map(|i| StructId::new(*i)).collect(),
        LedgeredLanes {
            union_lane: evidence.union_lane,
            enum_param_lane: evidence.enum_param_lane,
        },
    );
    let mut tags = drop_tags(&mir, &ir, evidence)?;
    let filtered;
    let pairing = if mir.drop_oracle.is_some() {
        filtered = super::without_drop_effects(&mir);
        &filtered
    } else {
        &mir
    };
    for unpaired in super::unpaired_effects(pairing, &ir) {
        tags.push(Tag {
            kind: unpaired.kind,
            site: format!(
                "retained source effect {} at span ordinal {}",
                unpaired.mir_index, pairing.effects[unpaired.mir_index].span
            ),
        });
    }
    let abstractions = super::judgement_abstractions(pairing, &ir, &collapsed);
    for kind in super::abstraction_kinds(&abstractions) {
        tags.push(Tag { kind, site: "decoded body carries a retained value abstraction".into() });
    }
    Ok(RetainedJudgement {
        tags,
        equivalences: super::unpaired_equivalences(pairing, &ir),
        shape: ir.shape,
    })
}

#[cfg(test)]
mod tests;
