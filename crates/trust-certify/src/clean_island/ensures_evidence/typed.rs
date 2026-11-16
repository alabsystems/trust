// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Exact-domain E9 transport. The bytes describe a checked Lean judgment;
//! they do not deserialize admission authority or identify a Rust body.
//! Scalar v1 and its explicit proof-lift mode remain byte-compatible.

use std::collections::{BTreeMap, BTreeSet};

use trust_spec_elab::{Domain, MachineSIntWidth, MachineUIntWidth, TargetPointerWidth};

use super::*;

pub(super) const CONTEXT_MAGIC: &[u8] = b"trust-certify.e9-ensures-discharge.context.v2\0";
const ENVIRONMENT_DOMAIN: &[u8] = b"trust-certify.e9-ensures-discharge.environment.v2";
const MAX_CONTEXT_BYTES: usize = 8 * 1024 * 1024;

/// An untrusted description, never a deserialized `RegisteredAdt` handle.
#[derive(Debug, Clone, PartialEq, Eq)]
struct TypedRecord {
    judgment: ContextRecord,
    params: Vec<(String, Vec<u8>)>,
    /// Canonical type bytes -> complete validated metadata snapshot bytes.
    /// Strictly sorted and unique, including carriers reached only by calls.
    carriers: Vec<(Vec<u8>, Vec<u8>)>,
}

/// Mint an exact-domain E9 certificate in strict clause mode. All registered
/// parameter and facet carriers are revalidated in `env`. `result` denotes the
/// admitted self-call, not a freely quantified value. This proves the resulting
/// Lean goal only; the caller must separately establish Rust correspondence.
///
/// This API intentionally accepts no `ProofClauseInputs`: it cannot silently
/// downgrade a supplied lift mode. Mode-aware scalar callers keep v1; typed
/// lift support requires additional implementation and currently fails closed.
#[must_use]
pub fn certify_ensures_discharge_with_domains(
    env: &Environment,
    clauses: &[EnsuresDischargeClause<'_>],
    params: &[(&str, Domain)],
    self_fn_name: &str,
) -> Option<EnsuresDischargeCertificate> {
    preflight(clauses, params, self_fn_name)?;
    let carriers = collect_carriers(env, clauses, params)?;
    let judgment = rebuild_judgment_from(
        env,
        clauses,
        |clause| {
            trust_spec_elab::elaborate_ensures_with_domains(
                env,
                clause.clause_src,
                params,
                self_fn_name,
                clause.facets,
            )
            .ok()
        },
        environment_digest,
    )?;
    let term = serialize_term(&judgment.proof).ok()?;
    if term.is_empty() || term.len() > MAX_TERM_BYTES {
        return None;
    }
    let record = TypedRecord {
        judgment: ContextRecord {
            self_fn_name: self_fn_name.to_owned(),
            params: Vec::new(), // v2 domains below, never lossy string aliases
            clauses: clauses
                .iter()
                .map(|clause| {
                    let (tag, referent) = route_fields(clause.route);
                    (tag, referent.to_owned(), clause.clause_src.to_owned())
                })
                .collect(),
            goal: serialize_term(&judgment.goal).ok()?,
            environment_digest: judgment.environment_digest,
            dependency_count: judgment.dependency_count,
        },
        params: params
            .iter()
            .map(|(name, domain)| Some(((*name).to_owned(), encode_domain(domain)?)))
            .collect::<Option<_>>()?,
        carriers,
    };
    let context = encode(&record)?;
    if decode(&context).as_ref() != Some(&record)
        || deserialize_term(&term).ok().as_ref() != Some(&judgment.proof)
        || deserialize_term(&record.judgment.goal).ok().as_ref() != Some(&judgment.goal)
        || !audit_presented(env, &term, &context)
    {
        return None;
    }
    // KR0 switch: the same closed judgment, through the reference entry.
    let reference =
        crate::reference_mint::check_closed_in(env, &judgment.goal, &judgment.proof).ok();
    Some(EnsuresDischargeCertificate { term, context, reference })
}

/// Regenerate from the consumer's own exact domains and clauses, independently
/// audit the presented bytes, then bind the exact obligation row. A matching
/// printed type name, valid proof of another goal, or another row is insufficient.
#[must_use]
pub fn recheck_ensures_discharge_with_domains(
    env: &Environment,
    clauses: &[EnsuresDischargeClause<'_>],
    params: &[(&str, Domain)],
    self_fn_name: &str,
    vc: &VerificationCondition,
    evidence: &trust_ir::ProofEvidence,
) -> bool {
    let trust_ir::ProofEvidence::CleanCic { term, context, lineage, kernel_recheck: None } =
        evidence
    else {
        return false;
    };
    let Some(canonical) =
        certify_ensures_discharge_with_domains(env, clauses, params, self_fn_name)
    else {
        return false;
    };
    canonical.term == *term
        && canonical.context == *context
        && audit_presented(env, term, context)
        && row_lineage(term, context, vc).as_ref() == Some(lineage)
}

pub(super) fn audit_presented(env: &Environment, term: &[u8], context: &[u8]) -> bool {
    if term.is_empty() || term.len() > MAX_TERM_BYTES {
        return false;
    }
    let Some(record) = decode(context) else {
        return false;
    };
    // Passive type expressions are rebuilt against THIS environment. A snapshot
    // blob never becomes a handle, and missing/changed metadata cannot pass.
    let mut carriers = BTreeSet::new();
    for (ty, binding) in &record.carriers {
        let Ok(expr) = deserialize_term(ty) else {
            return false;
        };
        let Some(current) = super::super::registered_carrier_of_clean_type(env, &expr) else {
            return false;
        };
        if current.canonical_binding(env).ok().as_ref() != Some(binding) {
            return false;
        }
        carriers.insert(ty.as_slice());
    }
    for (_, domain) in &record.params {
        let Some(domain) = decode_domain(env, domain) else {
            return false;
        };
        if let Domain::RegisteredAdt(registered) = domain {
            let Ok(ty) = serialize_term(&registered.ty()) else {
                return false;
            };
            if !carriers.contains(ty.as_slice()) {
                return false;
            }
        }
    }
    let (Ok(goal), Ok(proof)) = (deserialize_term(&record.judgment.goal), deserialize_term(term))
    else {
        return false;
    };
    let audit = env.audit_certification(&goal, &proof);
    if !audit.is_certified() {
        return false;
    }
    let referents: Vec<&str> =
        record.judgment.clauses.iter().map(|(_, name, _)| name.as_str()).collect();
    u64::try_from(audit.dependencies.len()).ok() == Some(record.judgment.dependency_count)
        && environment_digest(env, &referents, &audit.dependencies)
            == Some(record.judgment.environment_digest)
}

fn environment_digest(
    env: &Environment,
    referents: &[&str],
    dependencies: &[Name],
) -> Option<[u8; 32]> {
    if referents.len() > MAX_CONTEXT_ENTRIES as usize
        || dependencies.len() > MAX_CONTEXT_ENTRIES as usize
    {
        return None;
    }
    let mut hash = Sha256::new();
    update_field(&mut hash, ENVIRONMENT_DOMAIN);
    let referents: Vec<Name> = referents.iter().map(|name| Name::from_string(name)).collect();
    // Preserve the ordered referent/dependency partition as well as the complete
    // semantic closure, including constructor/rule dependencies not used by an
    // identity proof. Names use structural term serialization, never Display.
    for names in [referents.as_slice(), dependencies] {
        hash.update((names.len() as u64).to_le_bytes());
        for name in names {
            update_field(&mut hash, &serialize_term(&Expr::const_(name.clone(), vec![])).ok()?);
        }
    }
    let roots: Vec<Name> = referents.into_iter().chain(dependencies.iter().cloned()).collect();
    update_field(&mut hash, &trust_spec_elab::canonical_environment_binding(env, &roots).ok()?);
    Some(hash.finalize().into())
}

fn preflight(
    clauses: &[EnsuresDischargeClause<'_>],
    params: &[(&str, Domain)],
    name: &str,
) -> Option<()> {
    if name.is_empty()
        || clauses.is_empty()
        || clauses.len() > MAX_CONTEXT_ENTRIES as usize
        || params.len() > MAX_CONTEXT_ENTRIES as usize
    {
        return None;
    }
    let mut bytes = name.len();
    let mut names = BTreeSet::new();
    for (param, _) in params {
        if param.is_empty() || !names.insert(*param) {
            return None;
        }
        bytes = bytes.checked_add(param.len())?;
    }
    for clause in clauses {
        bytes = bytes
            .checked_add(clause.clause_src.len())?
            .checked_add(route_fields(clause.route).1.len())?;
    }
    (!trust_types::audit_ledger::cap_hit_if(
        bytes > MAX_CONTEXT_BYTES,
        "crates/trust-certify/src/clean_island/ensures_evidence/typed.rs:MAX_CONTEXT_BYTES",
    ))
    .then_some(())
}

fn collect_carriers(
    env: &Environment,
    clauses: &[EnsuresDischargeClause<'_>],
    params: &[(&str, Domain)],
) -> Option<Vec<(Vec<u8>, Vec<u8>)>> {
    let mut map = BTreeMap::new();
    let mut total = 0usize;
    let mut add = |carrier: &trust_spec_elab::RegisteredAdt| -> Option<()> {
        let ty = serialize_term(&carrier.ty()).ok()?;
        let binding = carrier.canonical_binding(env).ok()?;
        if let Some(old) = map.get(&ty) {
            return (*old == binding).then_some(());
        }
        total = total.checked_add(ty.len())?.checked_add(binding.len())?;
        if trust_types::audit_ledger::cap_hit_if(
            total > MAX_CONTEXT_BYTES,
            "crates/trust-certify/src/clean_island/ensures_evidence/typed.rs:MAX_CONTEXT_BYTES",
        ) || map.len() >= MAX_CONTEXT_ENTRIES as usize
        {
            return None;
        }
        map.insert(ty, binding);
        Some(())
    };
    for (_, domain) in params {
        if let Domain::RegisteredAdt(carrier) = domain {
            add(carrier)?;
        }
    }
    for clause in clauses {
        for carrier in clause.facets.registered_carriers() {
            add(carrier)?;
        }
    }
    Some(map.into_iter().collect())
}

fn signed_bits(width: MachineSIntWidth) -> u8 {
    match width {
        MachineSIntWidth::I8 => 8,
        MachineSIntWidth::I16 => 16,
        MachineSIntWidth::I32 => 32,
        MachineSIntWidth::I64 => 64,
        MachineSIntWidth::I128 => 128,
    }
}
fn signed_width(bits: u8) -> Option<MachineSIntWidth> {
    Some(match bits {
        8 => MachineSIntWidth::I8,
        16 => MachineSIntWidth::I16,
        32 => MachineSIntWidth::I32,
        64 => MachineSIntWidth::I64,
        128 => MachineSIntWidth::I128,
        _ => return None,
    })
}

fn encode_domain(domain: &Domain) -> Option<Vec<u8>> {
    Some(match domain {
        Domain::Nat => vec![0],
        Domain::Int => vec![1],
        Domain::Bool => vec![2],
        Domain::Machine(width) => vec![
            3,
            match width {
                MachineUIntWidth::U8 => 8,
                MachineUIntWidth::U16 => 16,
                MachineUIntWidth::U32 => 32,
                MachineUIntWidth::U64 => 64,
            },
        ],
        Domain::Signed(width) => vec![4, signed_bits(*width)],
        Domain::U128 => vec![5],
        Domain::USize(width) => vec![6, width.bits() as u8],
        Domain::ISize(width) => vec![7, width.bits() as u8],
        Domain::OptionSigned(width) => vec![8, signed_bits(*width)],
        Domain::RegisteredAdt(registered) => {
            let mut out = vec![9];
            field(&mut out, &serialize_term(&registered.ty()).ok()?)?;
            out
        }
    })
}

fn decode_domain(env: &Environment, bytes: &[u8]) -> Option<Domain> {
    let mut reader = Reader { bytes };
    let domain = match reader.take(1)?[0] {
        0 => Domain::Nat,
        1 => Domain::Int,
        2 => Domain::Bool,
        3 => Domain::Machine(match reader.take(1)?[0] {
            8 => MachineUIntWidth::U8,
            16 => MachineUIntWidth::U16,
            32 => MachineUIntWidth::U32,
            64 => MachineUIntWidth::U64,
            _ => return None,
        }),
        4 => Domain::Signed(signed_width(reader.take(1)?[0])?),
        5 => Domain::U128,
        6 => Domain::USize(TargetPointerWidth::from_bits(u32::from(reader.take(1)?[0])).ok()?),
        7 => Domain::ISize(TargetPointerWidth::from_bits(u32::from(reader.take(1)?[0])).ok()?),
        8 => Domain::OptionSigned(signed_width(reader.take(1)?[0])?),
        9 => {
            let ty = deserialize_term(reader.field()?).ok()?;
            Domain::RegisteredAdt(super::super::registered_carrier_of_clean_type(env, &ty)?)
        }
        _ => return None,
    };
    (reader.bytes.is_empty() && encode_domain(&domain)?.as_slice() == bytes).then_some(domain)
}

fn append(out: &mut Vec<u8>, bytes: &[u8]) -> Option<()> {
    if trust_types::audit_ledger::cap_hit_if(
        out.len().checked_add(bytes.len())? > MAX_CONTEXT_BYTES,
        "crates/trust-certify/src/clean_island/ensures_evidence/typed.rs:MAX_CONTEXT_BYTES",
    ) {
        return None;
    }
    out.extend_from_slice(bytes);
    Some(())
}
fn field(out: &mut Vec<u8>, bytes: &[u8]) -> Option<()> {
    if bytes.len() > MAX_CONTEXT_FIELD_BYTES {
        return None;
    }
    append(out, &(bytes.len() as u64).to_le_bytes())?;
    append(out, bytes)
}
fn count(out: &mut Vec<u8>, n: usize) -> Option<()> {
    if n > MAX_CONTEXT_ENTRIES as usize {
        return None;
    }
    append(out, &(n as u64).to_le_bytes())
}

fn encode(record: &TypedRecord) -> Option<Vec<u8>> {
    let mut out = CONTEXT_MAGIC.to_vec();
    field(&mut out, &encode_context(&record.judgment))?;
    count(&mut out, record.params.len())?;
    for (name, domain) in &record.params {
        field(&mut out, name.as_bytes())?;
        field(&mut out, domain)?;
    }
    count(&mut out, record.carriers.len())?;
    for (ty, binding) in &record.carriers {
        field(&mut out, ty)?;
        field(&mut out, binding)?;
    }
    Some(out)
}

fn decode(bytes: &[u8]) -> Option<TypedRecord> {
    if trust_types::audit_ledger::cap_hit_if(
        bytes.len() > MAX_CONTEXT_BYTES,
        "crates/trust-certify/src/clean_island/ensures_evidence/typed.rs:MAX_CONTEXT_BYTES",
    ) {
        return None;
    }
    let mut reader = Reader { bytes: bytes.strip_prefix(CONTEXT_MAGIC)? };
    let judgment = decode_context(reader.field()?)?;
    if !judgment.params.is_empty() {
        return None;
    }
    let mut params = Vec::new();
    let mut names = BTreeSet::new();
    for _ in 0..reader.count()? {
        let name = reader.string()?;
        if name.is_empty() || !names.insert(name.clone()) {
            return None;
        }
        let domain = reader.field()?.to_vec();
        if domain.is_empty() {
            return None;
        }
        params.push((name, domain));
    }
    let mut carriers: Vec<(Vec<u8>, Vec<u8>)> = Vec::new();
    for _ in 0..reader.count()? {
        let ty = reader.field()?.to_vec();
        let binding = reader.field()?.to_vec();
        if ty.is_empty()
            || binding.is_empty()
            || carriers.last().is_some_and(|(last, _)| *last >= ty)
        {
            return None;
        }
        carriers.push((ty, binding));
    }
    if !reader.bytes.is_empty() {
        return None;
    }
    let record = TypedRecord { judgment, params, carriers };
    (encode(&record)?.as_slice() == bytes).then_some(record)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn domain_tags_preserve_signedness_and_pointer_identity() {
        let env = Environment::new();
        let domains = [
            Domain::Nat,
            Domain::Int,
            Domain::Bool,
            Domain::U128,
            Domain::Machine(MachineUIntWidth::U64),
            Domain::Signed(MachineSIntWidth::I64),
            Domain::USize(TargetPointerWidth::W64),
            Domain::ISize(TargetPointerWidth::W64),
            Domain::OptionSigned(MachineSIntWidth::I64),
        ];
        let mut encodings = BTreeSet::new();
        for domain in domains {
            let bytes = encode_domain(&domain).expect("domain");
            assert_eq!(decode_domain(&env, &bytes), Some(domain));
            assert!(encodings.insert(bytes.clone()));
            let mut trailing = bytes;
            trailing.push(0);
            assert!(decode_domain(&env, &trailing).is_none());
        }
        for invalid in [&[255][..], &[3, 128], &[4, 0], &[6, 8], &[9]] {
            assert!(decode_domain(&env, invalid).is_none());
        }
    }

    #[test]
    fn whole_context_budget_and_checked_lengths_fail_closed() {
        assert!(decode(&vec![0; MAX_CONTEXT_BYTES + 1]).is_none());
        let mut out = vec![0; MAX_CONTEXT_BYTES];
        assert!(append(&mut out, &[1]).is_none());
        let mut bad = CONTEXT_MAGIC.to_vec();
        bad.extend_from_slice(&u64::MAX.to_le_bytes());
        assert!(decode(&bad).is_none());
    }

    #[test]
    fn passive_context_codec_refuses_ambiguous_tables_and_nested_v1_bindings() {
        // A codec record, deliberately not offered as a kernel certificate.
        let original = TypedRecord {
            judgment: ContextRecord {
                self_fn_name: "self".into(),
                params: vec![],
                clauses: vec![(ROUTE_TAG_ISLAND_DEFEQ, "self".into(), "result == result".into())],
                goal: serialize_term(&Expr::prop()).unwrap(),
                environment_digest: [0; 32],
                dependency_count: 0,
            },
            params: vec![("x".into(), vec![0])],
            carriers: vec![(vec![1], vec![2]), (vec![3], vec![4])],
        };
        let bytes = encode(&original).unwrap();
        assert_eq!(decode(&bytes), Some(original.clone()));
        let mut duplicate = original.clone();
        duplicate.params.push(duplicate.params[0].clone());
        let mut empty_name = original.clone();
        empty_name.params[0].0.clear();
        let mut empty_domain = original.clone();
        empty_domain.params[0].1.clear();
        let mut repeated_carrier = original.clone();
        repeated_carrier.carriers[1] = repeated_carrier.carriers[0].clone();
        let mut reversed = original.clone();
        reversed.carriers.reverse();
        let mut empty_binding = original.clone();
        empty_binding.carriers[0].1.clear();
        let mut nested_bindings = original.clone();
        nested_bindings.judgment.params.push(("x".into(), "u64".into()));
        for malformed in [
            duplicate,
            empty_name,
            empty_domain,
            repeated_carrier,
            reversed,
            empty_binding,
            nested_bindings,
        ] {
            assert!(decode(&encode(&malformed).unwrap()).is_none());
        }
        let mut trailing = bytes;
        trailing.push(0);
        assert!(decode(&trailing).is_none());
        let mut too_many = original;
        too_many.params.resize(MAX_CONTEXT_ENTRIES as usize + 1, ("x".into(), vec![0]));
        assert!(encode(&too_many).is_none());
    }
}
