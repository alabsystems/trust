//! Complete local proof closure relative to an explicitly reconstructed basis.
//!
//! Wire v1 is length-framed, not a serialized Environment: magic, version,
//! fixed-model source SHA-256, sorted reconstructed-basis manifest, then the
//! exact 262 ordered local declarations. Each declaration carries kind, name,
//! canonical type bytes, and canonical Clean proof-term bytes. Integers are
//! little-endian u32; hashes are 64 lowercase ASCII hex bytes. Nothing trails
//! the last declaration. No wire name, type, digest, or kind grants authority.
//!
//! The basis manifest binds actual ConstantInfo plus inductive/constructor/
//! recursor metadata, including recursor reduction rules. Basis declarations
//! are NOT imported from the wire: the fixed scalar model and Clean foundation
//! must be reconstructed by this checker, and their exact transitive manifest
//! must agree. Thus all family-local proof dependencies are carried, but this
//! is deliberately NOT a self-contained foundation or kernel distribution.
//! Native reducer code and the replay executable remain explicit external TCB;
//! these payload hashes do not attest either executable implementation.

use std::collections::{BTreeSet, HashSet, VecDeque};

use clean_kernel::{ConstantKind, ExprKind};
use trust_types::digest::{canonical_json_sha256, stable_sha256_hex};

use super::*;

const MAGIC: &[u8] = b"TrustScalarReturnFamily\0";
const VERSION: u32 = 1;
const LOCAL_COUNT: usize = 4 + 257 + 1;
const MAX_TERM_BYTES: usize = 512 * 1024;
const MAX_NAME_BYTES: usize = 512;
const MAX_BASIS_DECLS: usize = 4096;

/// Maximum accepted bundle size, checked before copying or decoding input.
pub const MAX_SCALAR_FAMILY_BUNDLE_BYTES: usize = 8 * 1024 * 1024;

/// Construct all proof terms and serialize the complete local family closure.
///
/// The result is untrusted transport data. Call [`replay_u8_widen_add_one_family`]
/// to independently recheck it against the fixed model, canonical full-observation
/// goal and freshly reconstructed Clean basis. This grants no Rust/MIR, caller,
/// codegen, or compiler proof authority.
pub fn prove_u8_widen_add_one_family() -> Result<Vec<u8>, String> {
    crate::checker_core::run_on_large_stack(prove)
        .ok_or_else(|| "scalar family bundle construction worker failed".to_string())?
}

/// Independently check an external bundle in a fresh fixed-model environment.
///
/// All 262 local definitions/proofs must occur in the canonical order. Every
/// type is reconstructed, all four definition values are fixed, and every
/// decoded proof is checked with both axiom audits. No ambient caller-supplied
/// environment or claim is accepted. Input/count/term bounds and the inner
/// Clean codec's allocation/structure/canonicality bounds fail closed.
///
/// Success is only this scalar-model theorem relative to the reconstructed
/// basis. It is neither a self-contained foundation attestation nor compiler
/// authority. A source/MIR refinement and caller-composition proof are absent.
pub fn replay_u8_widen_add_one_family(bytes: &[u8]) -> Result<(), String> {
    if trust_types::audit_ledger::cap_hit_if(
        bytes.len() > MAX_SCALAR_FAMILY_BUNDLE_BYTES,
        "crates/trust-certify/src/scalar_return_family/bundle.rs:MAX_SCALAR_FAMILY_BUNDLE_BYTES",
    ) {
        return Err("scalar family bundle exceeds byte limit".to_string());
    }
    let bytes = bytes.to_vec();
    crate::checker_core::run_on_large_stack(move || replay(&bytes))
        .ok_or_else(|| "scalar family bundle replay worker failed".to_string())?
}

struct CanonicalDecl {
    name: String,
    ty: Expr,
    value: Expr,
    theorem: bool,
}

fn canonical_declarations() -> Vec<CanonicalDecl> {
    let mut declarations: Vec<_> = fixed_definitions(Construction::default())
        .into_iter()
        .map(|(name, ty, value)| CanonicalDecl {
            name: name.to_string(),
            ty,
            value,
            theorem: false,
        })
        .collect();
    declarations.extend((0..=256).rev().map(|offset| CanonicalDecl {
        name: clause_name(offset),
        ty: clause_goal(offset),
        value: clause_proof(offset),
        theorem: true,
    }));
    declarations.push(CanonicalDecl {
        name: THEOREM.to_string(),
        ty: universal_goal(),
        value: universal_proof(),
        theorem: true,
    });
    declarations
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Record {
    name: String,
    theorem: bool,
    ty: Vec<u8>,
    value: Vec<u8>,
}

#[derive(Clone, Debug)]
struct Bundle {
    model_sha256: String,
    basis: Vec<(String, String)>,
    records: Vec<Record>,
}

fn model_digest() -> String {
    stable_sha256_hex(crate::scalar_return::SCALAR_MODEL_SOURCE.as_bytes())
}

fn prove() -> Result<Vec<u8>, String> {
    let model = ScalarExecutionModel::new()?;
    let mut env = model.environment().clone();
    let declarations = canonical_declarations();
    let mut records = Vec::with_capacity(LOCAL_COUNT);
    for declaration in &declarations {
        let value = register(
            &mut env,
            &declaration.name,
            declaration.ty.clone(),
            declaration.value.clone(),
            declaration.theorem,
        )?;
        records.push(Record {
            name: declaration.name.clone(),
            theorem: declaration.theorem,
            ty: serialize_term(&declaration.ty)
                .map_err(|e| format!("type serialization: {e:?}"))?,
            value,
        });
    }
    let basis = basis_manifest(&env, &declarations)?;
    encode(&Bundle { model_sha256: model_digest(), basis, records })
}

fn replay(bytes: &[u8]) -> Result<(), String> {
    let bundle = decode(bytes)?;
    if bundle.model_sha256 != model_digest() {
        return Err("fixed scalar model source binding mismatch".to_string());
    }
    let declarations = canonical_declarations();
    // Validate the complete roster and canonical goals before building the
    // kernel environment. Definition equality is indispensable: merely checking
    // their types would let a claimant change BOTH the program and its expected
    // result, and then prove a different but true equation under the same names.
    for (record, expected) in bundle.records.iter().zip(&declarations) {
        if record.name != expected.name || record.theorem != expected.theorem {
            return Err(format!("canonical declaration roster mismatch at {}", expected.name));
        }
        let ty =
            serialize_term(&expected.ty).map_err(|e| format!("canonical goal encoding: {e:?}"))?;
        if record.ty != ty {
            return Err(format!("canonical goal mismatch for {}", expected.name));
        }
        if !expected.theorem {
            let value = serialize_term(&expected.value)
                .map_err(|e| format!("fixed definition encoding: {e:?}"))?;
            if record.value != value {
                return Err(format!("fixed definition mismatch for {}", expected.name));
            }
        }
    }
    let model = ScalarExecutionModel::new()?;
    let mut env = model.environment().clone();
    let expected_basis = basis_manifest(&env, &declarations)?;
    if bundle.basis != expected_basis {
        return Err("reconstructed foundation/model dependency manifest mismatch".to_string());
    }
    for (record, expected) in bundle.records.iter().zip(&declarations) {
        decode_and_register(
            &mut env,
            &expected.name,
            expected.ty.clone(),
            &record.value,
            expected.theorem,
        )?;
    }
    // A replacement proof may typecheck but borrow extra ambient lemmas. Such
    // a proof needs its own complete basis; this fixed-family format accepts
    // only the explicitly reconstructed closure, never undeclared dependencies.
    let actual: Vec<_> = declarations
        .iter()
        .map(|expected| {
            let info = env
                .get_const(&Name::from_string(&expected.name))
                .ok_or_else(|| format!("replayed declaration missing: {}", expected.name))?;
            Ok(CanonicalDecl {
                name: expected.name.clone(),
                ty: info.type_.clone(),
                value: info.value.clone().ok_or("replayed declaration has no value")?,
                theorem: expected.theorem,
            })
        })
        .collect::<Result<_, String>>()?;
    if basis_manifest(&env, &actual)? != bundle.basis {
        return Err("replayed proof borrows an undeclared dependency closure".to_string());
    }
    Ok(())
}

// Include structure projection owners too: Expr::collect_constants only walks
// the projected expression, not the separately stored projection type name.
// Other kernel modes/extensions have no admitted role in this CIC-only bundle.
fn dependencies(expr: &Expr, names: &mut HashSet<Name>) -> Result<(), String> {
    let mut pending = vec![expr];
    while let Some(expr) = pending.pop() {
        match expr.kind() {
            ExprKind::Const(name, _) => {
                names.insert(name.clone());
            }
            ExprKind::App(f, a) => {
                pending.push(f);
                pending.push(a);
            }
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                pending.push(ty);
                pending.push(body);
            }
            ExprKind::Let(_, ty, value, body, _) => {
                pending.push(ty);
                pending.push(value);
                pending.push(body);
            }
            ExprKind::Proj(name, _, value) => {
                names.insert(name.clone());
                pending.push(value);
            }
            ExprKind::MData(_, value) => pending.push(value),
            ExprKind::BVar(_) | ExprKind::Sort(_) | ExprKind::Lit(_) => {}
            _ => return Err("non-closed-CIC dependency in scalar family closure".to_string()),
        }
    }
    Ok(())
}

fn basis_manifest(
    env: &Environment,
    locals: &[CanonicalDecl],
) -> Result<Vec<(String, String)>, String> {
    if env.has_constant_source() {
        return Err("scalar family basis cannot rely on a lazy constant source".to_string());
    }
    let local_names: BTreeSet<_> = locals.iter().map(|d| Name::from_string(&d.name)).collect();
    let mut roots = HashSet::new();
    for declaration in locals {
        dependencies(&declaration.ty, &mut roots)?;
        dependencies(&declaration.value, &mut roots)?;
    }
    let mut pending: VecDeque<_> = roots.into_iter().collect();
    let mut seen = BTreeSet::new();
    while let Some(name) = pending.pop_front() {
        if local_names.contains(&name) || !seen.insert(name.clone()) {
            continue;
        }
        if seen.len() > MAX_BASIS_DECLS {
            return Err("reconstructed scalar basis exceeds declaration limit".to_string());
        }
        let info = env.get_const(&name).ok_or_else(|| format!("missing dependency {name}"))?;
        if info.kind == ConstantKind::Axiom
            || env.is_unsafe(&name)
            || env.is_partial(&name)
            || !env.axiom_deps(&name).is_some_and(|a| a.is_empty())
            || !env.foundational_axiom_deps(&name).is_some_and(|a| a.is_empty())
        {
            return Err(format!("dependency {name} has unchecked/axiom debt"));
        }
        let mut found = HashSet::new();
        dependencies(&info.type_, &mut found)?;
        if let Some(value) = &info.value {
            dependencies(value, &mut found)?;
        }
        if let Some(inductive) = env.get_inductive(&name) {
            found.extend(inductive.all_names.iter().cloned());
            found.extend(inductive.constructor_names.iter().cloned());
        }
        if let Some(constructor) = env.get_constructor(&name) {
            found.insert(constructor.inductive_name.clone());
        }
        if let Some(recursor) = env.get_recursor(&name) {
            found.insert(recursor.inductive_name.clone());
            for rule in &recursor.rules {
                found.insert(rule.constructor_name.clone());
                dependencies(&rule.rhs, &mut found)?;
            }
        }
        if info.value.is_none()
            && env.get_inductive(&name).is_none()
            && env.get_constructor(&name).is_none()
            && env.get_recursor(&name).is_none()
        {
            return Err(format!("bodyless dependency {name} is outside the scalar basis"));
        }
        pending.extend(found);
    }
    seen.into_iter()
        .map(|name| {
            let info = env.get_const(&name).ok_or("basis declaration disappeared")?;
            let hash = canonical_json_sha256(&(
                info,
                env.get_inductive(&name),
                env.get_constructor(&name),
                env.get_recursor(&name),
                format!("{:?}", env.mode()),
            ))
            .map_err(|e| format!("basis payload {name}: {e}"))?;
            Ok((name.to_string(), hash))
        })
        .collect()
}

fn append_u32(bytes: &mut Vec<u8>, value: usize) -> Result<(), String> {
    bytes.extend_from_slice(&u32::try_from(value).map_err(|_| "length overflow")?.to_le_bytes());
    Ok(())
}

fn append_blob(bytes: &mut Vec<u8>, value: &[u8], limit: usize) -> Result<(), String> {
    if value.len() > limit {
        return Err("scalar bundle field exceeds limit".to_string());
    }
    append_u32(bytes, value.len())?;
    bytes.extend_from_slice(value);
    Ok(())
}

fn append_hash(bytes: &mut Vec<u8>, value: &str) -> Result<(), String> {
    if value.len() != 64 || !value.bytes().all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
    {
        return Err("noncanonical SHA-256 field".to_string());
    }
    bytes.extend_from_slice(value.as_bytes());
    Ok(())
}

fn encode(bundle: &Bundle) -> Result<Vec<u8>, String> {
    if bundle.records.len() != LOCAL_COUNT || bundle.basis.len() > MAX_BASIS_DECLS {
        return Err("scalar bundle declaration count mismatch".to_string());
    }
    let mut bytes = MAGIC.to_vec();
    bytes.extend_from_slice(&VERSION.to_le_bytes());
    append_hash(&mut bytes, &bundle.model_sha256)?;
    append_u32(&mut bytes, bundle.basis.len())?;
    for (name, hash) in &bundle.basis {
        append_blob(&mut bytes, name.as_bytes(), MAX_NAME_BYTES)?;
        append_hash(&mut bytes, hash)?;
    }
    append_u32(&mut bytes, bundle.records.len())?;
    for record in &bundle.records {
        bytes.push(u8::from(record.theorem));
        append_blob(&mut bytes, record.name.as_bytes(), MAX_NAME_BYTES)?;
        let _ = trust_types::audit_ledger::cap_hit_if(
            record.ty.len() > MAX_TERM_BYTES || record.value.len() > MAX_TERM_BYTES,
            "crates/trust-certify/src/scalar_return_family/bundle.rs:MAX_TERM_BYTES",
        );
        append_blob(&mut bytes, &record.ty, MAX_TERM_BYTES)?;
        append_blob(&mut bytes, &record.value, MAX_TERM_BYTES)?;
        if trust_types::audit_ledger::cap_hit_if(
            bytes.len() > MAX_SCALAR_FAMILY_BUNDLE_BYTES,
            "crates/trust-certify/src/scalar_return_family/bundle.rs:MAX_SCALAR_FAMILY_BUNDLE_BYTES",
        ) {
            return Err("scalar family bundle exceeds byte limit".to_string());
        }
    }
    Ok(bytes)
}

struct Reader<'a> {
    bytes: &'a [u8],
    offset: usize,
}
impl<'a> Reader<'a> {
    fn take(&mut self, length: usize) -> Result<&'a [u8], String> {
        let end = self.offset.checked_add(length).ok_or("bundle length overflow")?;
        let value = self.bytes.get(self.offset..end).ok_or("truncated scalar family bundle")?;
        self.offset = end;
        Ok(value)
    }
    fn count(&mut self, limit: usize) -> Result<usize, String> {
        let n = u32::from_le_bytes(self.take(4)?.try_into().map_err(|_| "bad length")?) as usize;
        if n > limit {
            return Err("scalar bundle count/length exceeds limit".to_string());
        }
        Ok(n)
    }
    fn blob(&mut self, limit: usize) -> Result<Vec<u8>, String> {
        let n = self.count(limit)?;
        Ok(self.take(n)?.to_vec())
    }
    /// [`Self::blob`] whose bound is the T3 L4 CAP site `cap`: a length over it is
    /// recorded as a hit (`trust_types::audit_ledger`; measurement only).
    fn blob_at(&mut self, limit: usize, cap: &'static str) -> Result<Vec<u8>, String> {
        let at = self.offset;
        let blob = self.blob(limit);
        if blob.is_err() {
            let declared = self
                .bytes
                .get(at..at.saturating_add(4))
                .and_then(|length| <[u8; 4]>::try_from(length).ok())
                .map(|length| u32::from_le_bytes(length) as usize);
            let _ = trust_types::audit_ledger::cap_hit_if(declared.is_some_and(|n| n > limit), cap);
        }
        blob
    }
    fn name(&mut self) -> Result<String, String> {
        String::from_utf8(self.blob(MAX_NAME_BYTES)?).map_err(|_| "invalid name UTF-8".to_string())
    }
    fn hash(&mut self) -> Result<String, String> {
        let hash = std::str::from_utf8(self.take(64)?).map_err(|_| "invalid hash ASCII")?;
        let mut checked = Vec::new();
        append_hash(&mut checked, hash)?;
        Ok(hash.to_string())
    }
}

fn decode(bytes: &[u8]) -> Result<Bundle, String> {
    if trust_types::audit_ledger::cap_hit_if(
        bytes.len() > MAX_SCALAR_FAMILY_BUNDLE_BYTES,
        "crates/trust-certify/src/scalar_return_family/bundle.rs:MAX_SCALAR_FAMILY_BUNDLE_BYTES",
    ) {
        return Err("scalar family bundle exceeds byte limit".to_string());
    }
    let mut reader = Reader { bytes, offset: 0 };
    if reader.take(MAGIC.len())? != MAGIC || reader.count(u32::MAX as usize)? != VERSION as usize {
        return Err("unknown scalar family bundle magic/version".to_string());
    }
    let model_sha256 = reader.hash()?;
    let count = reader.count(MAX_BASIS_DECLS)?;
    let mut basis = Vec::new();
    for _ in 0..count {
        basis.push((reader.name()?, reader.hash()?));
    }
    let count = reader.count(LOCAL_COUNT)?;
    if count != LOCAL_COUNT {
        return Err("scalar bundle declaration count mismatch".to_string());
    }
    let mut records = Vec::new();
    for _ in 0..count {
        let theorem = match reader.take(1)?[0] {
            0 => false,
            1 => true,
            _ => return Err("invalid declaration kind".to_string()),
        };
        records.push(Record {
            theorem,
            name: reader.name()?,
            ty: reader.blob_at(
                MAX_TERM_BYTES,
                "crates/trust-certify/src/scalar_return_family/bundle.rs:MAX_TERM_BYTES",
            )?,
            value: reader.blob_at(
                MAX_TERM_BYTES,
                "crates/trust-certify/src/scalar_return_family/bundle.rs:MAX_TERM_BYTES",
            )?,
        });
    }
    if reader.offset != bytes.len() {
        return Err("trailing scalar family bundle data".to_string());
    }
    Ok(Bundle { model_sha256, basis, records })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fixture() -> &'static Vec<u8> {
        static BUNDLE: std::sync::OnceLock<Vec<u8>> = std::sync::OnceLock::new();
        BUNDLE.get_or_init(|| {
            prove_u8_widen_add_one_family().expect("construct complete family proof")
        })
    }

    #[test]
    fn complete_bundle_replays_in_a_fresh_model_with_exact_dependency_roster() {
        let bundle = decode(fixture()).unwrap();
        assert_eq!(bundle.records.len(), LOCAL_COUNT);
        assert_eq!(bundle.records.iter().filter(|r| !r.theorem).count(), 4);
        for name in ["UInt8", "BitVec", "Fin", "Nat.le_of_succ_le_succ", "sm_run", "sm_observe"] {
            assert!(bundle.basis.iter().any(|(n, _)| n == name), "missing {name}");
        }
        eprintln!(
            "scalar bundle: {} bytes, {} local declarations, {} reconstructed basis declarations",
            fixture().len(),
            LOCAL_COUNT,
            bundle.basis.len()
        );
        replay_u8_widen_add_one_family(fixture()).unwrap();
    }

    fn rejected(bundle: &Bundle, stage: &str) {
        let bytes = encode(bundle).unwrap();
        let error = replay_u8_widen_add_one_family(&bytes).unwrap_err();
        assert!(error.contains(stage), "expected {stage}: {error}");
    }

    #[test]
    fn missing_reordered_renamed_or_kind_replaced_declarations_are_not_a_closure() {
        let original = decode(fixture()).unwrap();
        // Retain the advertised count with a duplicate, so a count-only check
        // would miss the missing definition/interior helper/final theorem.
        for index in [0, 1, 2, 3, 4, 132, LOCAL_COUNT - 1] {
            let mut bundle = original.clone();
            bundle.records.remove(index);
            bundle.records.push(original.records[0].clone());
            rejected(&bundle, "roster mismatch");
        }
        let mut swapped = original.clone();
        swapped.records.swap(130, 131);
        rejected(&swapped, "roster mismatch");
        let mut renamed = original.clone();
        renamed.records[0].name = "ScalarFamily.otherProgram".to_string();
        rejected(&renamed, "roster mismatch");
        let mut changed_kind = original;
        changed_kind.records[4].theorem = false;
        rejected(&changed_kind, "roster mismatch");
    }

    #[test]
    fn every_fixed_definition_and_canonical_goal_are_checked_not_wire_authored() {
        let original = decode(fixture()).unwrap();
        for index in 0..4 {
            let mut changed = original.clone();
            changed.records[index].value = serialize_term(&c("True.intro")).unwrap();
            rejected(&changed, "fixed definition mismatch");
        }
        // Coherently change the actual program AND the expected observation
        // to +2. This is another true theorem, not the claimed fixed family.
        let mut coherent = original.clone();
        let different = fixed_definitions(Construction {
            addend: 2,
            expected_return_addend: 2,
            ..Construction::default()
        });
        for (record, (_, _, value)) in coherent.records.iter_mut().zip(different) {
            record.value = serialize_term(&value).unwrap();
        }
        rejected(&coherent, "fixed definition mismatch");

        for index in [0, 4, 132, LOCAL_COUNT - 1] {
            let mut changed = original.clone();
            changed.records[index].ty = serialize_term(&c("True")).unwrap();
            rejected(&changed, "canonical goal mismatch");
        }
    }

    #[test]
    fn correctly_serialized_forged_final_proof_is_not_a_verdict() {
        let mut bundle = decode(fixture()).unwrap();
        bundle.records.last_mut().unwrap().value = serialize_term(&c("True.intro")).unwrap();
        rejected(&bundle, "roundtrip");
    }

    #[test]
    fn a_typechecking_foundational_axiom_dependency_still_refuses_replay() {
        let mut bundle = decode(fixture()).unwrap();
        let goal = universal_goal();
        // Classical.choice chooses a proof from an inhabited proof type. The
        // proposition is true and this term typechecks, but this axiom-free
        // family must reject its added foundational dependency anyway.
        let inhabited = poly("Nonempty.intro", Level::zero(), [goal.clone(), universal_proof()]);
        let proof = poly("Classical.choice", Level::zero(), [goal, inhabited]);
        bundle.records.last_mut().unwrap().value = serialize_term(&proof).unwrap();
        // This stage is reached only AFTER the ordinary kernel typecheck.
        rejected(&bundle, "axiom debt");
    }

    #[test]
    fn an_axiom_free_extra_dependency_cannot_be_borrowed() {
        crate::checker_core::run_on_large_stack(|| {
            let mut bundle = decode(fixture()).unwrap();
            let model = ScalarExecutionModel::new().unwrap();
            let env = model.environment();
            for name in ["UInt64", "UInt64.ofNat"] {
                let constant = Name::from_string(name);
                assert!(env.get_const(&constant).is_some(), "missing ambient {name}");
                assert!(env.axiom_deps(&constant).unwrap().is_empty());
                assert!(env.foundational_axiom_deps(&constant).unwrap().is_empty());
                assert!(!bundle.basis.iter().any(|(n, _)| n == name));
            }
            let extra_value = app("UInt64.ofNat", [n(0)]);
            TypeChecker::new(env)
                .check_type(&extra_value, &c("UInt64"))
                .expect("the extra axiom-free value actually typechecks");
            // The dead let preserves the true canonical proposition. It still
            // borrows an ambient declaration absent from the promised complete
            // closure, even though ordinary kernel checking and both axiom
            // audits succeed. Do not append that dependency to the wire basis.
            let proof = Expr::let_named(
                Name::from_string("extra"),
                c("UInt64"),
                extra_value,
                universal_proof(),
                false,
            );
            bundle.records.last_mut().unwrap().value = serialize_term(&proof).unwrap();
            // This exact stage is reached only after all 262 decoded terms,
            // including this full final proof, pass kernel checking and audits.
            rejected(&bundle, "undeclared dependency closure");
        })
        .expect("extra-dependency control worker");
    }

    #[test]
    fn model_or_reconstructed_foundation_identity_cannot_be_authored() {
        let original = decode(fixture()).unwrap();
        let mut model = original.clone();
        model.model_sha256 = "0".repeat(64);
        rejected(&model, "source binding mismatch");
        let mut omitted = original.clone();
        omitted.basis.pop();
        rejected(&omitted, "dependency manifest mismatch");
        let mut reordered = original.clone();
        reordered.basis.swap(0, 1);
        rejected(&reordered, "dependency manifest mismatch");
        let mut changed = original;
        changed.basis[0].1 = "0".repeat(64);
        rejected(&changed, "dependency manifest mismatch");
    }

    #[test]
    fn trailing_or_truncated_bundle_and_inner_term_data_are_refused() {
        let mut trailing = fixture().clone();
        trailing.extend_from_slice(b"extra unaudited record");
        assert!(replay_u8_widen_add_one_family(&trailing).unwrap_err().contains("trailing"));
        let truncated = &fixture()[..fixture().len() - 1];
        assert!(replay_u8_widen_add_one_family(truncated).unwrap_err().contains("truncated"));
        let mut inner = decode(fixture()).unwrap();
        inner.records[4].value.push(0);
        rejected(&inner, "decode");
    }

    fn local_count_offset(bytes: &[u8]) -> usize {
        let mut reader = Reader { bytes, offset: MAGIC.len() + 4 + 64 };
        let count = reader.count(MAX_BASIS_DECLS).unwrap();
        for _ in 0..count {
            reader.name().unwrap();
            reader.hash().unwrap();
        }
        reader.offset
    }

    #[test]
    fn wire_counts_lengths_versions_and_axiom_kinds_fail_before_kernel_work() {
        let original = fixture();
        let count_offset = local_count_offset(original);
        let first_record = count_offset + 4;
        let mut name_reader = Reader { bytes: original, offset: first_record + 1 };
        name_reader.name().unwrap();
        let first_type_length = name_reader.offset;
        for (offset, value) in [
            (MAGIC.len(), VERSION + 1),
            (MAGIC.len() + 4 + 64, (MAX_BASIS_DECLS + 1) as u32),
            (count_offset, (LOCAL_COUNT - 1) as u32),
            (count_offset, (LOCAL_COUNT + 1) as u32),
            (first_record + 1, (MAX_NAME_BYTES + 1) as u32),
            (first_type_length, (MAX_TERM_BYTES + 1) as u32),
        ] {
            let mut bytes = original.clone();
            bytes[offset..offset + 4].copy_from_slice(&value.to_le_bytes());
            assert!(decode(&bytes).is_err(), "accepted oversized/version field at {offset}");
        }
        let mut axiom = original.clone();
        axiom[first_record] = 2;
        assert!(replay_u8_widen_add_one_family(&axiom).unwrap_err().contains("kind"));
        let oversized = vec![0; MAX_SCALAR_FAMILY_BUNDLE_BYTES + 1];
        assert!(replay_u8_widen_add_one_family(&oversized).unwrap_err().contains("byte limit"));
    }
}
