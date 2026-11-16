//! Compiler-authenticated source-loop/place provenance for the E4/E5 flip lane.

use std::collections::{BTreeMap, BTreeSet};

use rustc_middle::mir;
use rustc_middle::mir::trust_contract::{
    TrustContractKind, TrustContractPredicateKind, TrustContractProposition,
    TrustContractPropositionDomain, TrustContractSource, TrustContractSubject,
};
use rustc_middle::ty::TyCtxt;
use rustc_middle::ty::print::with_no_trimmed_paths;
use rustc_span::def_id::LocalDefId;
use trust_ir::{
    BlockId, FuncId, Inst, Module, ProofDigest, SourceBindingProvenance, SourceLoopProvenance,
    SourcePlace, SourceProvenance,
};
use trust_types::VerifiableBody;

/// Private result of the built-vs-derived header-role comparison.  This value is
/// intentionally not the flip capability itself: [`crate::mir_differential`]
/// binds it to the definition/module/callee lineage before exposing an opaque
/// capability to the `mir_built` hook.
#[derive(Clone, Copy, Debug)]
pub(crate) struct AuthenticatedHeaderRoles {
    pub(crate) digest: ProofDigest,
}

const HEADER_ROLE_EVIDENCE_DOMAIN: &str = "trust_thir_lower.source_header_role_correspondence.v1";

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct SourceBindingPlan {
    pub(crate) name: String,
    pub(crate) hir_local_id: u32,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct SourceLoopPlan {
    pub(crate) source_loop_id: u32,
    pub(crate) hir_local_id: u32,
    pub(crate) bindings: Vec<SourceBindingPlan>,
}

fn put_u32(bytes: &mut Vec<u8>, value: u32) {
    bytes.extend_from_slice(&value.to_be_bytes());
}

fn put_u128(bytes: &mut Vec<u8>, value: u128) {
    bytes.extend_from_slice(&value.to_be_bytes());
}

fn put_i128(bytes: &mut Vec<u8>, value: i128) {
    bytes.extend_from_slice(&value.to_be_bytes());
}

fn put_str(bytes: &mut Vec<u8>, value: &str) {
    put_u32(bytes, u32::try_from(value.len()).unwrap_or(u32::MAX));
    bytes.extend_from_slice(value.as_bytes());
}

fn put_domain(bytes: &mut Vec<u8>, domain: TrustContractPropositionDomain) {
    match domain {
        TrustContractPropositionDomain::Bool => bytes.push(0),
        TrustContractPropositionDomain::MathematicalInt => bytes.push(1),
        TrustContractPropositionDomain::PointerSizedInt { width, signed } => {
            bytes.push(2);
            put_u32(bytes, width);
            bytes.push(u8::from(signed));
        }
        TrustContractPropositionDomain::MachineInt { width, signed } => {
            bytes.push(3);
            put_u32(bytes, width);
            bytes.push(u8::from(signed));
        }
        // Tag 4, appended rather than inserted: these bytes are a digest input,
        // so renumbering an existing domain would change the provenance hash of
        // every contract that does not involve a float.
        TrustContractPropositionDomain::Float { width } => {
            bytes.push(4);
            put_u32(bytes, width);
        }
    }
}

fn put_proposition(bytes: &mut Vec<u8>, proposition: &TrustContractProposition) {
    use TrustContractProposition as P;
    match proposition {
        P::Bool(value) => {
            bytes.push(0);
            bytes.push(u8::from(*value));
        }
        P::Int(value) => {
            bytes.push(1);
            put_i128(bytes, *value);
        }
        P::UInt(value) => {
            bytes.push(2);
            put_u128(bytes, *value);
        }
        // Tag appended for the same digest-stability reason as the domain above.
        // The BITS go in, not a rendered decimal: two spellings of one value
        // must not hash apart, and the two zeroes must not hash together.
        P::Float { bits, width } => {
            bytes.push(20);
            put_u32(bytes, *width);
            put_u128(bytes, u128::from(*bits));
        }
        P::Var { name, domain } => {
            bytes.push(3);
            put_str(bytes, name.as_str());
            put_domain(bytes, *domain);
        }
        P::Not(inner) => unary(bytes, 4, inner),
        P::And(terms) => terms_node(bytes, 5, terms),
        P::Or(terms) => terms_node(bytes, 6, terms),
        P::Implies(lhs, rhs) => binary(bytes, 7, lhs, rhs),
        P::Eq(lhs, rhs) => binary(bytes, 8, lhs, rhs),
        P::Lt(lhs, rhs) => binary(bytes, 9, lhs, rhs),
        P::Le(lhs, rhs) => binary(bytes, 10, lhs, rhs),
        P::Gt(lhs, rhs) => binary(bytes, 11, lhs, rhs),
        P::Ge(lhs, rhs) => binary(bytes, 12, lhs, rhs),
        P::Add(lhs, rhs) => binary(bytes, 13, lhs, rhs),
        P::Sub(lhs, rhs) => binary(bytes, 14, lhs, rhs),
        P::Mul(lhs, rhs) => binary(bytes, 15, lhs, rhs),
        P::Div(lhs, rhs) => binary(bytes, 16, lhs, rhs),
        P::Rem(lhs, rhs) => binary(bytes, 17, lhs, rhs),
        P::Neg(inner) => unary(bytes, 18, inner),
    }
}

fn unary(bytes: &mut Vec<u8>, tag: u8, inner: &TrustContractProposition) {
    bytes.push(tag);
    put_proposition(bytes, inner);
}

fn binary(
    bytes: &mut Vec<u8>,
    tag: u8,
    lhs: &TrustContractProposition,
    rhs: &TrustContractProposition,
) {
    bytes.push(tag);
    put_proposition(bytes, lhs);
    put_proposition(bytes, rhs);
}

fn terms_node(bytes: &mut Vec<u8>, tag: u8, terms: &[TrustContractProposition]) {
    bytes.push(tag);
    put_u32(bytes, u32::try_from(terms.len()).unwrap_or(u32::MAX));
    for term in terms {
        put_proposition(bytes, term);
    }
}

/// Rebuild the complete compiler-owned loop/binding catalog. The catalog is
/// independent of TrustIR; a partial query sidecar fails closed.
pub(crate) fn source_loop_plans(
    tcx: TyCtxt<'_>,
    def: LocalDefId,
) -> Result<Vec<SourceLoopPlan>, String> {
    let bundle = tcx.trust_contracts(def.to_def_id());
    let authored_clause_count = tcx
        .hir_maybe_body_owned_by(def)
        .and_then(|body| body.contract)
        .map_or(0, |contract| contract.loop_clauses.len());
    if bundle.loop_contracts.len() != authored_clause_count {
        return Err("fresh query loop catalog does not match authored HIR clauses".into());
    }
    let mut loops = BTreeMap::<u32, (u32, BTreeMap<String, u32>)>::new();
    for contract in &bundle.loop_contracts {
        let TrustContractSubject::HirLoop { id, .. } = contract.subject else {
            return Err("loop contract lacks HIR-loop identity".into());
        };
        let bindings = contract
            .predicate
            .source_place_bindings
            .as_ref()
            .ok_or_else(|| "loop contract has incomplete source-place bindings".to_string())?;
        let entry = loops.entry(id.index).or_insert_with(|| (id.hir_local_id, BTreeMap::new()));
        if entry.0 != id.hir_local_id {
            return Err("one source-loop index names multiple HIR loops".into());
        }
        for binding in bindings {
            let name = binding.name.to_string();
            if let Some(previous) = entry.1.insert(name, binding.hir_local_id) {
                if previous != binding.hir_local_id {
                    return Err("one source name maps to multiple HIR locals".into());
                }
            }
        }
    }
    let mut result = Vec::with_capacity(loops.len());
    let mut seen_loop_hir = BTreeSet::new();
    for (expected, (source_loop_id, (hir_local_id, bindings))) in loops.into_iter().enumerate() {
        if source_loop_id != u32::try_from(expected).unwrap_or(u32::MAX) {
            return Err("source-loop ids are not dense and ordered".into());
        }
        if !seen_loop_hir.insert(hir_local_id) {
            return Err("distinct source-loop ids share one HIR-loop identity".into());
        }
        let mut seen_hir = BTreeSet::new();
        let bindings = bindings
            .into_iter()
            .map(|(name, hir_local_id)| {
                if !seen_hir.insert(hir_local_id) {
                    return Err("one HIR local has multiple source names".to_string());
                }
                Ok(SourceBindingPlan { name, hir_local_id })
            })
            .collect::<Result<Vec<_>, _>>()?;
        result.push(SourceLoopPlan { source_loop_id, hir_local_id, bindings });
    }
    Ok(result)
}

/// Fresh compiler digest over function identity and the complete ordered loop
/// clause catalog. This authenticates the source side of the carrier; it is
/// deliberately regenerated at both production and consumption.
pub(crate) fn compiler_source_digest(
    tcx: TyCtxt<'_>,
    def: LocalDefId,
) -> Result<ProofDigest, String> {
    let bundle = tcx.trust_contracts(def.to_def_id());
    let mut bytes = Vec::new();
    let path = with_no_trimmed_paths!(tcx.def_path_str(def.to_def_id()));
    put_str(&mut bytes, &path);
    put_u32(
        &mut bytes,
        u32::try_from(bundle.loop_contracts.len())
            .map_err(|_| "too many loop contracts for provenance")?,
    );
    for contract in &bundle.loop_contracts {
        bytes.push(match contract.kind {
            TrustContractKind::LoopInvariant => 0,
            TrustContractKind::Decreases => 1,
            _ => return Err("non-E4/E5 clause in loop-contract catalog".into()),
        });
        if contract.source != TrustContractSource::Native {
            return Err("non-native clause in loop-contract catalog".into());
        }
        let TrustContractSubject::HirLoop { id, .. } = contract.subject else {
            return Err("loop contract lacks HIR-loop identity".into());
        };
        put_u32(&mut bytes, id.index);
        put_u32(&mut bytes, id.hir_local_id);
        match &contract.predicate.kind {
            TrustContractPredicateKind::Typed { proposition, .. } => {
                bytes.push(0);
                put_proposition(&mut bytes, proposition);
            }
            TrustContractPredicateKind::BoolLiteral { value } => {
                // Literal loop invariants have a complete empty binding map,
                // but their truth value still belongs to the authenticated
                // compiler-source image.
                bytes.push(1);
                bytes.push(u8::from(*value));
            }
            TrustContractPredicateKind::Opaque { .. }
            | TrustContractPredicateKind::MirLocal { .. }
            | TrustContractPredicateKind::Unsupported { .. } => {
                return Err("loop contract is not a structural proposition".into());
            }
        }
        let bindings = contract
            .predicate
            .source_place_bindings
            .as_ref()
            .ok_or_else(|| "loop contract has incomplete source-place bindings".to_string())?;
        put_u32(&mut bytes, u32::try_from(bindings.len()).unwrap_or(u32::MAX));
        for binding in bindings {
            put_str(&mut bytes, binding.name.as_str());
            put_u32(&mut bytes, binding.hir_local_id);
        }
    }
    Ok(ProofDigest::sha256_domain("trust.rustc.source_loop_catalog.v1", &bytes))
}

fn successors(block: &trust_ir::Block) -> Vec<BlockId> {
    match block.terminator().map(|node| &node.inst) {
        Some(Inst::Br { target, .. }) => vec![*target],
        Some(Inst::CondBr { then_target, else_target, .. }) => {
            vec![*then_target, *else_target]
        }
        Some(Inst::Switch { default, cases, .. }) => {
            let mut targets = cases.iter().map(|case| case.target).collect::<Vec<_>>();
            targets.push(*default);
            targets
        }
        Some(Inst::Invoke { normal_dest, unwind_dest, .. }) => {
            vec![*normal_dest, *unwind_dest]
        }
        _ => Vec::new(),
    }
}

/// Reconstruct exact natural-loop headers independently from the carrier.
/// An edge is a backedge iff its target dominates its source; ordinary exits
/// may also point to an earlier-created block, so block-id ordering is never
/// treated as loop evidence. The returned set's iteration order carries no
/// authority. Header iteration order is deliberately discarded below.
fn structural_loop_headers(module: &Module) -> Result<Vec<BlockId>, String> {
    let function = module
        .function_by_id(FuncId::new(0))
        .ok_or_else(|| "module lacks body function #0".to_string())?;
    let blocks = function.blocks.iter().map(|block| (block.id, block)).collect::<BTreeMap<_, _>>();
    let mut reachable = BTreeSet::new();
    let mut work = vec![function.entry];
    while let Some(block) = work.pop() {
        if !reachable.insert(block) {
            continue;
        }
        let body =
            blocks.get(&block).ok_or_else(|| "reachable edge names a missing block".to_string())?;
        work.extend(successors(body));
    }
    let mut predecessors =
        reachable.iter().map(|block| (*block, BTreeSet::new())).collect::<BTreeMap<_, _>>();
    for source in &reachable {
        for target in successors(blocks[source]) {
            if let Some(preds) = predecessors.get_mut(&target) {
                preds.insert(*source);
            }
        }
    }
    let mut dominators = BTreeMap::<BlockId, BTreeSet<BlockId>>::new();
    for block in &reachable {
        dominators.insert(
            *block,
            if *block == function.entry {
                [*block].into_iter().collect()
            } else {
                reachable.clone()
            },
        );
    }
    loop {
        let mut changed = false;
        for block in reachable.iter().copied().filter(|block| *block != function.entry) {
            let preds = &predecessors[&block];
            let mut next = if let Some(first) = preds.iter().next() {
                dominators[first].clone()
            } else {
                BTreeSet::new()
            };
            for pred in preds.iter().skip(1) {
                next = next.intersection(&dominators[pred]).copied().collect();
            }
            next.insert(block);
            if dominators[&block] != next {
                dominators.insert(block, next);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    let mut headers = BTreeSet::new();
    for source in &reachable {
        for target in successors(blocks[source]) {
            if dominators[source].contains(&target) {
                headers.insert(target);
            }
        }
    }
    Ok(headers.into_iter().collect())
}

/// Validate and independently reconstruct the exact source-loop/place map.
///
/// For multiple loops this establishes a complete bijection between the fresh
/// source catalog and the carrier, and between carried headers and structural
/// TrustIR natural headers.  It deliberately does *not* authorize which HIR
/// loop owns which header: [`authenticate_source_header_correspondence`] adds
/// that cross-domain authority from independently built MIR before a green
/// registry entry can be minted.
pub(crate) fn validated_source_provenance(
    tcx: TyCtxt<'_>,
    def: LocalDefId,
    module: &Module,
) -> Result<Option<SourceProvenance>, String> {
    let plans = source_loop_plans(tcx, def)?;
    let compiler_digest = compiler_source_digest(tcx, def)?;
    validated_source_provenance_against(module, &plans, compiler_digest)
}

fn validated_source_provenance_against(
    module: &Module,
    plans: &[SourceLoopPlan],
    compiler_digest: ProofDigest,
) -> Result<Option<SourceProvenance>, String> {
    let function = module
        .function_by_id(FuncId::new(0))
        .ok_or_else(|| "module lacks body function #0".to_string())?;
    if plans.is_empty() {
        return if function.source_provenance.is_none() {
            Ok(None)
        } else {
            Err("contract-free function carries unexpected source provenance".into())
        };
    }
    let provenance = function
        .source_provenance
        .as_ref()
        .ok_or_else(|| "loop contracts require source provenance".to_string())?;
    if !trust_ir_build::validate_module(module).is_empty() {
        return Err("TrustIR source provenance failed structural validation".into());
    }
    if provenance.compiler_source_digest != compiler_digest {
        return Err("source provenance compiler digest mismatch".into());
    }
    let semantic = module
        .source_provenance_semantic_digest(FuncId::new(0))
        .map_err(|error| format!("source provenance semantic digest: {error}"))?;
    if provenance.semantic_body_digest != semantic {
        return Err("source provenance semantic-body digest mismatch".into());
    }
    if !provenance.binding_digest_is_valid() {
        return Err("source provenance binding digest mismatch".into());
    }
    let structural_headers = structural_loop_headers(module)?.into_iter().collect::<BTreeSet<_>>();
    if structural_headers.len() != plans.len() || provenance.loops.len() != plans.len() {
        return Err("source/TrustIR loop count mismatch".into());
    }

    // Match by the compiler-owned dense source-loop id, never by either
    // vector's order.  At this boundary a swapped, self-resealed multi-loop
    // carrier remains only a structurally complete *claim*; the independent
    // built/derived canonical-role check below is what accepts or rejects it.
    let mut carried_by_source = BTreeMap::<u32, &SourceLoopProvenance>::new();
    let mut carried_hir_owners = BTreeMap::<u32, u32>::new();
    let mut carried_headers = BTreeSet::<BlockId>::new();
    for carried in &provenance.loops {
        if carried_by_source.insert(carried.source_loop_id, carried).is_some() {
            return Err("source provenance repeats one source-loop id".into());
        }
        if let Some(previous) =
            carried_hir_owners.insert(carried.hir_local_id, carried.source_loop_id)
        {
            if previous != carried.source_loop_id {
                return Err("source provenance maps two source loops to one HIR loop".into());
            }
        }
        if !carried_headers.insert(carried.header) {
            return Err("source provenance maps two source loops to one TrustIR header".into());
        }
    }
    if carried_headers != structural_headers {
        return Err("source provenance does not cover the exact structural header set".into());
    }

    for plan in plans {
        let carried = carried_by_source
            .get(&plan.source_loop_id)
            .copied()
            .ok_or_else(|| "source-loop plan is absent from provenance".to_string())?;
        if carried.source_loop_id != plan.source_loop_id
            || carried.hir_local_id != plan.hir_local_id
            || carried.bindings.len() != plan.bindings.len()
        {
            return Err("source-loop provenance identity mismatch".into());
        }
        let block = function
            .block(carried.header)
            .ok_or_else(|| "source-loop provenance header is missing".to_string())?;
        for (index, (expected, actual)) in plan.bindings.iter().zip(&carried.bindings).enumerate() {
            let expected_index = u32::try_from(index).map_err(|_| "too many source bindings")?;
            if actual.name != expected.name
                || actual.hir_local_id != expected.hir_local_id
                || actual.place != (SourcePlace::LoopParameter { index: expected_index })
                || block.params.get(index).is_none()
            {
                return Err("source-place provenance mapping mismatch".into());
            }
        }
    }
    Ok(Some(provenance.clone()))
}

/// Pure final cross-domain check, factored out so swapped/self-resealed
/// adversaries are executable unit obligations rather than comments.
fn validate_header_correspondence_against(
    provenance: &SourceProvenance,
    ir_header_roles: &BTreeMap<BlockId, Vec<u32>>,
    built_source_roles: &BTreeMap<u32, (u32, Vec<u32>)>,
) -> Result<(), String> {
    if ir_header_roles.len() != provenance.loops.len()
        || built_source_roles.len() != provenance.loops.len()
    {
        return Err("source-header correspondence is partial".into());
    }

    let ir_unique = ir_header_roles.values().cloned().collect::<BTreeSet<_>>();
    let built_unique =
        built_source_roles.values().map(|(_, role)| role.clone()).collect::<BTreeSet<_>>();
    if ir_unique.len() != ir_header_roles.len() || built_unique.len() != built_source_roles.len() {
        return Err("source-loop canonical CFG roles are ambiguous".into());
    }

    for carried in &provenance.loops {
        let ir_role = ir_header_roles
            .get(&carried.header)
            .ok_or_else(|| "carried TrustIR header has no canonical CFG role".to_string())?;
        let (built_hir, built_role) = built_source_roles
            .get(&carried.source_loop_id)
            .ok_or_else(|| "source loop has no compiler-stamped built-MIR header".to_string())?;
        if *built_hir != carried.hir_local_id {
            return Err("compiler-stamped built header has a different HIR-loop identity".into());
        }
        if built_role != ir_role {
            return Err("TrustIR/built-MIR source-loop canonical CFG role mismatch".into());
        }
    }
    Ok(())
}

/// Canonically bind both sides of the successfully checked role map.  Raw ids
/// are included only as subjects of the relation; they are never compared to
/// one another.  `module` lineage separately binds the carried BlockIds, while
/// this digest makes the exact translated-role and compiler-stamped-role maps
/// part of the opaque authority witness rather than leaving the witness as a
/// bare success bit.
fn header_role_evidence_digest(
    provenance: Option<&SourceProvenance>,
    ir_header_roles: &BTreeMap<BlockId, Vec<u32>>,
    built_source_roles: &BTreeMap<u32, (u32, usize, Vec<u32>)>,
) -> Result<ProofDigest, String> {
    let mut bytes = Vec::new();
    let loops = provenance.map_or(&[][..], |p| p.loops.as_slice());
    put_u32(
        &mut bytes,
        u32::try_from(loops.len()).map_err(|_| "too many source loops for role evidence")?,
    );
    for carried in loops {
        let ir_role = ir_header_roles
            .get(&carried.header)
            .ok_or_else(|| "role evidence lacks a carried TrustIR header".to_string())?;
        let (built_hir, built_header, built_role) = built_source_roles
            .get(&carried.source_loop_id)
            .ok_or_else(|| "role evidence lacks a compiler-stamped source loop".to_string())?;
        put_u32(&mut bytes, carried.source_loop_id);
        put_u32(&mut bytes, carried.hir_local_id);
        put_u32(
            &mut bytes,
            u32::try_from(carried.header.index())
                .map_err(|_| "TrustIR header id is too large for role evidence")?,
        );
        put_u32(&mut bytes, *built_hir);
        put_u32(
            &mut bytes,
            u32::try_from(*built_header)
                .map_err(|_| "built MIR header id is too large for role evidence")?,
        );
        for role in [ir_role.as_slice(), built_role.as_slice()] {
            put_u32(
                &mut bytes,
                u32::try_from(role.len()).map_err(|_| "CFG role is too long for evidence")?,
            );
            for slot in role {
                put_u32(&mut bytes, *slot);
            }
        }
    }
    Ok(ProofDigest::sha256_domain(HEADER_ROLE_EVIDENCE_DOMAIN, &bytes))
}

/// Authenticate the carried HIR-loop -> TrustIR-header association against the
/// freshly built MIR sibling.
///
/// `rustc_mir_build` stamps `trust_loop_hir_local_id` into loop source scopes.
/// `trust_mir_extract::stamp_loop_header_provenance` independently re-detects
/// dominator-proved built-MIR backedges and binds those stamps to exact native
/// headers.  Separately, the translator supplies its `BlockId -> BasicBlock`
/// map and both extracted CFGs reconstruct unique goto-threaded DFS roles.
/// Equal roles establish the cross-domain correspondence without consulting
/// producer allocation order, numeric ids, spans, or the carrier's digest.
pub(crate) fn authenticate_source_header_correspondence(
    tcx: TyCtxt<'_>,
    def: LocalDefId,
    module: &Module,
    ir_block_map: &std::collections::HashMap<BlockId, mir::BasicBlock>,
    built: &mir::Body<'_>,
    derived_extracted: &VerifiableBody,
    built_extracted: &VerifiableBody,
) -> Result<AuthenticatedHeaderRoles, String> {
    let Some(provenance) = validated_source_provenance(tcx, def, module)? else {
        return Ok(AuthenticatedHeaderRoles {
            digest: header_role_evidence_digest(None, &BTreeMap::new(), &BTreeMap::new())?,
        });
    };

    let derived_roles = crate::mir_differential::canonical_cfg_roles(derived_extracted)
        .map_err(|reason| format!("derived CFG roles: {reason}"))?;
    let built_roles = crate::mir_differential::canonical_cfg_roles(built_extracted)
        .map_err(|reason| format!("built CFG roles: {reason}"))?;

    let mut ir_header_roles = BTreeMap::<BlockId, Vec<u32>>::new();
    for carried in &provenance.loops {
        let translated = ir_block_map
            .get(&carried.header)
            .ok_or_else(|| "TrustIR provenance header was not translated".to_string())?;
        let role = derived_roles
            .role(translated.index())
            .ok_or_else(|| "translated TrustIR header has no canonical CFG role".to_string())?;
        if ir_header_roles.insert(carried.header, role.to_vec()).is_some() {
            return Err("TrustIR provenance repeats one translated header".into());
        }
    }

    let rustc_bundle = tcx.trust_contracts(def.to_def_id());
    let mut portable = trust_mir_extract::convert_trust_contract_bundle(tcx, rustc_bundle)
        .map_err(|reason| format!("built loop catalog conversion: {reason}"))?;
    let failures = trust_mir_extract::stamp_loop_header_provenance(built, &mut portable);
    if !failures.is_empty() {
        return Err(format!("built loop-header stamping failed: {failures:?}"));
    }

    let mut built_source_roles = BTreeMap::<u32, (u32, usize, Vec<u32>)>::new();
    for spec in &portable.loop_contracts {
        let hir = spec
            .source_hir_local_id
            .ok_or_else(|| "built loop row lacks HIR identity".to_string())?;
        let header = spec
            .mir_header
            .ok_or_else(|| "built loop row lacks an authenticated MIR header".to_string())?;
        let role = built_roles
            .role(header)
            .ok_or_else(|| "compiler-stamped built header has no canonical CFG role".to_string())?
            .to_vec();
        match built_source_roles.entry(spec.source_loop_id) {
            std::collections::btree_map::Entry::Vacant(entry) => {
                entry.insert((hir, header, role));
            }
            std::collections::btree_map::Entry::Occupied(entry)
                if entry.get() == &(hir, header, role) => {}
            std::collections::btree_map::Entry::Occupied(_) => {
                return Err("clauses on one source loop disagree on built header identity".into());
            }
        }
    }

    let comparable_built_roles = built_source_roles
        .iter()
        .map(|(&source, &(hir, _, ref role))| (source, (hir, role.clone())))
        .collect();
    validate_header_correspondence_against(&provenance, &ir_header_roles, &comparable_built_roles)?;
    Ok(AuthenticatedHeaderRoles {
        digest: header_role_evidence_digest(
            Some(&provenance),
            &ir_header_roles,
            &built_source_roles,
        )?,
    })
}

pub(crate) fn seal_source_provenance(
    tcx: TyCtxt<'_>,
    def: LocalDefId,
    module: &mut Module,
    loops: Vec<SourceLoopProvenance>,
) -> Result<(), String> {
    if loops.is_empty() {
        return Ok(());
    }
    let compiler = compiler_source_digest(tcx, def)?;
    let semantic = module.source_provenance_semantic_digest(FuncId::new(0))?;
    let function = module
        .function_by_id_mut(FuncId::new(0))
        .ok_or_else(|| "module lacks body function #0".to_string())?;
    function.source_provenance = Some(SourceProvenance::new(compiler, semantic, loops));
    Ok(())
}

pub(crate) fn binding_carrier(
    source_loop_id: u32,
    hir_local_id: u32,
    header: BlockId,
    bindings: &[SourceBindingPlan],
) -> SourceLoopProvenance {
    SourceLoopProvenance {
        source_loop_id,
        hir_local_id,
        header,
        bindings: bindings
            .iter()
            .enumerate()
            .map(|(index, binding)| SourceBindingProvenance {
                name: binding.name.clone(),
                hir_local_id: binding.hir_local_id,
                place: SourcePlace::LoopParameter {
                    index: u32::try_from(index).unwrap_or(u32::MAX),
                },
            })
            .collect(),
    }
}

#[cfg(test)]
mod tests {
    use trust_ir::{Block, Constant, FuncTy, Function, InstrNode, Ty, ValueId};

    use super::*;

    fn authenticated_fixture() -> (Module, Vec<SourceLoopPlan>, ProofDigest) {
        let mut module = Module::new("authenticated-source-loop");
        let signature = module
            .add_func_type(FuncTy { params: vec![], returns: vec![], is_vararg: false, abi: None })
            .expect("Module::add_func_type: test fixture");
        let mut function = Function::new(FuncId::new(0), "f", signature, BlockId::new(0));
        let initial = ValueId::new(0);
        let carried = ValueId::new(1);
        let condition = ValueId::new(2);
        let mut entry = Block::new(BlockId::new(0));
        entry.body.push(
            InstrNode::new(Inst::Const { ty: Ty::I32, value: Constant::Int(1) })
                .with_result(initial),
        );
        entry.body.push(InstrNode::new(Inst::Br { target: BlockId::new(1), args: vec![initial] }));
        let mut header = Block::new(BlockId::new(1)).with_param(carried, Ty::I32);
        header.body.push(
            InstrNode::new(Inst::Const { ty: Ty::Bool, value: Constant::Bool(true) })
                .with_result(condition),
        );
        header.body.push(InstrNode::new(Inst::CondBr {
            cond: condition,
            then_target: BlockId::new(3),
            then_args: vec![],
            else_target: BlockId::new(2),
            else_args: vec![],
        }));
        let mut exit = Block::new(BlockId::new(2));
        exit.body.push(InstrNode::new(Inst::Return { values: vec![] }));
        let mut body = Block::new(BlockId::new(3));
        body.body.push(InstrNode::new(Inst::Br { target: BlockId::new(1), args: vec![carried] }));
        function.blocks = vec![entry, header, exit, body];
        module.try_add_function(function).expect("Module::try_add_function: test fixture");

        let plans = vec![SourceLoopPlan {
            source_loop_id: 0,
            hir_local_id: 3,
            bindings: vec![SourceBindingPlan { name: "x".into(), hir_local_id: 7 }],
        }];
        let compiler_digest = ProofDigest::sha256_domain("test.compiler.catalog", b"f/x");
        let semantic = module.source_provenance_semantic_digest(FuncId::new(0)).unwrap();
        module.functions[0].source_provenance = Some(SourceProvenance::new(
            compiler_digest,
            semantic,
            vec![binding_carrier(0, 3, BlockId::new(1), &plans[0].bindings)],
        ));
        (module, plans, compiler_digest)
    }

    fn two_loop_fixture() -> Module {
        let mut module = Module::new("two-source-loops");
        let signature = module
            .add_func_type(FuncTy { params: vec![], returns: vec![], is_vararg: false, abi: None })
            .expect("Module::add_func_type: test fixture");
        let mut function = Function::new(FuncId::new(0), "f", signature, BlockId::new(0));
        let first_condition = ValueId::new(0);
        let second_condition = ValueId::new(1);
        let mut entry = Block::new(BlockId::new(0));
        entry.body.push(InstrNode::new(Inst::Br { target: BlockId::new(20), args: vec![] }));

        let mut first_header = Block::new(BlockId::new(20));
        first_header.body.push(
            InstrNode::new(Inst::Const { ty: Ty::Bool, value: Constant::Bool(true) })
                .with_result(first_condition),
        );
        first_header.body.push(InstrNode::new(Inst::CondBr {
            cond: first_condition,
            then_target: BlockId::new(21),
            then_args: vec![],
            else_target: BlockId::new(5),
            else_args: vec![],
        }));
        let mut first_body = Block::new(BlockId::new(21));
        first_body.body.push(InstrNode::new(Inst::Br { target: BlockId::new(20), args: vec![] }));

        let mut between = Block::new(BlockId::new(5));
        between.body.push(InstrNode::new(Inst::Br { target: BlockId::new(3), args: vec![] }));
        let mut second_header = Block::new(BlockId::new(3));
        second_header.body.push(
            InstrNode::new(Inst::Const { ty: Ty::Bool, value: Constant::Bool(true) })
                .with_result(second_condition),
        );
        second_header.body.push(InstrNode::new(Inst::CondBr {
            cond: second_condition,
            then_target: BlockId::new(4),
            then_args: vec![],
            else_target: BlockId::new(30),
            else_args: vec![],
        }));
        let mut second_body = Block::new(BlockId::new(4));
        second_body.body.push(InstrNode::new(Inst::Br { target: BlockId::new(3), args: vec![] }));
        let mut exit = Block::new(BlockId::new(30));
        exit.body.push(InstrNode::new(Inst::Return { values: vec![] }));
        function.blocks =
            vec![entry, first_header, first_body, between, second_header, second_body, exit];
        module.try_add_function(function).expect("Module::try_add_function: test fixture");
        module
    }

    #[test]
    fn natural_header_reconstruction_does_not_mistake_backward_exit_edges() {
        let mut module = Module::new("source-loop-structure");
        let signature = module
            .add_func_type(FuncTy { params: vec![], returns: vec![], is_vararg: false, abi: None })
            .expect("Module::add_func_type: test fixture");
        let mut function = Function::new(FuncId::new(0), "f", signature, BlockId::new(0));
        let mut entry = Block::new(BlockId::new(0));
        entry.body.push(InstrNode::new(Inst::Br { target: BlockId::new(1), args: vec![] }));
        let cond = ValueId::new(0);
        let mut header = Block::new(BlockId::new(1));
        header.body.push(
            InstrNode::new(Inst::Const { ty: Ty::Bool, value: Constant::Bool(true) })
                .with_result(cond),
        );
        header.body.push(InstrNode::new(Inst::CondBr {
            cond,
            then_target: BlockId::new(3),
            then_args: vec![],
            else_target: BlockId::new(2),
            else_args: vec![],
        }));
        let mut exit = Block::new(BlockId::new(2));
        exit.body.push(InstrNode::new(Inst::Return { values: vec![] }));
        let mut body = Block::new(BlockId::new(3));
        body.body.push(InstrNode::new(Inst::CondBr {
            cond,
            then_target: BlockId::new(4),
            then_args: vec![],
            // This is a backward-by-id edge, but not a backedge: exit does
            // not dominate the body.
            else_target: BlockId::new(2),
            else_args: vec![],
        }));
        let mut latch = Block::new(BlockId::new(4));
        latch.body.push(InstrNode::new(Inst::Br { target: BlockId::new(1), args: vec![] }));
        function.blocks = vec![entry, header, exit, body, latch];
        module.try_add_function(function).expect("Module::try_add_function: test fixture");

        assert_eq!(structural_loop_headers(&module).unwrap(), vec![BlockId::new(1)]);
    }

    #[test]
    fn multiple_source_headers_need_independent_canonical_role_identity() {
        let mut module = two_loop_fixture();
        let structural = structural_loop_headers(&module).unwrap();
        assert_eq!(structural.len(), 2);
        assert!(structural.contains(&BlockId::new(20)) && structural.contains(&BlockId::new(3)));

        let plans = vec![
            SourceLoopPlan { source_loop_id: 0, hir_local_id: 10, bindings: vec![] },
            SourceLoopPlan { source_loop_id: 1, hir_local_id: 11, bindings: vec![] },
        ];
        let compiler_digest = ProofDigest::sha256_domain("test.compiler.catalog", b"f/loops");
        let semantic = module.source_provenance_semantic_digest(FuncId::new(0)).unwrap();
        module.functions[0].source_provenance = Some(SourceProvenance::new(
            compiler_digest,
            semantic,
            vec![
                binding_carrier(0, 10, BlockId::new(20), &[]),
                binding_carrier(1, 11, BlockId::new(3), &[]),
            ],
        ));
        let valid = validated_source_provenance_against(&module, &plans, compiler_digest)
            .expect("fresh catalog and exact structural header set make a complete claim")
            .expect("contracted fixture carries provenance");
        let ir_roles = BTreeMap::from([(BlockId::new(20), vec![0]), (BlockId::new(3), vec![1, 0])]);
        let built_roles = BTreeMap::from([(0, (10, vec![0])), (1, (11, vec![1, 0]))]);
        validate_header_correspondence_against(&valid, &ir_roles, &built_roles)
            .expect("correct multi-loop association has equal unique roles");

        let mut block_id_forgery = module.clone();
        block_id_forgery.functions[0].source_provenance = Some(SourceProvenance::new(
            compiler_digest,
            semantic,
            vec![
                binding_carrier(0, 10, BlockId::new(3), &[]),
                binding_carrier(1, 11, BlockId::new(20), &[]),
            ],
        ));
        let resealed_forgery =
            validated_source_provenance_against(&block_id_forgery, &plans, compiler_digest)
                .expect("the resealed swap is intentionally a structurally complete claim")
                .expect("contracted fixture carries provenance");
        assert_eq!(
            validate_header_correspondence_against(&resealed_forgery, &ir_roles, &built_roles,)
                .unwrap_err(),
            "TrustIR/built-MIR source-loop canonical CFG role mismatch",
            "a swapped and self-resealed BlockId association cannot borrow producer authority",
        );

        let ambiguous_ir_roles =
            BTreeMap::from([(BlockId::new(20), vec![0]), (BlockId::new(3), vec![0])]);
        assert_eq!(
            validate_header_correspondence_against(&valid, &ambiguous_ir_roles, &built_roles,)
                .unwrap_err(),
            "source-loop canonical CFG roles are ambiguous",
            "isomorphic loops still need distinct whole-graph roles",
        );
    }

    #[test]
    fn binding_carrier_uses_canonical_loop_parameter_prefix() {
        let bindings = vec![
            SourceBindingPlan { name: "a".into(), hir_local_id: 7 },
            SourceBindingPlan { name: "z".into(), hir_local_id: 11 },
        ];
        let carrier = binding_carrier(0, 3, BlockId::new(5), &bindings);
        assert_eq!(
            carrier.bindings.iter().map(|binding| binding.place).collect::<Vec<_>>(),
            vec![SourcePlace::LoopParameter { index: 0 }, SourcePlace::LoopParameter { index: 1 },]
        );
    }

    #[test]
    fn consumer_rejects_stale_forged_and_unexpected_carriers() {
        let (module, plans, compiler_digest) = authenticated_fixture();
        validated_source_provenance_against(&module, &plans, compiler_digest)
            .expect("fresh compiler, semantic, binding, and structural identities agree");

        let stale_compiler = ProofDigest::sha256_domain("test.compiler.catalog", b"other");
        assert!(
            validated_source_provenance_against(&module, &plans, stale_compiler).is_err(),
            "fresh compiler identity must reject a carrier from another source catalog",
        );

        let mut changed_body = module.clone();
        let Inst::Const { value, .. } = &mut changed_body.functions[0].blocks[0].body[0].inst
        else {
            panic!("fixture entry starts with a constant")
        };
        *value = Constant::Int(2);
        assert!(
            validated_source_provenance_against(&changed_body, &plans, compiler_digest).is_err(),
            "a semantic edit must invalidate the original carrier",
        );

        let mut forged_binding = module.clone();
        let forged_plan = SourceBindingPlan { name: "y".into(), hir_local_id: 7 };
        let semantic = forged_binding.source_provenance_semantic_digest(FuncId::new(0)).unwrap();
        forged_binding.functions[0].source_provenance = Some(SourceProvenance::new(
            compiler_digest,
            semantic,
            vec![binding_carrier(0, 3, BlockId::new(1), &[forged_plan])],
        ));
        assert!(
            validated_source_provenance_against(&forged_binding, &plans, compiler_digest).is_err(),
            "a self-consistent reseal cannot change the fresh compiler's binding map",
        );

        assert!(
            validated_source_provenance_against(&module, &[], compiler_digest).is_err(),
            "a contract-free source catalog must reject injected authority",
        );
    }
}
