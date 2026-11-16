//! D39/D40: the sealed, strict-only level-R metadata input to the existing assembler.
//!
//! P-TIR trusts that one dependency compilation produced the encoded body and census.
//! We bind the actual Rust owner, producer mode, target, signatures and callee instances,
//! and rederive D28 over the decoded bytes. No producer verdict bit is an input.
//! P-TIR includes the canonical producer refusing unexported inherited-overflow attributes;
//! missing upstream attributes cannot establish their absence. Named producer refusals survive.
//! The token grants structural admission only; emitted bytes still owe the strict gate.
//! This file and its identity-recovery delegate require an exact freeze at landing.

use rustc_abi::ExternAbi;
use rustc_hir::def::DefKind;
use rustc_middle::ty::{self, TyCtxt, TypeVisitableExt};
use trust_ir::{CallingConv, Endianness, FuncId, FuncTy, Module, StructPassingPolicy, Ty};
use trust_thir_lower::rmeta_entry::{self, EntryBinding, EntryDecodeError, EvidenceLedgerRow};

use super::{FrontendRefusal, clean_below_gate, instance_assembly};

#[derive(Debug, Clone)]
pub(super) struct Refusal {
    check: &'static str,
    detail: String,
    clean: Option<clean_below_gate::CleanRowRefusal>,
}
impl Refusal {
    fn new(check: &'static str, detail: impl Into<String>) -> Self {
        Self { check, detail: detail.into(), clean: None }
    }
    pub(super) fn frontend(&self, symbol: &str) -> FrontendRefusal {
        if let Some(row) = &self.clean {
            return FrontendRefusal::CleanBelowGate { symbol: symbol.into(), row: row.clone() };
        }
        match self.check {
            "effects" => FrontendRefusal::EffectNotConserved {
                symbol: symbol.into(),
                detail: self.detail.clone(),
            },
            "abi" => FrontendRefusal::UnsupportedAbi {
                symbol: symbol.into(),
                detail: self.detail.clone(),
            },
            _ => FrontendRefusal::UpstreamEntry {
                symbol: symbol.into(),
                check: self.check,
                detail: self.detail.clone(),
            },
        }
    }
    pub(super) fn called_from(mut self) -> Self {
        if let Some(row) = &mut self.clean {
            row.role = clean_below_gate::CleanRole::Reaches;
        }
        self
    }
}
impl std::fmt::Display for Refusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{}] {}", self.check, self.detail)
    }
}
type Result<T> = std::result::Result<T, Refusal>;

/// Exact original and rebound identities, carried to the post-output-gate disclosure.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct Disclosure {
    owner: (u64, u64),
    content: [u8; 32],
    module: [u8; 32],
    rebound: [u8; 32],
}
impl Disclosure {
    pub(super) fn describe(&self) -> String {
        fn hex(bytes: &[u8]) -> String {
            bytes.iter().map(|b| format!("{b:02x}")).collect()
        }
        format!(
            "upstream entry {:016x}/{:016x}, content SHA256 {}, original module digest {}, rebound module SHA256 {}; \
             conservation re-derived; structural admission under P-TIR/D17/D39, no MIR seam differential",
            self.owner.0,
            self.owner.1,
            hex(&self.content),
            hex(&self.module),
            hex(&self.rebound),
        )
    }
}

/// Minted only after this file's actual-session admission sequence; no public constructor.
pub(super) struct Admitted<'tcx> {
    instance: ty::Instance<'tcx>,
}
impl<'tcx> Admitted<'tcx> {
    pub(super) fn instance(&self) -> ty::Instance<'tcx> {
        self.instance
    }
}
pub(super) struct Callee<'tcx> {
    id: FuncId,
    instance: ty::Instance<'tcx>,
}
impl<'tcx> Callee<'tcx> {
    pub(super) fn id(&self) -> FuncId {
        self.id
    }
    pub(super) fn instance(&self) -> ty::Instance<'tcx> {
        self.instance
    }
}

/// Immutable content plus its own-instance token; neither local admission type is fabricated.
pub(super) struct UpstreamBody<'tcx> {
    original: Module,
    evidence: rmeta_entry::Evidence,
    module: Module,
    callees: Vec<Callee<'tcx>>,
    fn_pointer_free: bool,
    admitted: Admitted<'tcx>,
    disclosure: Disclosure,
}
impl<'tcx> UpstreamBody<'tcx> {
    pub(super) fn original_module(&self) -> &Module { &self.original }
    pub(super) fn retained_evidence(&self) -> &rmeta_entry::Evidence { &self.evidence }
    pub(super) fn module(&self) -> &Module {
        &self.module
    }
    pub(super) fn callees(&self) -> &[Callee<'tcx>] {
        &self.callees
    }
    pub(super) fn fn_pointer_free(&self) -> bool {
        self.fn_pointer_free
    }
    pub(super) fn admitted(&self) -> &Admitted<'tcx> {
        &self.admitted
    }
    pub(super) fn disclosure(&self) -> Disclosure {
        self.disclosure
    }
}

fn decode_error(e: EntryDecodeError) -> Refusal {
    let check = match e {
        EntryDecodeError::EnvelopeDigest | EntryDecodeError::Digest => "digest",
        EntryDecodeError::OverflowMode { .. } | EntryDecodeError::OverflowByte(_) => "mode",
        EntryDecodeError::Schema(_)
        | EntryDecodeError::EvidenceSchema(_)
        | EntryDecodeError::TrustIrVersion { .. } => "schema",
        _ => "decode",
    };
    Refusal::new(check, e.to_string())
}

pub(super) fn check_target(module: &Module, expected: &trust_ir::TargetInfo) -> Result<()> {
    match &module.target_info {
        Some(actual) if actual == expected => Ok(()),
        actual => Err(Refusal::new(
            "target",
            format!("entry target {actual:?} differs from {expected:?}"),
        )),
    }
}

/// Exact table-free source-type spelling. An unrepresented type refuses; it never becomes Unit.
fn source_type(t: ty::Ty<'_>, depth: usize) -> Result<Ty> {
    if depth > 128 {
        return Err(Refusal::new("signature", "source signature nesting"));
    }
    let out = match t.kind() {
        ty::Bool => Ty::Bool,
        ty::Char => Ty::Char,
        ty::Int(ty::IntTy::I8) => Ty::I8,
        ty::Int(ty::IntTy::I16) => Ty::I16,
        ty::Int(ty::IntTy::I32) => Ty::I32,
        ty::Int(ty::IntTy::I64) => Ty::I64,
        ty::Int(ty::IntTy::I128) => Ty::I128,
        ty::Int(ty::IntTy::Isize) => Ty::Isize,
        ty::Uint(ty::UintTy::U8) => Ty::U8,
        ty::Uint(ty::UintTy::U16) => Ty::U16,
        ty::Uint(ty::UintTy::U32) => Ty::U32,
        ty::Uint(ty::UintTy::U64) => Ty::U64,
        ty::Uint(ty::UintTy::U128) => Ty::U128,
        ty::Uint(ty::UintTy::Usize) => Ty::Usize,
        ty::Float(ty::FloatTy::F16) => Ty::F16,
        ty::Float(ty::FloatTy::F32) => Ty::F32,
        ty::Float(ty::FloatTy::F64) => Ty::F64,
        ty::Never => Ty::Never,
        ty::Tuple(fields) if fields.is_empty() => Ty::Unit,
        ty::Tuple(fields) => {
            Ty::Tuple(fields.iter().map(|t| source_type(t, depth + 1)).collect::<Result<_>>()?)
        }
        ty::Ref(_, p, _) | ty::RawPtr(p, _)
            if matches!(
                p.kind(),
                ty::Bool | ty::Char | ty::Int(_) | ty::Uint(_) | ty::Float(_)
            ) =>
        {
            Ty::Ptr
        }
        ty::Ref(_, p, rustc_hir::Mutability::Not) if matches!(p.kind(), ty::Str) => {
            Ty::FatPtr(trust_ir::FatPtrKind::Str)
        }
        _ => {
            return Err(Refusal::new(
                "signature",
                format!("source type `{t}` requires a qualified type/table/ABI transport"),
            ));
        }
    };
    Ok(out)
}

fn check_signature<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
    module: &Module,
    id: FuncId,
) -> Result<()> {
    let raw = tcx.fn_sig(instance.def_id()).instantiate(tcx, instance.args);
    let env = ty::TypingEnv::fully_monomorphized();
    let normalized = tcx
        .try_normalize_erasing_regions(env, raw)
        .map_err(|_| Refusal::new("signature", "Rust signature normalization failed"))?;
    if normalized.bound_vars().iter().any(|v| !matches!(v, ty::BoundVariableKind::Region(_))) {
        return Err(Refusal::new("signature", "nonregion signature binder"));
    }
    let signature = tcx.instantiate_bound_regions_with_erased(normalized);
    let conv = match signature.abi() {
        ExternAbi::Rust => CallingConv::Rust,
        ExternAbi::C { unwind: false } => CallingConv::C,
        other => {
            return Err(Refusal::new(
                "abi",
                format!("unrepresented source calling convention {other}"),
            ));
        }
    };
    if signature.c_variadic() || signature.fn_sig_kind.splatted().is_some() {
        return Err(Refusal::new(
            "abi",
            "variadic or spread source signature needs a real adapter",
        ));
    }
    let expected = FuncTy {
        params: signature.inputs().iter().map(|t| source_type(*t, 0)).collect::<Result<_>>()?,
        // Both source producers and the codegen ABI spell `()` and `!` as zero results.
        returns: if signature.output().is_unit() || signature.output().is_never() {
            vec![]
        } else {
            vec![source_type(signature.output(), 0)?]
        },
        is_vararg: false,
        abi: None,
    };
    let body = module
        .function_by_id(id)
        .ok_or_else(|| Refusal::new("signature", "missing entry/declaration"))?;
    let actual = module
        .func_types
        .get(body.ty.as_usize())
        .ok_or_else(|| Refusal::new("signature", "missing FuncTy"))?;
    check_signature_data(actual, body.calling_conv, &expected, conv)?;
    // This independently checks the actual Rust attrs, convention, hidden args, unwind and pass modes.
    crate::validate_codegen_instance_abi_trust_ir(tcx, instance, actual.params.len())
        .map_err(|e| Refusal::new("abi", e))
}

fn check_signature_data(
    actual: &FuncTy,
    actual_conv: CallingConv,
    expected: &FuncTy,
    expected_conv: CallingConv,
) -> Result<()> {
    if actual != expected || actual_conv != expected_conv {
        return Err(Refusal::new(
            "signature",
            format!(
                "entry carries {actual:?}/{actual_conv:?}, actual Rust instance requires {expected:?}/{expected_conv:?}"
            ),
        ));
    }
    Ok(())
}

pub(super) fn require_strict(strict: bool) -> Result<()> {
    if strict {
        Ok(())
    } else {
        Err(Refusal::new(
            "strict",
            "D17/D39 admits upstream bodies only under the strict output gate",
        ))
    }
}

fn concrete_item<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
) -> Result<rustc_span::def_id::DefId> {
    let ty::InstanceKind::Item(def) = instance.def else {
        return Err(Refusal::new(
            "instance",
            "a synthesized instance requires a real source adapter",
        ));
    };
    if let Some(row) = clean_below_gate::source_origin_refusal(tcx, def) {
        return Err(Refusal { check: "clean", detail: row.why.clone(), clean: Some(row) });
    }
    if !matches!(tcx.def_kind(def), DefKind::Fn | DefKind::AssocFn)
        || instance.args.len() != tcx.generics_of(def).count()
        || instance.args.has_non_region_param()
        || instance.args.has_infer()
        || tcx.intrinsic(def).is_some()
        || tcx.instantiate_and_check_impossible_clauses((def, instance.args))
    {
        return Err(Refusal::new(
            "instance",
            "requires a concrete ordinary nonintrinsic Rust function",
        ));
    }
    Ok(def)
}

fn resolve_callee<'tcx>(tcx: TyCtxt<'tcx>, row: &EvidenceLedgerRow) -> Result<ty::Instance<'tcx>> {
    let [identity] = row.ids.as_slice() else {
        return Err(Refusal::new("callee", "callee identity is absent or ambiguous"));
    };
    let def = checked_definition(tcx, *identity)?;
    if !matches!(tcx.def_kind(def), DefKind::Fn | DefKind::AssocFn) {
        return Err(Refusal::new("callee", "retained callee identity is not an ordinary function"));
    }
    let target = if let Some(site) = &row.site {
        let recovered =
            trust_thir_lower::metadata_site::recover_with_definition(tcx, site, |key| {
                checked_definition(tcx, key).map_err(|_| {
                    trust_thir_lower::metadata_site::SiteError(
                        "legacy site stable identity differs from actual Rust metadata",
                    )
                })
            })
            .map_err(|e| Refusal::new("callee", e.to_string()))?;
        let target = recovered.instance();
        // The complete key must describe the actual resolved Item and all its
        // arguments, independently of the parser's returned argument vector.
        let canonical = trust_thir_lower::metadata_site::canonical_suffix(tcx, target)
            .map_err(|e| Refusal::new("callee", e.to_string()))?;
        if canonical != *site {
            return Err(Refusal::new(
                "callee",
                "actual Rust instance differs from the complete retained site",
            ));
        }
        target
    } else {
        if tcx.generics_of(def).requires_monomorphization(tcx) {
            return Err(Refusal::new(
                "callee",
                "generic callee has no complete retained concrete site",
            ));
        }
        let args = tcx.erase_and_anonymize_regions(ty::GenericArgs::identity_for_item(tcx, def));
        ty::Instance::try_resolve(tcx, ty::TypingEnv::fully_monomorphized(), def, args)
            .map_err(|_| Refusal::new("callee", "Rust instance resolution failed"))?
            .ok_or_else(|| Refusal::new("callee", "Rust instance is unresolved"))?
    };
    if concrete_item(tcx, target)? != def {
        return Err(Refusal::new(
            "callee",
            "retained stable identity differs from the resolved Item",
        ));
    }
    Ok(target)
}

/// The delegate only locates a candidate. Rustc's actual stable crate id and
/// DefPathHash independently establish its identity at this frozen boundary.
fn checked_definition(tcx: TyCtxt<'_>, wanted: (u64, u64)) -> Result<rustc_span::def_id::DefId> {
    let def = trust_thir_lower::template_key::rustc::definition(tcx, wanted)
        .map_err(|e| Refusal::new("callee", e.to_string()))?;
    let hash = tcx.def_path_hash(def);
    check_stable_identity(
        wanted,
        (hash.stable_crate_id().as_u64(), hash.local_hash().as_u64()),
        tcx.stable_crate_id(def.krate).as_u64(),
    )?;
    Ok(def)
}

fn check_stable_identity(
    wanted: (u64, u64),
    actual_hash: (u64, u64),
    actual_crate: u64,
) -> Result<()> {
    if wanted != actual_hash || wanted.0 != actual_crate {
        return Err(Refusal::new(
            "callee",
            "stable key differs from the actual Rust DefPathHash/crate",
        ));
    }
    Ok(())
}

/// One actual Rust crate-store input; no caller-supplied module, verdict, resolver or strict bit.
pub(super) fn admit<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
) -> Result<UpstreamBody<'tcx>> {
    require_strict(instance_assembly::session_gate_is_strict(tcx.sess))?;
    let def = concrete_item(tcx, instance)?;
    if def.is_local() || !tcx.should_codegen_locally(instance) {
        return Err(Refusal::new(
            "locality",
            "this upstream instance must be linked, not imported as a local body",
        ));
    }
    let header = tcx.trust_ir_crate_header(def.krate).ok_or_else(|| {
        Refusal::new("absent", "upstream crate was compiled without the Trust-IR producer")
    })?;
    if header.trust_ir_version != trust_ir::binary::VERSION
        || header.entry_schema != rmeta_entry::ENTRY_SCHEMA
    {
        return Err(Refusal::new("schema", "upstream crate producer wire/entry version mismatch"));
    }
    if let Some(reason) = &header.crate_refusal {
        return Err(Refusal::new("absent", reason.clone()));
    }
    let blob = tcx.trust_ir_entry(def).ok_or_else(|| {
        Refusal::new(
            "absent",
            header.unencoded_reason(def.index.as_u32()).unwrap_or("not in the producer encode set"),
        )
    })?;
    if tcx.generics_of(def).requires_monomorphization(tcx) {
        return Err(Refusal::new(
            "template",
            "level-S instances require sealed template admission (6.6); level-R cannot substitute an identity body",
        ));
    }
    let decoded = rmeta_entry::decode_entry_for_overflow(&blob.0, tcx.sess.overflow_checks())
        .map_err(decode_error)?;
    let hash = tcx.def_path_hash(def);
    let expected = EntryBinding {
        stable_crate_id: tcx.stable_crate_id(def.krate).as_u64(),
        local_hash: hash.local_hash().as_u64(),
    };
    if decoded.binding != expected {
        return Err(Refusal::new("binding", "entry names another stable Rust owner"));
    }
    let target = trust_ir::TargetInfo {
        triple: tcx.sess.target.llvm_target.to_string(),
        pointer_size: u32::from(tcx.sess.target.pointer_width / 8),
        endianness: match tcx.sess.target.endian {
            rustc_abi::Endian::Little => Endianness::Little,
            rustc_abi::Endian::Big => Endianness::Big,
        },
        abi: None,
        struct_passing: StructPassingPolicy::Unclassified,
    };
    check_target(&decoded.module, &target)?;
    let evidence = rmeta_entry::decode_evidence(&decoded.evidence).map_err(decode_error)?;
    let judgement =
        trust_thir_lower::effect_conservation::retained::judge(&decoded.module, &evidence)
            .map_err(|e| Refusal::new("effects", e.to_string()))?;
    if !judgement.tags().is_empty() {
        return Err(Refusal::new("effects", format!("{:?}", judgement.tags())));
    }
    check_signature(tcx, instance, &decoded.module, FuncId::new(0))?;
    let original = decoded.module.clone();
    let mut module = decoded.module;
    let mut callees = Vec::with_capacity(evidence.ledger.len());
    for (position, row) in evidence.ledger.iter().enumerate() {
        let id = FuncId::new(position as u32 + 1);
        if row.func_id != id.index() {
            return Err(Refusal::new("callee", "callee ledger is not dense and ordered"));
        }
        let target = resolve_callee(tcx, row).map_err(Refusal::called_from)?;
        check_signature(tcx, target, &module, id)?;
        module
            .function_by_id_mut(id)
            .ok_or_else(|| Refusal::new("callee", "callee declaration absent"))?
            .name = tcx.symbol_name(target).name.to_string();
        callees.push(Callee { id, instance: target });
    }
    module
        .function_by_id_mut(FuncId::new(0))
        .ok_or_else(|| Refusal::new("body", "FuncId0 body absent"))?
        .name = tcx.symbol_name(instance).name.to_string();
    trust_thir_lower::instance_admission::instance_module_is_self_contained(&module, callees.len())
        .map_err(|e| Refusal::new("module", e))?;
    let errors = trust_ir_build::validate_module(&module);
    if !errors.is_empty() {
        return Err(Refusal::new("module", format!("{errors:?}")));
    }
    let rebound = trust_thir_lower::effect_conservation::retained::judge(&module, &evidence)
        .map_err(|e| Refusal::new("effects", e.to_string()))?;
    if !rebound.tags().is_empty()
        || rebound.shape() != judgement.shape()
        || rebound.equivalences() != judgement.equivalences()
    {
        return Err(Refusal::new("effects", "symbol rebinding changed the retained judgement"));
    }
    let fn_pointer_free =
        trust_thir_lower::instance_admission::instance_body_is_fn_pointer_free(&module);
    let rebound_bytes = trust_ir::binary::serialize_module(&module)
        .map_err(|e| Refusal::new("module", format!("rebound module has no wire image: {e}")))?;
    let disclosure = Disclosure {
        owner: (expected.stable_crate_id, expected.local_hash),
        content: decoded.content_digest,
        module: decoded.digest,
        rebound: trust_ir::proof::ProofDigest::sha256_domain(
            "trust.rmeta.rebound-module.v1",
            &rebound_bytes,
        )
        .bytes,
    };
    Ok(UpstreamBody {
        original,
        evidence,
        module,
        callees,
        fn_pointer_free,
        admitted: Admitted { instance },
        disclosure,
    })
}

#[cfg(test)]
mod tests;
