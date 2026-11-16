//! Trust (PKG-C2d2 slice 1; design §5.5(a) and §6.6 of
//! `docs/design/2026-10-02-step2-inc6-trust-ir-in-metadata.md`; INC6.5-NO-AUTHORITY in
//! `docs/DECISION_QUEUE.md`): the template-instance equivalence TEST-ORACLE.
//!
//! DIAGNOSTIC ONLY. Nothing here is an output, admission, splice or proof input. The default-off
//! `-Ztrust-ir-template-instance-oracle` (driver-fenced to the D17 per-instance MIR seam
//! TEST-ORACLE lane) asks, for one local generic instance that D17 spliced and whose MIR seam
//! oracle agreed:
//!
//! 1. this crate's own canonical level-S row for the owner, the exact blob the metadata encoder
//!    writes (`trust_ir_local_entries`), read through the authenticated [`super::read`] against
//!    independently derived [`super::rustc::owner_bindings`];
//! 2. hole-free templates only (callee, type and const holes refuse, so no CTFE answer enters);
//! 3. construction with [`super::instantiate::construct_source_checked_with`] (S2 source custody,
//!    `concrete::instantiate`, `binding::bind` and `retained::judge`, FnAbi custody,
//!    `validate_module`, every body Ungated);
//! 4. a one-body, table-free, call-free constructed module;
//! 5. EXACT equality of trust-ir canonical text between a one-function projection of the
//!    constructed body and of the body D17 spliced into the codegen module.
//!
//! The projection re-interns only the function's own `FuncTy` and the paths its spans name (the
//! splice re-interns both the same way), and replaces exactly the link and identity header fields
//! in [`ERASED_FIELDS`] by fixed values. [`projection`] destructures `Function` with no `..`, so a
//! new trust-ir field fails to compile here until it is classified as compared or erased.
//!
//! The emitted side passed the splice preconditions (a table-free, function-pointer-free guest
//! of whitelisted instructions), so its body names no table row besides its signature and its
//! files. Exact text equality therefore makes the constructed body the subject the MIR seam
//! oracle already compared with raw built MIR at this instance: the two comparisons chain.
//!
//! [`compare`] returns no module, lowering, token or gate. A mismatch is `Err`, which the caller
//! makes a fatal session error. Each negative control alters only a private copy and can never
//! return `Ok`.

use rustc_hir::def::DefKind;
use rustc_middle::ty::{self, TyCtxt, TypeVisitableExt};
use rustc_span::def_id::DefId;
use trust_ir::proof::ProofDigest;
use trust_ir::{BodyGate, Constant, FuncAttrs, FuncId, Function, FunctionG, Inst, Linkage, Module};

use super::instantiate::{self, TemplateProvider};
use super::{AuthenticatedTemplate, Result as ReadResult, err};

/// The oracle's verdict on one instance. It holds no IR, token or gate.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OracleOutcome {
    /// The constructed instance's canonical text equals the emitted D17 body's. Grants nothing.
    Agreed { owner: String, envelope_sha256: [u8; 32], graph_digest: ProofDigest },
    /// The instance is outside the slice-1 comparator; a named reason, never agreement.
    Refused(String),
}
impl OracleOutcome {
    /// The diagnostic note for `symbol`. Text only.
    pub fn note(&self, symbol: &str) -> String {
        match self {
            Self::Agreed { owner, envelope_sha256, graph_digest } => format!(
                "template-instance TEST-ORACLE: `{symbol}`: agreed (template {owner}, envelope \
                 SHA256 {}, instance graph {}; chained to the per-instance MIR seam TEST-ORACLE; \
                 no authority)",
                hex(envelope_sha256),
                hex(&graph_digest.bytes)
            ),
            Self::Refused(reason) => {
                format!("template-instance TEST-ORACLE: `{symbol}`: refused({reason})")
            }
        }
    }
}
fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// The header fields the comparison replaces by fixed values: link identity (`id`, `name`,
/// `linkage`), producer claims (`attrs`, `summary`, `producer`) and the codegen license, which
/// the splice re-stamps. Every other `Function` field is compared.
pub(crate) const ERASED_FIELDS: [&str; 7] =
    ["id", "name", "linkage", "attrs", "summary", "producer", "body_gate"];

const PROJECTION_MODULE: &str = "template-instance-oracle";
const PROJECTION_SYMBOL: &str = "template_instance_oracle_subject";
/// `read`'s refusal for a payload whose content digest does not match.
const DIGEST_REFUSAL: &str = "template content digest";
/// magic (8) + schema (4) + trust-ir version (4) + content digest (32) + payload length (8).
const PAYLOAD_OFFSET: usize = 56;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Mutation {
    IntConstant,
    EnvelopeByte,
}
impl Mutation {
    fn requested(tcx: TyCtxt<'_>) -> Result<Option<Self>, String> {
        match tcx.sess.opts.unstable_opts.trust_test_template_oracle_mutation.as_deref() {
            None => Ok(None),
            Some("int-constant") => Ok(Some(Self::IntConstant)),
            Some("envelope-byte") => Ok(Some(Self::EnvelopeByte)),
            Some(other) => Err(format!("unknown template-instance TEST-ORACLE mutation `{other}`")),
        }
    }
    fn name(self) -> &'static str {
        match self {
            Self::IntConstant => "int-constant",
            Self::EnvelopeByte => "envelope-byte",
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
enum Judgement {
    Agree,
    Refused(String),
    Disagreed(String),
}

/// Compare one D17-emitted local generic instance body (`emitted.functions[func]`) with its
/// construction from this crate's own authenticated level-S template. `Err` is a mismatch or a
/// negative control (which never returns `Ok`); the caller must end the session on it.
pub fn compare<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
    emitted: &Module,
    func: FuncId,
) -> Result<OracleOutcome, String> {
    let mutation = Mutation::requested(tcx)?;
    let (judgement, agreed) = judge_instance(tcx, instance, emitted, func, mutation);
    settle(mutation, judgement, agreed)
}

fn settle(
    mutation: Option<Mutation>,
    judgement: Judgement,
    agreed: Option<(String, [u8; 32], ProofDigest)>,
) -> Result<OracleOutcome, String> {
    match (mutation, judgement) {
        (None, Judgement::Agree) => {
            let (owner, envelope_sha256, graph_digest) =
                agreed.ok_or("internal: agreement without its construction record")?;
            Ok(OracleOutcome::Agreed { owner, envelope_sha256, graph_digest })
        }
        (None, Judgement::Refused(reason)) => Ok(OracleOutcome::Refused(reason)),
        (None, Judgement::Disagreed(detail)) => Err(detail),
        (Some(_), Judgement::Agree) => Err("negative control unexpectedly agreed".to_string()),
        (Some(Mutation::IntConstant), Judgement::Disagreed(detail)) => {
            Err(format!("negative control int-constant: disagreed: {detail}"))
        }
        (Some(Mutation::EnvelopeByte), Judgement::Refused(reason))
            if reason.contains(DIGEST_REFUSAL) =>
        {
            Err(format!("negative control envelope-byte: refused: {reason}"))
        }
        (Some(mode), Judgement::Refused(reason)) => {
            Err(format!("negative control {}: unexpected refusal: {reason}", mode.name()))
        }
        (Some(mode), Judgement::Disagreed(detail)) => {
            Err(format!("negative control {}: unexpected disagreement: {detail}", mode.name()))
        }
    }
}

fn judge_instance<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
    emitted: &Module,
    func: FuncId,
    mutation: Option<Mutation>,
) -> (Judgement, Option<(String, [u8; 32], ProofDigest)>) {
    let refused = |reason: String| (Judgement::Refused(reason), None);
    let ty::InstanceKind::Item(def) = instance.def else {
        return refused("not an ordinary item instance".to_string());
    };
    if !def.is_local() || !matches!(tcx.def_kind(def), DefKind::Fn | DefKind::AssocFn) {
        return refused("not a local fn or associated-fn item".to_string());
    }
    if instance.args.iter().all(|arg| arg.as_region().is_some()) {
        return refused("not a generic instance".to_string());
    }
    if instance.args.has_non_region_param() || instance.args.has_non_region_infer() {
        return refused("instance arguments are not concrete".to_string());
    }
    let mut provider = LocalEntries { envelope_byte: mutation == Some(Mutation::EnvelopeByte) };
    let holes = match provider.load(tcx, def) {
        Ok(artifact) => artifact.template().header.holes.len(),
        Err(error) => return refused(format!("authenticated read: {error}")),
    };
    if holes != 0 {
        return refused(format!(
            "{holes} hole(s); the slice-1 comparator covers hole-free templates"
        ));
    }
    let constructed = match instantiate::construct_source_checked_with(tcx, instance, &mut provider)
    {
        Ok(constructed) => constructed,
        Err(error) => return refused(format!("construction: {error}")),
    };
    if constructed.callables().len() != 1 || constructed.callables()[0].instance() != instance {
        return refused(
            "outside the slice-1 comparator fragment: the construction is not exactly this \
             instance's one callable"
                .to_string(),
        );
    }
    if constructed.source_checks().map_or(0, <[_]>::len) != 1 {
        return refused(
            "outside the slice-1 comparator fragment: the construction has no single source check"
                .to_string(),
        );
    }
    let judgement = judge_modules(
        constructed.module(),
        constructed.entry(),
        emitted,
        func,
        mutation == Some(Mutation::IntConstant),
    );
    let owner = rustc_middle::ty::print::with_no_trimmed_paths!(tcx.def_path_str(def));
    (judgement, Some((owner, constructed.input_digest(), constructed.graph_digest())))
}

/// This crate's own level-S rows, exactly as the metadata encoder writes them. A provider for
/// the oracle only: it refuses every non-local owner.
struct LocalEntries {
    envelope_byte: bool,
}
impl<'tcx> TemplateProvider<'tcx> for LocalEntries {
    fn load(&mut self, tcx: TyCtxt<'tcx>, owner: DefId) -> ReadResult<AuthenticatedTemplate> {
        let local = owner
            .as_local()
            .ok_or_else(|| err("the TEST-ORACLE reads only this crate's own level-S rows"))?;
        let entries = tcx.trust_ir_local_entries(());
        if !entries.producer_ran {
            return Err(err("this crate's trust-ir producer did not run"));
        }
        if let Some(refusal) = &entries.crate_refusal {
            return Err(err(format!("this crate's trust-ir entries are refused: {refusal}")));
        }
        let index = local.local_def_index.as_u32();
        if !entries.templates.contains(&index) {
            return Err(err("no level-S row: the producer routed no template for the owner"));
        }
        let blob = match entries.entries.get(&index) {
            Some(Ok(blob)) => &blob.0,
            Some(Err(reason)) => return Err(err(format!("no level-S row: {reason}"))),
            None => return Err(err("no level-S row: the producer recorded no body for the owner")),
        };
        let expected = super::rustc::owner_bindings(tcx, owner)?;
        if self.envelope_byte {
            let tampered = flip_payload_byte(blob).map_err(err)?;
            return super::read(&tampered, &expected, tcx.sess.overflow_checks());
        }
        super::read(blob, &expected, tcx.sess.overflow_checks())
    }
}

/// The envelope-byte negative control: a private copy with its first payload byte flipped.
fn flip_payload_byte(blob: &[u8]) -> Result<Vec<u8>, String> {
    if blob.len() <= PAYLOAD_OFFSET {
        return Err("negative control envelope-byte: the blob has no payload byte".to_string());
    }
    let mut copy = blob.to_vec();
    copy[PAYLOAD_OFFSET] ^= 1;
    Ok(copy)
}

/// The pure comparator: the constructed module's fragment, both bodies' fragment, then exact
/// canonical text of each one-function projection.
fn judge_modules(
    constructed: &Module,
    entry: FuncId,
    emitted: &Module,
    func: FuncId,
    mutate_int_constant: bool,
) -> Judgement {
    let outside = |what: String| {
        Judgement::Refused(format!("outside the slice-1 comparator fragment: {what}"))
    };
    if let Err(what) = constructed_fragment(constructed) {
        return outside(what);
    }
    let Some(ours) = constructed.function_by_id(entry) else {
        return outside(format!("the constructed module has no FuncId({})", entry.index()));
    };
    let Some(theirs) = emitted.function_by_id(func) else {
        return outside(format!("the emitted module has no FuncId({})", func.index()));
    };
    let mut ours = ours.clone();
    if mutate_int_constant && !flip_first_int_constant(&mut ours) {
        return Judgement::Refused(
            "negative control int-constant: the constructed body has no integer constant"
                .to_string(),
        );
    }
    if let Err(what) = body_fragment(&ours) {
        return outside(format!("constructed body {what}"));
    }
    if let Err(what) = body_fragment(theirs) {
        return outside(format!("emitted body {what}"));
    }
    let text = |module: &Module, function: &Function, side: &str| {
        let projected =
            projection(module, function).map_err(|e| format!("{side} projection: {e}"))?;
        trust_ir::format::canonical_checked(&projected)
            .map_err(|e| format!("{side} projection has no lossless text: {e:?}"))
    };
    let left = match text(constructed, &ours, "constructed") {
        Ok(text) => text,
        Err(reason) => return Judgement::Refused(reason),
    };
    let right = match text(emitted, theirs, "emitted") {
        Ok(text) => text,
        Err(reason) => return Judgement::Refused(reason),
    };
    if left == right {
        Judgement::Agree
    } else {
        Judgement::Disagreed(first_difference(&left, &right))
    }
}

/// One body, table-free (only its signature row), call-free: what the slice-1 comparator covers.
fn constructed_fragment(module: &Module) -> Result<(), String> {
    if module.functions.len() != 1 {
        return Err(format!("the construction holds {} bodies", module.functions.len()));
    }
    let tables: [(&str, bool); 17] = [
        ("structs", module.structs.is_empty()),
        ("enums", module.enums.is_empty()),
        ("records", module.records.is_empty()),
        ("closure_types", module.closure_types.is_empty()),
        ("globals", module.globals.is_empty()),
        ("types", module.types.is_empty()),
        ("tuple_layouts", module.tuple_layouts.is_empty()),
        ("predicates", module.predicates.is_empty()),
        ("universes", module.universes.is_empty()),
        ("spec_modules", module.spec_modules.is_empty()),
        ("imports", module.imports.is_empty()),
        ("global_asm", module.global_asm.is_empty()),
        ("proof_obligations", module.proof_obligations.is_empty()),
        ("proof_certificates", module.proof_certificates.is_empty()),
        ("obligation_diagnostics", module.obligation_diagnostics.is_empty()),
        ("drop_glue", module.drop_glue.is_empty()),
        ("closure_layouts", module.closure_layouts.is_empty()),
    ];
    if let Some((table, _)) = tables.iter().find(|(_, empty)| !empty) {
        return Err(format!("the construction carries a `{table}` table"));
    }
    if module.completeness.is_some() {
        return Err("the construction carries a completeness claim".to_string());
    }
    Ok(())
}

fn body_fragment(function: &Function) -> Result<(), String> {
    if function.blocks.is_empty() {
        return Err("is a declaration".to_string());
    }
    for node in function.blocks.iter().flat_map(|block| &block.body) {
        match &node.inst {
            Inst::Call { .. } | Inst::Invoke { .. } | Inst::CallIndirect { .. } => {
                return Err("has a call".to_string());
            }
            Inst::GlobalAddr { .. } => return Err("names a global".to_string()),
            Inst::Const { value: Constant::FnDef(_), .. } => {
                return Err("names a function value".to_string());
            }
            _ => {}
        }
    }
    Ok(())
}

/// The int-constant negative control: the low bit of the first integer constant, in a private
/// clone of the constructed body.
fn flip_first_int_constant(function: &mut Function) -> bool {
    for node in function.blocks.iter_mut().flat_map(|block| &mut block.body) {
        if let Inst::Const { value: Constant::Int(value), .. } = &mut node.inst {
            *value ^= 1;
            return true;
        }
    }
    false
}

/// A one-function module: the body with [`ERASED_FIELDS`] fixed, its own signature as the only
/// `FuncTy`, the target, and the files its spans name (in first-use order). It must validate.
fn projection(module: &Module, function: &Function) -> Result<Module, String> {
    // EXHAUSTIVE: a new trust-ir `Function` field fails to compile until it is classified.
    let FunctionG {
        // Erased (ERASED_FIELDS): fixed values below.
        id: _,
        name: _,
        linkage: _,
        attrs: _,
        summary: _,
        producer: _,
        body_gate: _,
        // Compared.
        ty,
        entry,
        blocks,
        proofs,
        calling_conv,
        value_names,
        scopes,
        source_provenance,
        display_path,
        section,
        visibility,
        retained,
    } = function;
    let signature = module
        .func_types
        .get(ty.as_usize())
        .cloned()
        .ok_or_else(|| format!("the body names missing FuncTy {}", ty.as_usize()))?;
    let mut out = Module::new(PROJECTION_MODULE);
    out.target_info = module.target_info.clone();
    let ty = out.intern_func_type(signature).map_err(|e| e.to_string())?;
    let mut projected = FunctionG {
        id: FuncId::new(0),
        name: PROJECTION_SYMBOL.to_string(),
        linkage: Linkage::External,
        attrs: FuncAttrs::default(),
        summary: None,
        producer: None,
        body_gate: Some(BodyGate::Ungated),
        ty,
        entry: *entry,
        blocks: blocks.clone(),
        proofs: proofs.clone(),
        calling_conv: *calling_conv,
        value_names: value_names.clone(),
        scopes: scopes.clone(),
        source_provenance: source_provenance.clone(),
        display_path: display_path.clone(),
        section: section.clone(),
        visibility: *visibility,
        retained: *retained,
    };
    reintern_files(&mut projected, &module.files, &mut out.files)?;
    out.functions.push(projected);
    let errors = trust_ir_build::validate::validate_module(&out);
    if !errors.is_empty() {
        return Err(format!("the one-function projection does not validate: {errors:?}"));
    }
    Ok(out)
}

/// Re-intern every span's file (instruction spans and the scope tree, as the splice does) by its
/// path, in first-use order. A dangling file index refuses.
fn reintern_files(
    function: &mut Function,
    from: &[String],
    to: &mut Vec<String>,
) -> Result<(), String> {
    let mut remap = |file: &mut u32| -> Result<(), String> {
        let path = from
            .get(*file as usize)
            .ok_or_else(|| format!("a span names dangling file #{file}"))?;
        let index = match to.iter().position(|known| known == path) {
            Some(index) => index,
            None => {
                to.push(path.clone());
                to.len() - 1
            }
        };
        *file = u32::try_from(index).map_err(|_| "file table exceeds u32".to_string())?;
        Ok(())
    };
    for node in function.blocks.iter_mut().flat_map(|block| &mut block.body) {
        if let Some(span) = node.span.as_mut() {
            remap(&mut span.file)?;
        }
    }
    for scope in function.scopes.iter_mut().flatten() {
        if let Some(span) = scope.span.as_mut() {
            remap(&mut span.file)?;
        }
        if let Some(inlined) = scope.inlined_at.as_mut() {
            remap(&mut inlined.span.file)?;
        }
    }
    Ok(())
}

/// The first differing line of the two canonical texts, with one line of context each side, and
/// the header fields the projection fixed before comparing (so the reader knows a difference there
/// cannot be the cause).
fn first_difference(constructed: &str, emitted: &str) -> String {
    let left: Vec<&str> = constructed.lines().collect();
    let right: Vec<&str> = emitted.lines().collect();
    let at =
        left.iter().zip(&right).position(|(a, b)| a != b).unwrap_or(left.len().min(right.len()));
    let line =
        |lines: &[&str], i: usize| lines.get(i).copied().unwrap_or("<end of text>").to_string();
    format!(
        "canonical text differs at line {} (constructed {} lines, emitted {} lines): constructed \
         `{}` / emitted `{}`; previous line `{}`; not compared: {}",
        at + 1,
        left.len(),
        right.len(),
        line(&left, at),
        line(&right, at),
        if at == 0 { "<none>".to_string() } else { line(&left, at - 1) },
        ERASED_FIELDS.join(", "),
    )
}

#[cfg(test)]
mod tests {
    use trust_ir::proof::ProofAnnotation;
    use trust_ir::{
        BinOp, Block, BlockId, CallingConv, FuncTy, InstrNode, SourceSpan, Ty, ValueId,
    };

    use super::*;

    fn v(id: u32) -> ValueId {
        ValueId::new(id)
    }

    /// `fn(x: u64) -> u64 { x ^ 0x55 }`, one body, one signature, one file.
    fn module(name: &str, files: &[&str]) -> Module {
        let mut m = Module::new("synthetic");
        m.files = files.iter().map(|f| f.to_string()).collect();
        let ty = m
            .intern_func_type(FuncTy {
                params: vec![Ty::U64],
                returns: vec![Ty::U64],
                is_vararg: false,
                abi: None,
            })
            .unwrap();
        let span = SourceSpan { file: (files.len() - 1) as u32, line: 3, col: 5 };
        let mut b = Block::new(BlockId::new(0)).with_param(v(0), Ty::U64);
        b.body.push(
            InstrNode::new(Inst::Const { ty: Ty::U64, value: Constant::Int(0x55) })
                .with_result(v(1))
                .with_span(span),
        );
        b.body.push(
            InstrNode::new(Inst::BinOp { op: BinOp::Xor, ty: Ty::U64, lhs: v(0), rhs: v(1) })
                .with_result(v(2)),
        );
        b.body.push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
        let mut f = Function::new(FuncId::new(0), name, ty, BlockId::new(0));
        f.calling_conv = CallingConv::Rust;
        f.body_gate = Some(BodyGate::Ungated);
        f.blocks = vec![b];
        m.try_add_function(f).unwrap();
        assert!(trust_ir_build::validate::validate_module(&m).is_empty());
        m
    }

    fn judge(constructed: &Module, emitted: &Module) -> Judgement {
        judge_modules(constructed, FuncId::new(0), emitted, FuncId::new(0), false)
    }

    fn disagreed(j: &Judgement) -> bool {
        matches!(j, Judgement::Disagreed(_))
    }

    #[test]
    fn identical_inputs_agree_and_the_file_index_is_reinterned_by_path() {
        let a = module("a", &["src/lib.rs"]);
        assert_eq!(judge(&a, &a), Judgement::Agree);
        // The emitted module's file table is the crate's: the same path at another index.
        let b = module("a", &["other.rs", "more.rs", "src/lib.rs"]);
        assert_eq!(judge(&a, &b), Judgement::Agree);
        // A different path is a real difference.
        let c = module("a", &["src/other.rs"]);
        assert!(disagreed(&judge(&a, &c)));
    }

    #[test]
    fn each_erased_header_field_may_differ() {
        let a = module("a", &["src/lib.rs"]);
        let mut b = module("_ZN3sym17h0123456789abcdefE", &["src/lib.rs"]);
        let f = &mut b.functions[0];
        f.linkage = Linkage::Internal;
        f.attrs = FuncAttrs { cold: true, ..FuncAttrs::default() };
        f.producer = Some(trust_ir::Producer::TRust);
        f.body_gate = Some(BodyGate::Gated { authority: "lane".to_string(), evidence: None });
        assert_eq!(judge(&a, &b), Judgement::Agree);
        assert_eq!(ERASED_FIELDS.len(), 7);
    }

    #[test]
    fn each_compared_part_mismatches() {
        let a = module("a", &["src/lib.rs"]);
        let mutations: [(&str, fn(&mut Module)); 7] = [
            ("instruction constant", |m| {
                m.functions[0].blocks[0].body[0].inst =
                    Inst::Const { ty: Ty::U64, value: Constant::Int(0x54) }
            }),
            ("FuncTy param", |m| {
                m.func_types[0].params.push(Ty::U8);
                m.functions[0].blocks[0].params.push((v(7), Ty::U8));
            }),
            ("FuncTy return", |m| {
                m.func_types[0].returns.push(Ty::U64);
                m.functions[0].blocks[0].body[2].inst = Inst::Return { values: vec![v(2), v(2)] };
            }),
            ("calling_conv", |m| m.functions[0].calling_conv = CallingConv::C),
            ("terminator", |m| {
                m.functions[0].blocks[0].body[2].inst = Inst::Return { values: vec![v(0)] }
            }),
            ("span line", |m| {
                m.functions[0].blocks[0].body[0].span =
                    Some(SourceSpan { file: 0, line: 4, col: 5 })
            }),
            ("display path", |m| m.functions[0].display_path = Some("x::y".to_string())),
        ];
        for (part, mutate) in mutations {
            let mut b = a.clone();
            mutate(&mut b);
            assert!(disagreed(&judge(&a, &b)), "{part}: {:?}", judge(&a, &b));
            assert!(disagreed(&judge(&b, &a)), "{part} (reversed)");
        }
        // Proof annotations and the entry block are compared; whichever of the projection's
        // validation or the text catches them, they never agree.
        let mut b = a.clone();
        b.functions[0].proofs.push(ProofAnnotation::NoOverflow);
        assert_ne!(judge(&a, &b), Judgement::Agree);
        let mut b = a.clone();
        b.functions[0].entry = BlockId::new(1);
        assert_ne!(judge(&a, &b), Judgement::Agree);
    }

    #[test]
    fn table_call_and_multi_body_inputs_refuse() {
        let a = module("a", &["src/lib.rs"]);
        let mut tabled = a.clone();
        tabled.types.push(Ty::U8);
        let refused = |j: Judgement, needle: &str| match j {
            Judgement::Refused(reason) => assert!(reason.contains(needle), "{reason}"),
            other => panic!("expected a refusal naming `{needle}`, got {other:?}"),
        };
        refused(judge(&tabled, &a), "`types` table");
        let mut called = a.clone();
        called.functions[0].blocks[0].body.insert(
            0,
            InstrNode::new(Inst::Call { callee: FuncId::new(0), args: vec![v(0)] })
                .with_result(v(9)),
        );
        refused(judge(&called, &a), "constructed body has a call");
        refused(judge(&a, &called), "emitted body has a call");
        let mut two = a.clone();
        let mut second = two.functions[0].clone();
        second.id = FuncId::new(1);
        second.name = "b".to_string();
        two.functions.push(second);
        refused(judge(&two, &a), "2 bodies");
        refused(judge_modules(&a, FuncId::new(0), &a, FuncId::new(7), false), "no FuncId(7)");
    }

    #[test]
    fn the_int_constant_control_disagrees_and_needs_a_constant() {
        let a = module("a", &["src/lib.rs"]);
        let j = judge_modules(&a, FuncId::new(0), &a, FuncId::new(0), true);
        assert!(disagreed(&j), "{j:?}");
        let mut no_constant = a.clone();
        no_constant.functions[0].blocks[0].body =
            vec![InstrNode::new(Inst::Return { values: vec![v(0)] })];
        assert!(matches!(
            judge_modules(&no_constant, FuncId::new(0), &no_constant, FuncId::new(0), true),
            Judgement::Refused(reason) if reason.contains("no integer constant")
        ));
    }

    #[test]
    fn the_envelope_byte_control_refuses_at_the_content_digest() {
        let (bindings, template, evidence) = super::super::tests::fixture();
        let blob = super::super::frame(&bindings, &template, true, &evidence).unwrap();
        assert!(super::super::read(&blob, &bindings, true).is_ok());
        let tampered = flip_payload_byte(&blob).unwrap();
        assert_eq!(super::super::read(&tampered, &bindings, true).unwrap_err().0, DIGEST_REFUSAL);
        assert!(flip_payload_byte(&blob[..PAYLOAD_OFFSET]).is_err());
    }

    #[test]
    fn a_negative_control_never_returns_ok() {
        let digest = ProofDigest::sha256_domain("t", b"x");
        let agreed = || Some(("o".to_string(), [0; 32], digest));
        assert!(settle(None, Judgement::Agree, agreed()).is_ok());
        assert_eq!(
            settle(None, Judgement::Refused("r".into()), None),
            Ok(OracleOutcome::Refused("r".into()))
        );
        assert_eq!(settle(None, Judgement::Disagreed("d".into()), None), Err("d".into()));
        for mode in [Mutation::IntConstant, Mutation::EnvelopeByte] {
            for judgement in [
                Judgement::Agree,
                Judgement::Refused("r".into()),
                Judgement::Refused(format!("authenticated read: {DIGEST_REFUSAL}")),
                Judgement::Disagreed("d".into()),
            ] {
                let expected = match (mode, &judgement) {
                    (Mutation::IntConstant, Judgement::Disagreed(_)) => true,
                    (Mutation::EnvelopeByte, Judgement::Refused(r)) => r.contains(DIGEST_REFUSAL),
                    _ => false,
                };
                let error = settle(Some(mode), judgement, agreed()).unwrap_err();
                let word = if mode == Mutation::IntConstant { "disagreed" } else { "refused" };
                assert_eq!(
                    error.starts_with(&format!("negative control {}: {word}: ", mode.name())),
                    expected,
                    "{error}"
                );
            }
        }
    }
}
