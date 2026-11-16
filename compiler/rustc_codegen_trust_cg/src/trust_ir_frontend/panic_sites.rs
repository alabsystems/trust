//! Trust (PKG-CP, R-8 item P): failed checks panic as Rust does, on the compiler lane
//! (`-Ztrust-cg-f1-backend=compiler`).
//!
//! The producer emits every runtime check as a siteless `Inst::Assert` that names its kind
//! (overflow, division, remainder, shift, bounds; trust-ir v52) and carries its source span.
//! A siteless check has no faithful lowering: the only one trust-cg has is a bare trap, so the
//! bridge's F1 boundary refuses it (`ImplicitPanicUnfaithful`). This pass runs on the codegen
//! module M_cg after it is built and before it is compiled, and does two things to it:
//!
//! 1. **Folds a check whose condition is constant true.** The condition is evaluated over the
//!    function's own SSA definitions (`Const`, `ICmp` of two known integers, `Copy`, and the
//!    boolean `And`/`Or`/`Xor` with short-circuit on a known operand); anything else is unknown
//!    and is never folded. A folded check can never fail, so deleting it changes no behaviour.
//!    It is folded HERE, on M_cg, and not where trust-ir is built: the producer's module is what
//!    every oracle compares (the flip's assert parity against rustc's built MIR, the seam and
//!    interpretation differentials), and it keeps every check, so assert parity holds by
//!    construction; the call-event gate reads that unmodified producer body as its spec, where
//!    a constant-true guard is `true`.
//! 2. **Sites every other check of an admitted kind** ([`admitted`]): `site = Some(PanicSite {
//!    entry, location: Global(record) })`, where `entry` is a bodyless declaration under
//!    rustc's symbol for the kind's `core` panic entry (`panic_const_add_overflow`,
//!    `panic_bounds_check`, ...) and `record` is the `core::panic::Location` rustc's
//!    const-eval builds for the check's span (`TyCtxt::span_as_caller_location`), imaged as an
//!    Internal, immutable, non-thread-local global under rustc's `alloc_<hash>` name, whose
//!    file-name pointer is a `SymbolAddr` to a second such global holding the NUL-terminated
//!    file name (`trust_cg_lower::global_image::type_flat_image` gives both their canonical
//!    storage type: `[u8; n]`, and a `repr(packed(1))` struct of `ptr` and `[u8; n]` fields).
//!    trust-cg lowers a sited check to `brif cond, cont, fail; fail: call entry(operands..,
//!    &record); trap` (trust-ir `SPEC_RATIFICATIONS` §19.1 rule 7), which is what LLVM emits for
//!    the same MIR `Assert` at `-Cpanic=abort`.
//!
//! A check this pass cannot site faithfully is LEFT siteless, and its function is refused here
//! by name ([`super::FrontendRefusal::UnfaithfulPanic`]); the bridge boundary refuses it too.
//! That covers: a kind not yet [`admitted`] (its subject has not been shown to print LLVM's
//! stderr and exit status), `Unspecified`, a check with no span, a body that must report its
//! CALLER's location (`#[track_caller]`) or whose rustc instance is unknown, and anything the
//! rustc half could not resolve exactly. An `AssertInvoke` is never touched (the bridge
//! refuses it). A function with one refused check is not modified at all.
//!
//! [`check_postcondition`] re-derives, from the module before and after, that the pass did
//! exactly that and nothing else; a violation refuses the module.
//!
//! The rustc half ([`rustc_half`]) resolves entries and location records; this half is PURE
//! (no `TyCtxt`), so every rule is a unit test (`panic_sites/tests.rs`).
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::{BTreeMap, BTreeSet};

use trust_cg_bridge::global_image::type_flat_image;
use trust_ir::ty::FuncTy;
use trust_ir::value::{BlockId, FuncId, FuncTyId, GlobalId, SourceSpan, ValueId};
use trust_ir::{
    AssertKind, AssertOverflowOp, BinOp, CallingConv, Constant, Function, Global, ICmpOp, Inst, Linkage,
    Module, PanicLocation, PanicSite, Producer, Ty, Visibility,
};

use super::FrontendRefusal;

pub(crate) mod rustc_half;

#[cfg(test)]
mod tests;

// ===========================================================================
// WHICH CHECKS ARE SITED
// ===========================================================================

/// The check kinds whose failure this pass routes to rustc's panic entry. A kind is admitted
/// only once its subject in `tests/run-make/trust-cg-f1-faithful-panics` prints LLVM's stderr
/// and exit status; every other kind keeps its refusal.
pub(crate) fn admitted(kind: &AssertKind) -> bool {
    match kind {
        AssertKind::Overflow(op) => matches!(
            op,
            AssertOverflowOp::Add
                | AssertOverflowOp::Sub
                | AssertOverflowOp::Mul
                | AssertOverflowOp::Neg
                | AssertOverflowOp::Div
                | AssertOverflowOp::Rem
                | AssertOverflowOp::Shl
                | AssertOverflowOp::Shr
        ),
        AssertKind::DivByZero | AssertKind::RemByZero | AssertKind::BoundsCheck { .. } => true,
        // No producer emits these (rustc inserts them in MIR passes the producer does not
        // model), and no subject shows them faithful.
        AssertKind::MisalignedPtr { .. } | AssertKind::NullPtr => false,
        // Names no Rust panic (§19 rule 3).
        AssertKind::Unspecified => false,
    }
}

// ===========================================================================
// CONSTANT TRUTH
// ===========================================================================

/// A value the evaluator knows.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Known {
    Bool(bool),
    /// An integer of `bits` bits, its two's-complement image masked to them.
    Int { bits: u32, image: u128 },
}

fn mask(bits: u32) -> u128 {
    if bits >= 128 { u128::MAX } else { (1u128 << bits) - 1 }
}

fn signed(bits: u32, image: u128) -> i128 {
    if bits == 0 || bits >= 128 {
        return image as i128;
    }
    let shift = 128 - bits;
    ((image << shift) as i128) >> shift
}

/// The width of an integer type, `None` for anything else (`Char` included).
fn int_bits(ty: &Ty, pointer_bits: u32) -> Option<u32> {
    if !ty.is_integer() {
        return None;
    }
    ty.bit_width_with(pointer_bits).filter(|bits| (1..=128).contains(bits))
}

/// Each value's defining instruction in `function` (a block parameter has none).
fn definitions(function: &Function) -> BTreeMap<ValueId, &Inst> {
    let mut defs = BTreeMap::new();
    for block in &function.blocks {
        for node in &block.body {
            if let [result] = node.results.as_slice() {
                defs.insert(*result, &node.inst);
            }
        }
    }
    defs
}

/// What the evaluator knows about `value`, or `None`.
fn known(
    defs: &BTreeMap<ValueId, &Inst>,
    value: ValueId,
    pointer_bits: u32,
    depth: u32,
) -> Option<Known> {
    if depth == 0 {
        return None;
    }
    let go = |v: ValueId| known(defs, v, pointer_bits, depth - 1);
    match defs.get(&value)? {
        Inst::Const { ty: Ty::Bool, value: Constant::Bool(b) } => Some(Known::Bool(*b)),
        Inst::Const { ty, value } => {
            let bits = int_bits(ty, pointer_bits)?;
            let image = match value {
                Constant::Int(v) => *v as u128,
                Constant::U128(v) => *v,
                _ => return None,
            };
            Some(Known::Int { bits, image: image & mask(bits) })
        }
        Inst::Copy { operand, .. } => go(*operand),
        Inst::ICmp { op, ty, lhs, rhs } => {
            let bits = int_bits(ty, pointer_bits)?;
            let (Known::Int { bits: lb, image: l }, Known::Int { bits: rb, image: r }) =
                (go(*lhs)?, go(*rhs)?)
            else {
                return None;
            };
            if lb != bits || rb != bits {
                return None;
            }
            let (sl, sr) = (signed(bits, l), signed(bits, r));
            Some(Known::Bool(match op {
                ICmpOp::Eq => l == r,
                ICmpOp::Ne => l != r,
                ICmpOp::Ult => l < r,
                ICmpOp::Ule => l <= r,
                ICmpOp::Ugt => l > r,
                ICmpOp::Uge => l >= r,
                ICmpOp::Slt => sl < sr,
                ICmpOp::Sle => sl <= sr,
                ICmpOp::Sgt => sl > sr,
                ICmpOp::Sge => sl >= sr,
            }))
        }
        Inst::BinOp { op: op @ (BinOp::And | BinOp::Or | BinOp::Xor), ty: Ty::Bool, lhs, rhs } => {
            let (l, r) = (go(*lhs), go(*rhs));
            let as_bool = |k: Option<Known>| match k {
                Some(Known::Bool(b)) => Some(b),
                _ => None,
            };
            let (l, r) = (as_bool(l), as_bool(r));
            match op {
                BinOp::And => match (l, r) {
                    (Some(false), _) | (_, Some(false)) => Some(Known::Bool(false)),
                    (Some(true), Some(true)) => Some(Known::Bool(true)),
                    _ => None,
                },
                BinOp::Or => match (l, r) {
                    (Some(true), _) | (_, Some(true)) => Some(Known::Bool(true)),
                    (Some(false), Some(false)) => Some(Known::Bool(false)),
                    _ => None,
                },
                _ => Some(Known::Bool(l? ^ r?)),
            }
        }
        _ => None,
    }
}

/// How deep the evaluator follows definitions. The producer's checks are at most a few
/// definitions deep; a deeper condition is simply not folded.
const EVAL_DEPTH: u32 = 16;

/// `true` exactly when `cond` is a constant `true` over `function`'s own definitions.
#[cfg(test)]
pub(crate) fn constant_true(function: &Function, cond: ValueId, pointer_bits: u32) -> bool {
    true_over(&definitions(function), cond, pointer_bits)
}

/// `true` exactly when `cond` is a constant `true` over the definitions `defs`.
fn true_over(defs: &BTreeMap<ValueId, &Inst>, cond: ValueId, pointer_bits: u32) -> bool {
    known(defs, cond, pointer_bits, EVAL_DEPTH) == Some(Known::Bool(true))
}

// ===========================================================================
// WHAT THE RUSTC HALF RESOLVES
// ===========================================================================

/// A flat data image as rustc's const-eval laid it out: one `Constant::Int` per byte and one
/// `Constant::SymbolAddr` per pointer, under rustc's name for the allocation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DataImage {
    /// rustc's `alloc_<hash>` name for the allocation.
    pub(crate) symbol: String,
    /// The allocation's alignment, in bytes.
    pub(crate) align: u32,
    /// The image (see [`trust_cg_bridge::global_image::type_flat_image`]).
    pub(crate) elements: Vec<Constant>,
}

/// A `core::panic::Location` record and the file name it points to.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct LocationRecord {
    /// The record; its pointers name only `file`.
    pub(crate) record: DataImage,
    /// The NUL-terminated file name.
    pub(crate) file: DataImage,
}

/// What the rustc half answers.
pub(crate) trait Resolver {
    /// rustc's link symbol for `kind`'s panic entry, after checking the entry takes the kind's
    /// operands as `usize` and then the caller location, and returns `!`.
    fn entry(&mut self, kind: &AssertKind) -> Result<String, String>;
    /// rustc's location record for a check stamped at `span` of the module's file table.
    fn location(&mut self, files: &[String], span: SourceSpan) -> Result<LocationRecord, String>;
    /// `Ok` when the body under `symbol` reports a failed check at its own source location:
    /// a known rustc instance that is not `#[track_caller]`.
    fn reports_own_location(&mut self, symbol: &str) -> Result<(), String>;
    /// `Ok` when rustc's own MIR for the body under `symbol` holds, for each `(kind, record)`,
    /// a distinct MIR `Assert` that calls the same lang item and reports the same location
    /// record (LLVM's backend lowers exactly those). This is the oracle that ties each site to
    /// what rustc emits for the same check, independently of the producer's span stamp.
    fn matches_rustc_mir(
        &mut self,
        symbol: &str,
        checks: &[(AssertKind, LocationRecord)],
    ) -> Result<(), String>;
}

/// `true` when `symbol` names the lang item `name` as one identifier of its path: v0
/// (`..._4core9panicking18panic_bounds_check`) and legacy (`..._4core9panicking18panic_bounds_
/// check17h...E`) manglings both write an identifier as its decimal length, then its bytes. A
/// length is a maximal run of digits, so one that continues a longer run does not count.
pub(crate) fn names_lang_item(symbol: &str, name: &str) -> bool {
    let segment = format!("{}{name}", name.len());
    symbol
        .match_indices(&segment)
        .any(|(at, _)| !symbol[..at].ends_with(|c: char| c.is_ascii_digit()))
}

// ===========================================================================
// THE PASS
// ===========================================================================

/// What [`site`] did.
#[derive(Debug, Default)]
pub(crate) struct SitingReport {
    /// Checks deleted because their condition is constant true.
    pub(crate) folded: usize,
    /// Checks given a panic site.
    pub(crate) sited: usize,
    /// Functions refused because a check in them could not be sited.
    pub(crate) refusals: Vec<FrontendRefusal>,
}

/// One planned site: the entry symbol and the location record.
struct PlannedSite {
    entry: String,
    location: LocationRecord,
}

/// What [`site`] decided for one function.
enum Plan {
    /// No change.
    Untouched,
    /// Delete the checks at `fold`; site the checks at `sites`.
    Rewrite { fold: BTreeSet<(usize, usize)>, sites: BTreeMap<(usize, usize), PlannedSite> },
}

/// The signature a panic entry for `kind` has: one `usize` per kind operand, then the
/// location pointer, returning nothing (§19.1 rule 1).
pub(crate) fn entry_signature(kind: &AssertKind) -> FuncTy {
    let mut params = vec![Ty::Usize; kind.operand_count()];
    params.push(Ty::Ptr);
    FuncTy { params, returns: Vec::new(), is_vararg: false, abi: None }
}

fn unfaithful(symbol: &str, detail: String) -> FrontendRefusal {
    FrontendRefusal::UnfaithfulPanic { symbol: symbol.to_string(), detail }
}

/// Plan one function, or refuse it by name.
fn plan_function(
    m: &Module,
    function: &Function,
    pointer_bits: u32,
    resolver: &mut dyn Resolver,
) -> Result<Plan, String> {
    let defs = definitions(function);
    let mut fold = BTreeSet::new();
    let mut needs = Vec::new();
    for (b, block) in function.blocks.iter().enumerate() {
        for (n, node) in block.body.iter().enumerate() {
            if let Inst::Assert { cond, kind, site: None } = &node.inst {
                if true_over(&defs, *cond, pointer_bits) {
                    fold.insert((b, n));
                } else {
                    needs.push((b, n, *kind, node.span));
                }
            }
        }
    }
    if fold.is_empty() && needs.is_empty() {
        return Ok(Plan::Untouched);
    }
    let mut sites = BTreeMap::new();
    if !needs.is_empty() {
        resolver.reports_own_location(&function.name).map_err(|why| {
            format!("its checks cannot report a location of their own: {why}")
        })?;
    }
    for (b, n, kind, span) in needs {
        let at = format!("bb{}.{n}", function.blocks[b].id.index());
        if !admitted(&kind) {
            return Err(format!(
                "the check at {at} is of kind `{}`, which this lane does not route to a Rust \
                 panic entry (its subject has not been shown to panic as LLVM's build does)",
                kind.keyword()
            ));
        }
        let Some(span) = span else {
            return Err(format!("the check at {at} carries no source span to report"));
        };
        let entry = resolver
            .entry(&kind)
            .map_err(|why| format!("the check at {at} has no panic entry: {why}"))?;
        let location = resolver
            .location(&m.files, span)
            .map_err(|why| format!("the check at {at} has no location record: {why}"))?;
        if !kind.rust_panic_lang_item().is_some_and(|name| names_lang_item(&entry, name)) {
            return Err(format!(
                "the check at {at}: rustc's entry `{entry}` does not name the `{}` lang item",
                kind.keyword()
            ));
        }
        sites.insert((b, n), PlannedSite { entry, location });
    }
    if !sites.is_empty() {
        let checks: Vec<(AssertKind, LocationRecord)> = sites
            .iter()
            .map(|((b, n), planned)| {
                let Inst::Assert { kind, .. } = &function.blocks[*b].body[*n].inst else {
                    unreachable!("a planned site is an `Assert`")
                };
                (*kind, planned.location.clone())
            })
            .collect();
        resolver.matches_rustc_mir(&function.name, &checks).map_err(|why| {
            format!("its checks do not match rustc's own MIR `Assert`s: {why}")
        })?;
    }
    Ok(Plan::Rewrite { fold, sites })
}

/// Fold and site the checks of every body of `m_cg`, or refuse the functions that cannot be.
/// `m_cg` changes only as [`check_postcondition`] describes; on a module-level failure (an
/// entry or global name already taken by something else) nothing is changed and every
/// planned function is refused.
pub(crate) fn site(m_cg: &mut Module, resolver: &mut dyn Resolver) -> SitingReport {
    let mut report = SitingReport::default();
    let pointer_bits = match m_cg.target_info.as_ref().map(|t| t.pointer_size) {
        Some(bytes) if bytes > 0 => bytes * 8,
        _ => 64,
    };
    let mut plans = Vec::with_capacity(m_cg.functions.len());
    for function in &m_cg.functions {
        if function.is_declaration() {
            plans.push(Plan::Untouched);
            continue;
        }
        match plan_function(m_cg, function, pointer_bits, resolver) {
            Ok(plan) => plans.push(plan),
            Err(detail) => {
                report.refusals.push(unfaithful(&function.name, detail));
                plans.push(Plan::Untouched);
            }
        }
    }
    let before = m_cg.clone();
    match apply(m_cg, plans, u64::from(pointer_bits / 8)) {
        Ok((folded, sited)) => {
            report.folded = folded;
            report.sited = sited;
        }
        Err((symbols, why)) => {
            *m_cg = before;
            for symbol in symbols {
                report.refusals.push(unfaithful(&symbol, why.clone()));
            }
            return report;
        }
    }
    if let Err(why) = check_postcondition(&before, m_cg, pointer_bits) {
        *m_cg = before;
        report.folded = 0;
        report.sited = 0;
        report.refusals.push(FrontendRefusal::CodegenModule {
            symbol: m_cg.name.clone(),
            detail: format!("the panic-site pass broke its postcondition: {why}"),
        });
    }
    report
}

/// Intern the entry `symbol` for `kind`: an existing bodyless declaration signed exactly
/// [`entry_signature`] under Rust's calling convention is reused; any other
/// function of that name refuses. The rustc resolver confirms this convention.
fn intern_entry(m: &mut Module, symbol: &str, kind: &AssertKind) -> Result<FuncId, String> {
    let signature = entry_signature(kind);
    if let Some(existing) = m.functions.iter().find(|f| f.name == symbol) {
        let same = existing.is_declaration()
            && existing.linkage == Linkage::External
            && existing.calling_conv == CallingConv::Rust
            && m.func_type(existing.ty) == Some(&signature);
        return if same {
            Ok(existing.id)
        } else {
            Err(format!(
                "the panic entry `{symbol}` is already a function of M_cg with another shape"
            ))
        };
    }
    let ty = match m.func_types.iter().position(|t| *t == signature) {
        Some(index) => FuncTyId::new(index as u32),
        None => {
            m.func_types.push(signature);
            FuncTyId::new((m.func_types.len() - 1) as u32)
        }
    };
    let id = FuncId::new(m.functions.len() as u32);
    let mut declaration = Function::new(id, symbol, ty, BlockId::new(0));
    declaration.calling_conv = CallingConv::Rust;
    declaration.linkage = Linkage::External;
    declaration.producer = Some(Producer::TRust);
    m.functions.push(declaration);
    Ok(id)
}

/// Intern one data image as an Internal, immutable, non-thread-local global: an existing
/// global of that name is reused only when it is exactly that global.
fn intern_image(m: &mut Module, image: &DataImage, pointer_bytes: u64) -> Result<GlobalId, String> {
    // `type_flat_image` reads and grows only the type and struct tables.
    let mut scratch = Module::new(m.name.clone());
    scratch.types = m.types.clone();
    scratch.structs = m.structs.clone();
    let typed =
        type_flat_image(&mut scratch, &image.symbol, image.elements.clone(), pointer_bytes)?;
    let wanted = |g: &Global| {
        g.name == image.symbol
            && !g.mutable
            && g.tls.is_none()
            && g.linkage == Linkage::Internal
            && g.align == Some(image.align)
            && g.section.is_none()
            && g.initializer.as_ref().is_some_and(|init| {
                // Trust: flattened elements alone erase each relocation's byte extent.
                trust_cg_bridge::global_image::flat_image_matches(
                    m,
                    &g.ty,
                    init,
                    &image.elements,
                    pointer_bytes,
                ) == Some(true)
            })
    };
    if let Some(index) = m.globals.iter().position(|g| g.name == image.symbol) {
        return if wanted(&m.globals[index]) {
            Ok(GlobalId::new(index as u32))
        } else {
            Err(format!("the global name `{}` is already taken in M_cg", image.symbol))
        };
    }
    if m.functions.iter().any(|f| f.name == image.symbol) {
        return Err(format!("the global name `{}` is a function of M_cg", image.symbol));
    }
    m.types = scratch.types;
    m.structs = scratch.structs;
    m.globals.push(Global {
        section: None,
        visibility: Visibility::Default,
        retained: false,
        name: image.symbol.clone(),
        ty: typed.ty,
        mutable: false,
        initializer: Some(typed.initializer),
        linkage: Linkage::Internal,
        tls: None,
        align: Some(image.align),
    });
    Ok(GlobalId::new((m.globals.len() - 1) as u32))
}

/// Apply the plans. `Err` names every function that had a plan, and why.
#[allow(clippy::type_complexity)]
fn apply(
    m: &mut Module,
    plans: Vec<Plan>,
    pointer_bytes: u64,
) -> Result<(usize, usize), (Vec<String>, String)> {
    let planned: Vec<String> = m
        .functions
        .iter()
        .zip(&plans)
        .filter(|(_, p)| matches!(p, Plan::Rewrite { .. }))
        .map(|(f, _)| f.name.clone())
        .collect();
    let fail = |why: String| (planned.clone(), why);
    let (mut folded, mut sited) = (0, 0);
    let mut entries: BTreeMap<String, FuncId> = BTreeMap::new();
    let mut records: BTreeMap<String, GlobalId> = BTreeMap::new();
    for (index, plan) in plans.into_iter().enumerate() {
        let Plan::Rewrite { fold, sites } = plan else { continue };
        let mut resolved = BTreeMap::new();
        for (at, planned_site) in &sites {
            let kind = match &m.functions[index].blocks[at.0].body[at.1].inst {
                Inst::Assert { kind, .. } => *kind,
                _ => return Err(fail("a planned site is not an `Assert`".into())),
            };
            let entry = match entries.get(&planned_site.entry) {
                Some(id) => *id,
                None => {
                    let id = intern_entry(m, &planned_site.entry, &kind).map_err(&fail)?;
                    entries.insert(planned_site.entry.clone(), id);
                    id
                }
            };
            if m.function_by_id(entry).and_then(|f| m.func_type(f.ty))
                != Some(&entry_signature(&kind))
            {
                return Err(fail(format!(
                    "the panic entry `{}` serves two kinds of different shape",
                    planned_site.entry
                )));
            }
            let record = match records.get(&planned_site.location.record.symbol) {
                Some(id) => *id,
                None => {
                    intern_image(m, &planned_site.location.file, pointer_bytes).map_err(&fail)?;
                    let id = intern_image(m, &planned_site.location.record, pointer_bytes)
                        .map_err(&fail)?;
                    records.insert(planned_site.location.record.symbol.clone(), id);
                    id
                }
            };
            resolved.insert(*at, PanicSite { entry, location: PanicLocation::Global(record) });
        }
        let function = &mut m.functions[index];
        let function_id = function.id;
        let block_ids: Vec<BlockId> = function.blocks.iter().map(|block| block.id).collect();
        for (b, block) in function.blocks.iter_mut().enumerate() {
            let mut n = 0;
            block.body.retain(|_| {
                let keep = !fold.contains(&(b, n));
                n += 1;
                keep
            });
        }
        folded += fold.len();
        // An obligation names its check by `(block, inst_index)`. Re-key each one sited in this
        // function by the fold; one sited ON a folded check loses its site (`None`: no position,
        // which every consumer must treat as unbindable, never as a wildcard). Its row, id and
        // status are kept, so it stays as pending as it was.
        for obligation in &mut m.proof_obligations {
            let Some(at) = &mut obligation.site else { continue };
            if at.function != function_id {
                continue;
            }
            let Some(b) = block_ids.iter().position(|id| *id == at.block) else { continue };
            let n = at.inst_index as usize;
            if fold.contains(&(b, n)) {
                obligation.site = None;
            } else {
                let shift = fold.iter().filter(|(fb, fnode)| *fb == b && *fnode < n).count();
                at.inst_index -= u32::try_from(shift).map_err(|_| fail("an index overflowed".into()))?;
            }
        }
        let function = &mut m.functions[index];
        // Re-key the sites by their position after the fold.
        for ((b, n), new_site) in resolved {
            let shift = fold.iter().filter(|(fb, fnode)| *fb == b && *fnode < n).count();
            match &mut function.blocks[b].body[n - shift].inst {
                Inst::Assert { site: site @ None, .. } => *site = Some(new_site),
                _ => return Err(fail("a planned site moved off its `Assert`".into())),
            }
            sited += 1;
        }
    }
    Ok((folded, sited))
}

// ===========================================================================
// THE POSTCONDITION
// ===========================================================================

/// What [`site`] may have done to `before` to make `after`, re-derived without trusting the
/// plan:
///
/// * the tables only grew at their ends (types, structs, function types, globals, functions);
///   every pre-existing entry of each is unchanged, the file table included;
/// * every new function is a bodyless External declaration signed as some kind's entry
///   ([`entry_signature`]); every new global is Internal, immutable, non-thread-local,
///   initialized and in no explicit section;
/// * every pre-existing function keeps every field but its blocks, and each block keeps its
///   header and its nodes in order except that (a) a removed node is a siteless `Assert` whose
///   condition is constant true over the ORIGINAL body, and (b) a siteless `Assert` of an
///   [`admitted`] kind may gain a site whose entry is a bodyless External declaration (new or
///   pre-existing) signed for that kind and named for its lang item ([`names_lang_item`]), and
///   whose location is an immutable Internal initialized global (new or pre-existing);
/// * every obligation keeps its row; its site moves with its node, and one on a removed node
///   becomes `None`;
/// * nothing else in the module changed, and `trust_ir_build::validate_module` accepts it.
pub(crate) fn check_postcondition(
    before: &Module,
    after: &Module,
    pointer_bits: u32,
) -> Result<(), String> {
    fn grown<T: PartialEq>(what: &str, a: &[T], b: &[T]) -> Result<(), String> {
        if b.len() < a.len() || b[..a.len()] != *a {
            return Err(format!("the {what} table changed instead of growing at its end"));
        }
        Ok(())
    }
    grown("type", &before.types, &after.types)?;
    grown("struct", &before.structs, &after.structs)?;
    grown("function-type", &before.func_types, &after.func_types)?;
    grown("global", &before.globals, &after.globals)?;
    if before.files != after.files {
        return Err("the file table changed".into());
    }
    if after.functions.len() < before.functions.len() {
        return Err("functions were removed".into());
    }
    for g in &after.globals[before.globals.len()..] {
        if g.mutable
            || g.tls.is_some()
            || g.linkage != Linkage::Internal
            || g.initializer.is_none()
            || g.section.is_some()
        {
            return Err(format!("the new global `{}` is not an immutable Internal image", g.name));
        }
    }
    let new_functions = &after.functions[before.functions.len()..];
    for (offset, f) in new_functions.iter().enumerate() {
        if f.id.as_usize() != before.functions.len() + offset
            || !f.is_declaration()
            || f.linkage != Linkage::External
            || f.calling_conv != CallingConv::Rust
        {
            return Err(format!("the new function `{}` is not an External Rust declaration", f.name));
        }
        let signed = after.func_type(f.ty).is_some_and(|t| {
            t.returns.is_empty()
                && !t.is_vararg
                && t.abi.is_none()
                && t.params.last() == Some(&Ty::Ptr)
                && t.params[..t.params.len() - 1].iter().all(|p| *p == Ty::Usize)
        });
        if !signed {
            return Err(format!("the new function `{}` is not signed as a panic entry", f.name));
        }
    }
    // Where each pre-existing node went: `Some(new index)` in the same block, or `None` (folded).
    let mut moved: BTreeMap<(FuncId, BlockId, u32), Option<u32>> = BTreeMap::new();
    for (old, new) in before.functions.iter().zip(&after.functions) {
        // Every field but the bodies is unchanged.
        let (mut old_head, mut new_head) = (old.clone(), new.clone());
        old_head.blocks.clear();
        new_head.blocks.clear();
        if old_head != new_head || old.blocks.len() != new.blocks.len() {
            return Err(format!("the function `{}` changed outside its checks", old.name));
        }
        let defs = definitions(old);
        for (ob, nb) in old.blocks.iter().zip(&new.blocks) {
            if ob.id != nb.id || ob.params != nb.params {
                return Err(format!("a block of `{}` changed its header", old.name));
            }
            let mut next = nb.body.iter();
            let mut pending = next.next();
            // `kept` counts the new nodes matched so far: the new index of the next kept node.
            let mut kept: u32 = 0;
            for (n, node) in ob.body.iter().enumerate() {
                let old_at = (old.id, ob.id, n as u32);
                let Some(candidate) = pending else {
                    match &node.inst {
                        Inst::Assert { cond, site: None, .. }
                            if true_over(&defs, *cond, pointer_bits) =>
                        {
                            moved.insert(old_at, None);
                            continue;
                        }
                        _ => {
                            return Err(format!("a node of `{}` was removed", old.name));
                        }
                    }
                };
                if candidate == node {
                    moved.insert(old_at, Some(kept));
                    kept += 1;
                    pending = next.next();
                    continue;
                }
                match (&node.inst, &candidate.inst) {
                    (
                        Inst::Assert { cond, kind, site: None },
                        Inst::Assert { cond: c2, kind: k2, site: Some(new_site) },
                    ) if cond == c2 && kind == k2 && admitted(kind) && {
                        let mut stripped = candidate.clone();
                        if let Inst::Assert { site, .. } = &mut stripped.inst {
                            *site = None;
                        }
                        stripped == *node
                    } =>
                    {
                        // The entry is a bodyless External declaration (new, or one M_cg
                        // already had), signed for the kind and named for its lang item.
                        let entry_ok = after.function_by_id(new_site.entry).is_some_and(|f| {
                            f.is_declaration()
                                && f.linkage == Linkage::External
                                && f.calling_conv == CallingConv::Rust
                                && after.func_type(f.ty) == Some(&entry_signature(kind))
                                && kind
                                    .rust_panic_lang_item()
                                    .is_some_and(|name| names_lang_item(&f.name, name))
                        });
                        // The record is an immutable Internal image (new, or one M_cg
                        // already had: the interner reuses an identical global).
                        let location_ok = matches!(new_site.location,
                            PanicLocation::Global(g) if after.globals.get(g.as_usize()).is_some_and(|g| {
                                !g.mutable
                                    && g.tls.is_none()
                                    && g.linkage == Linkage::Internal
                                    && g.initializer.is_some()
                                    && g.section.is_none()
                            }));
                        if !entry_ok || !location_ok {
                            return Err(format!(
                                "a site in `{}` names an entry or location the pass did not add",
                                old.name
                            ));
                        }
                        moved.insert(old_at, Some(kept));
                        kept += 1;
                        pending = next.next();
                    }
                    (Inst::Assert { cond, site: None, .. }, _)
                        if true_over(&defs, *cond, pointer_bits) =>
                    {
                        moved.insert(old_at, None);
                    }
                    _ => return Err(format!("a node of `{}` changed", old.name)),
                }
            }
            if pending.is_some() {
                return Err(format!("a node was added to `{}`", old.name));
            }
        }
    }
    // The obligation table keeps every row, id and field; only a site moves with its node, and
    // a site on a folded check becomes `None`.
    if before.proof_obligations.len() != after.proof_obligations.len() {
        return Err("the obligation table changed size".into());
    }
    for (old, new) in before.proof_obligations.iter().zip(&after.proof_obligations) {
        let expected = match old.site {
            None => None,
            Some(at) => match moved.get(&(at.function, at.block, at.inst_index)) {
                // A site outside every node the walk saw (another function, or a stale index)
                // is untouched.
                None => Some(at),
                Some(None) => None,
                Some(Some(index)) => Some(trust_ir::ObligationSite { inst_index: *index, ..at }),
            },
        };
        let mut restored = new.clone();
        if restored.site != expected {
            return Err(format!("obligation #{:?} was re-sited to a node it is not about", old.id));
        }
        restored.site = old.site;
        if restored != *old {
            return Err(format!("obligation #{:?} changed beyond its site", old.id));
        }
    }
    // Every other part of the module is exactly as it was.
    let mut rest = after.clone();
    rest.types.truncate(before.types.len());
    rest.structs.truncate(before.structs.len());
    rest.func_types.truncate(before.func_types.len());
    rest.globals.truncate(before.globals.len());
    rest.functions = before.functions.clone();
    rest.proof_obligations = before.proof_obligations.clone();
    if rest != *before {
        return Err("a part of the module outside its tables, bodies and obligation sites changed".into());
    }
    let errors = trust_ir_build::validate_module(after);
    if let Some(first) = errors.first() {
        return Err(format!(
            "the sited module fails `validate_module` ({} error(s)); first: {first}",
            errors.len()
        ));
    }
    Ok(())
}
