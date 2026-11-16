//! Trust (step 2 increment 4c, 2026-10-02): THE DROP-GLUE ORACLE — rustc's own drop shim, read
//! from its MIR, as a TEST ORACLE for the synthesized glue (`drop_glue.rs`). R-2: MIR is an
//! oracle, never a production input; this reads it and feeds nothing.
//!
//! Design: `docs/design/2026-09-29-step2-inc4-drops.md` §4.4 and §7.3 ("for each glue instance in
//! the corpus, the synthesized glue against `instance_mir(Shim(DropGlue(T)))`: same `Drop::drop`
//! call, same child drops in the same order, same dealloc call, same switch arms"). Owner ruling
//! D18 OD-2: synthesized glue splices under D17's rule — structural checks plus THIS test-oracle
//! differential, with no per-instance MIR seam differential.
//!
//! # What it computes
//!
//! Two independent comparisons, per glue instance:
//!
//! 1. **Structural** ([`shim_events`], [`compare_events`]). rustc's drop shim
//!    (`build_drop_shim` + `DropShimElaborator`) is walked along its NORMAL path (cleanup blocks
//!    skipped) in execution order, and every effect is named as a [`GlueEvent`]: a call of
//!    `<T as Drop>::drop` (by the resolved instance's symbol), a `Drop` terminator of a field
//!    place of `*_1` (by its field path — `Downcast` / `Field` projections — and the symbol of the
//!    child's own glue), the array shim's call of its slice glue, a slice shim's element loop.
//!    The producer's plan (`drop_glue::plan_events`) is compared with it: a MISS is an event the
//!    shim performs that the plan lacks, an EXTRA one the plan has that the shim does not, and
//!    the ORDER is compared per variant trace (the destructor, then that variant's children in
//!    order). Anything in the shim the event model cannot name is an `Unmodelled` event, which
//!    can only be a miss.
//! 2. **Executed** ([`execute_glue`]). The synthesized body (`drop_glue::synthesize_glue`, with
//!    every callee a bodyless declaration) is RUN by trust-ir's reference interpreter, once per
//!    inhabited variant, on a buffer holding the tag rustc's own const-eval writes for that
//!    variant (`tcx.tag_for_variant`; for a niche's untagged variant a value outside the niche
//!    range). A host model records each call it makes and the address it passes. The recorded
//!    calls must EQUAL the shim's events for that variant, each child at the byte offset rustc's
//!    `layout_of` gives its field path. This executes the trust-ir decode and switch, which the
//!    MIR comparison cannot see (MIR's `Discriminant` hides the encoding).
//!
//! Both read rustc's layout for offsets (the one shared source: `layout_of` is rustc's ground
//! truth for where a field lives); the structure comes from the shim's MIR and the tag encoding
//! from `tag_for_variant`, neither of which the plan reads.
//!
//! # Where it runs
//!
//! Channel C of the instance-flip probe (`instance_probe.rs`, `glue=` column) runs it over every
//! drop-glue item the collector lists; `tests/run-make/trust-cg-f1-drop-glue` runs channel C over
//! a corpus of local-closed types and requires every row to agree. It runs in no production
//! lane.
//!
//! # Freeze
//!
//! It computes an oracle verdict, so under the manifest's rule it is FROZEN at landing,
//! SAMPLE-MORE-OR-REFUSE-MORE (`scripts/frozen-files.txt`): a change may compare more or refuse
//! more, never report agreement it did not measure.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com> | Copyright 2026 | License: MIT OR Apache-2.0

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Mutex;

use rustc_abi::{TagEncoding, Variants};
use rustc_middle::mir::{self, ProjectionElem, TerminatorKind};
use rustc_middle::ty::{self, TyCtxt};
use trust_ir::{
    BlockId, Constant, FatPtrKind, FuncId, FuncTy, Function, HostCalls, HostState, Inst, InstrNode,
    InterpretResult, InterpretValue, InterpretValueKind, Interpreter, Module, Ty, ValueId,
};

use crate::drop_glue::{self, GluePlan, GlueShape};

/// One step of a field path below the dropped place.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PathElem {
    Variant(u32),
    Field(u32),
}

/// One effect of a drop-glue body, as both sides name it.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum GlueEvent {
    /// `<T as Drop>::drop(&mut *p)`, by the resolved instance's symbol.
    Destructor { callee: String },
    /// A needs-drop child at `path`, dropped through the glue named `glue`.
    Child { path: Vec<PathElem>, glue: String },
    /// An array's shim: the slice glue `glue` called on `(p, len)`.
    SliceDelegate { glue: String, len: u64 },
    /// A slice's shim: each element dropped through `glue`, in ascending index order.
    ElementLoop { glue: String },
    /// Something in the shim the event model does not name. Only ever a miss.
    Unmodelled { what: String },
}

impl GlueEvent {
    fn variant(&self) -> Option<u32> {
        match self {
            GlueEvent::Child { path, .. } => match path.first() {
                Some(PathElem::Variant(v)) => Some(*v),
                _ => None,
            },
            _ => None,
        }
    }
}

/// rustc's drop shim for `glue` as events, in execution order along the normal path.
pub fn shim_events<'tcx>(
    tcx: TyCtxt<'tcx>,
    glue: ty::Instance<'tcx>,
) -> Result<Vec<GlueEvent>, String> {
    let ty::InstanceKind::Shim(ty::ShimKind::DropGlue(_, Some(dropped))) = glue.def else {
        return Err(format!("{:?} is not a drop-glue instance with a type", glue.def));
    };
    let env = ty::TypingEnv::fully_monomorphized();
    let body = glue.instantiate_mir_and_normalize_erasing_regions(
        tcx,
        env,
        ty::EarlyBinder::bind(tcx, tcx.instance_mir(glue.def).clone()),
    );
    let drop_trait =
        tcx.require_lang_item(rustc_attr_ir::lang_items::LangItem::Drop, rustc_span::DUMMY_SP);
    let drop_fn = tcx.associated_item_def_ids(drop_trait).first().copied();
    let blocks = &body.basic_blocks;
    let normal_successors = |bb: mir::BasicBlock| -> Vec<mir::BasicBlock> {
        blocks[bb].terminator().successors().filter(|s| !blocks[*s].is_cleanup).collect()
    };
    // Blocks on a cycle of the normal path (a slice's element loop).
    let reaches = |from: mir::BasicBlock, to: mir::BasicBlock| -> bool {
        let mut seen = BTreeSet::new();
        let mut stack = vec![from];
        while let Some(b) = stack.pop() {
            if b == to {
                return true;
            }
            if seen.insert(b) {
                stack.extend(normal_successors(b));
            }
        }
        false
    };
    let on_cycle = |bb: mir::BasicBlock| normal_successors(bb).into_iter().any(|s| reaches(s, bb));
    let sym = |i: ty::Instance<'tcx>| drop_glue::glue_symbol(tcx, i);
    let dropee = mir::Local::from_u32(1);
    let mut events = Vec::new();
    let mut seen = BTreeSet::new();
    let mut stack = vec![mir::START_BLOCK];
    while let Some(bb) = stack.pop() {
        if blocks[bb].is_cleanup || !seen.insert(bb) {
            continue;
        }
        let terminator = blocks[bb].terminator();
        match &terminator.kind {
            TerminatorKind::Drop { place, .. } => {
                let pty = place.ty(&body, tcx).ty;
                let child = sym(ty::Instance::resolve_drop_glue(tcx, pty));
                let projection = place.projection.as_slice();
                if place.local == dropee && projection.first() == Some(&ProjectionElem::Deref) {
                    let mut path = Vec::new();
                    let mut ok = projection.len() > 1;
                    for elem in &projection[1..] {
                        match elem {
                            ProjectionElem::Field(f, _) => path.push(PathElem::Field(f.as_u32())),
                            ProjectionElem::Downcast(_, v) => {
                                path.push(PathElem::Variant(v.as_u32()))
                            }
                            _ => ok = false,
                        }
                    }
                    events.push(if ok {
                        GlueEvent::Child { path, glue: child }
                    } else {
                        GlueEvent::Unmodelled { what: format!("drop of `{place:?}`") }
                    });
                } else if matches!(projection, [ProjectionElem::Deref]) && on_cycle(bb) {
                    let ev = GlueEvent::ElementLoop { glue: child };
                    if !events.contains(&ev) {
                        events.push(ev);
                    }
                } else {
                    events.push(GlueEvent::Unmodelled { what: format!("drop of `{place:?}`") });
                }
            }
            TerminatorKind::Call { func, .. } => {
                let resolved = func.const_fn_def().and_then(|(def_id, args)| {
                    ty::Instance::try_resolve(tcx, env, def_id, args)
                        .ok()
                        .flatten()
                        .map(|i| (def_id, i))
                });
                match resolved {
                    Some((def_id, instance)) if Some(def_id) == drop_fn => {
                        events.push(GlueEvent::Destructor { callee: sym(instance) });
                    }
                    Some((_, instance))
                        if drop_glue::glue_instance_ty(instance).is_some_and(|t| t.is_slice()) =>
                    {
                        let len = match dropped.kind() {
                            ty::Array(_, len) => len.try_to_target_usize(tcx),
                            _ => None,
                        };
                        events.push(match len {
                            Some(len) => GlueEvent::SliceDelegate { glue: sym(instance), len },
                            None => GlueEvent::Unmodelled {
                                what: format!("a slice-glue call from the glue of `{dropped}`"),
                            },
                        });
                    }
                    Some((_, instance)) => {
                        events.push(GlueEvent::Unmodelled {
                            what: format!("call of `{}`", sym(instance)),
                        });
                    }
                    None => {
                        events.push(GlueEvent::Unmodelled { what: format!("call of `{func:?}`") })
                    }
                }
            }
            TerminatorKind::Goto { .. }
            | TerminatorKind::SwitchInt { .. }
            | TerminatorKind::Return
            | TerminatorKind::Unreachable => {}
            other => events.push(GlueEvent::Unmodelled { what: format!("{other:?}") }),
        }
        let mut next = normal_successors(bb);
        next.reverse();
        stack.extend(next);
    }
    Ok(events)
}

/// The structural verdict of [`compare_events`].
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct GlueComparison {
    /// In rustc's shim, not in the plan.
    pub misses: Vec<GlueEvent>,
    /// In the plan, not in rustc's shim.
    pub extras: Vec<GlueEvent>,
    /// Every per-variant trace has the same events in the same order.
    pub order_agrees: bool,
}

impl GlueComparison {
    pub fn agrees(&self) -> bool {
        self.misses.is_empty() && self.extras.is_empty() && self.order_agrees
    }
}

/// The per-variant traces of an event list: for each variant some child is under, every event
/// NOT under a variant (the destructor, a struct's fields) plus that variant's children, in
/// order; one trace keyed `None` when no event is under a variant. PURE.
pub fn traces(events: &[GlueEvent]) -> BTreeMap<Option<u32>, Vec<GlueEvent>> {
    let variants: BTreeSet<u32> = events.iter().filter_map(GlueEvent::variant).collect();
    let mut out = BTreeMap::new();
    if variants.is_empty() {
        out.insert(None, events.to_vec());
        return out;
    }
    for v in variants {
        let trace =
            events.iter().filter(|e| e.variant().is_none_or(|ev| ev == v)).cloned().collect();
        out.insert(Some(v), trace);
    }
    out
}

/// THE STRUCTURAL COMPARISON: rustc's shim events (`oracle`) against the producer's plan events
/// (`producer`). PURE.
pub fn compare_events(oracle: &[GlueEvent], producer: &[GlueEvent]) -> GlueComparison {
    let mut remaining: Vec<GlueEvent> = producer.to_vec();
    let mut misses = Vec::new();
    for e in oracle {
        match remaining.iter().position(|p| p == e) {
            Some(i) => {
                remaining.remove(i);
            }
            None => misses.push(e.clone()),
        }
    }
    let order_agrees = traces(oracle) == traces(producer);
    GlueComparison { misses, extras: remaining, order_agrees }
}

/// One recorded call: the callee's symbol, the pointer argument as `(allocation, offset)`, and a
/// fat pointer's metadata.
type RecordedCall = (String, Option<(u64, u64)>, Option<u128>);

/// The host model: every callee of the glue under test is a bodyless declaration; each call is
/// recorded, and returns nothing.
#[derive(Default)]
struct Recorder {
    calls: Mutex<Vec<RecordedCall>>,
}

fn pointer_of(value: &InterpretValue) -> Option<(u64, u64)> {
    match &value.kind {
        InterpretValueKind::Ptr(p) => Some((p.allocation, p.offset)),
        _ => None,
    }
}

impl HostCalls for Recorder {
    fn call(
        &self,
        callee: &Function,
        _sig: &FuncTy,
        args: &[InterpretValue],
        _host: &mut HostState,
    ) -> Option<InterpretResult<Vec<InterpretValue>>> {
        let (ptr, metadata) = match args {
            [arg] => match &arg.kind {
                InterpretValueKind::Ptr(_) => (pointer_of(arg), None),
                InterpretValueKind::FatPtr { data, metadata } => (
                    pointer_of(data),
                    match &metadata.kind {
                        InterpretValueKind::Int(int) => Some(int.raw),
                        _ => None,
                    },
                ),
                _ => (None, None),
            },
            _ => (None, None),
        };
        let mut calls = self.calls.lock().ok()?;
        calls.push((callee.name.clone(), ptr, metadata));
        Some(Ok(Vec::new()))
    }
}

/// The byte offset of a field path below the dropped value, from rustc's layout.
fn path_offset<'tcx>(
    tcx: TyCtxt<'tcx>,
    layout: ty::layout::TyAndLayout<'tcx>,
    path: &[PathElem],
) -> Result<u64, String> {
    let cx = ty::layout::LayoutCx::new(tcx, ty::TypingEnv::fully_monomorphized());
    match path {
        [PathElem::Field(f)] => {
            let f = *f as usize;
            if f >= layout.fields.count() {
                return Err(format!("field {f} is out of the layout's range"));
            }
            Ok(layout.fields.offset(f).bytes())
        }
        [PathElem::Variant(v), PathElem::Field(f)] => {
            let vl = layout.for_variant(&cx, rustc_abi::VariantIdx::from_u32(*v));
            let f = *f as usize;
            if f >= vl.fields.count() {
                return Err(format!("field {f} of variant {v} is out of the layout's range"));
            }
            Ok(vl.fields.offset(f).bytes())
        }
        other => Err(format!("an event path the executor does not place: {other:?}")),
    }
}

/// The scratch module's target: a 64-bit little-endian target in the reference interpreter's
/// canonical scalar table (the executor reads integers and pointers only; byte offsets come
/// from rustc's layout of the real target).
pub fn oracle_target() -> trust_ir::TargetInfo {
    trust_ir::TargetInfo {
        triple: "aarch64-apple-darwin".to_string(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    }
}

/// How many elements a slice glue is executed on.
pub const ELEMENTS: u64 = 3;

/// One interpreter run of a synthesized glue body: a buffer of `size` bytes aligned to `align`,
/// with `tag = (offset, bits, value)` stored into it, passed to the glue as a thin pointer, or as
/// a fat slice pointer of `elements` elements.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GlueRun {
    pub size: u64,
    pub align: u64,
    pub tag: Option<(u64, u32, u128)>,
    pub elements: Option<u64>,
}

/// One call the executed glue made: the callee's name, the byte offset of its pointer argument
/// into the run's buffer, and a fat pointer's metadata.
pub type ExecutedCall = (String, u64, Option<u128>);

/// EXECUTE a synthesized glue body (PURE: no `TyCtxt`). `shape` names its callees by symbol; each
/// becomes a bodyless declaration whose calls a host model records. The glue is synthesized by
/// `drop_glue::synthesize_glue` exactly as the lane synthesizes it, then run by the reference
/// interpreter from a driver that builds the buffer of `run`. Returns the calls in order.
pub fn run_synthesized(
    glue_name: &str,
    shape: &GlueShape<String>,
    run: &GlueRun,
) -> Result<Vec<ExecutedCall>, String> {
    let mut module = Module::new("trust-drop-glue-oracle");
    module.target_info = Some(oracle_target());
    // A fat slice pointer over an `I8` row: the executor never indexes through it.
    // The table doors refuse instead of panicking (trust-ir D1b); a refusal is the oracle's.
    let table = |refusal: trust_ir::IdSpaceExhausted| refusal.to_string();
    let elem_row = module.add_type(Ty::I8).map_err(table)?;
    let fat = Ty::FatPtr(FatPtrKind::Slice(elem_row));
    let ptr_sig = module
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![],
            is_vararg: false,
            abi: None,
        })
        .map_err(table)?;
    let fat_sig = module
        .add_func_type(FuncTy {
            params: vec![fat.clone()],
            returns: vec![],
            is_vararg: false,
            abi: None,
        })
        .map_err(table)?;
    let unit_sig = module
        .add_func_type(FuncTy { params: vec![], returns: vec![], is_vararg: false, abi: None })
        .map_err(table)?;
    let mut ids: BTreeMap<String, FuncId> = BTreeMap::new();
    for callee in shape.callees() {
        if ids.contains_key(callee) {
            continue;
        }
        let id = FuncId::new(module.functions.len() as u32);
        let sig = if shape.passes_fat_pointer() { fat_sig } else { ptr_sig };
        let mut decl = Function::new(id, callee.clone(), sig, BlockId::new(0));
        decl.linkage = trust_ir::Linkage::External;
        module.try_add_function(decl).map_err(|refusal| refusal.to_string())?;
        ids.insert(callee.clone(), id);
    }
    let shape = shape.try_map(|name| {
        ids.get(name).copied().ok_or_else(|| format!("no declaration for `{name}`"))
    })?;
    let glue_id = FuncId::new(module.functions.len() as u32);
    let glue_sig =
        module.add_func_type(drop_glue::glue_signature(&shape, Some(&fat))?).map_err(table)?;
    module
        .try_add_function(drop_glue::synthesize_glue(
            glue_id,
            glue_name,
            glue_sig,
            &shape,
            Some(&fat),
        )?)
        .map_err(|refusal| refusal.to_string())?;

    // The driver.
    let driver_id = FuncId::new(module.functions.len() as u32);
    let mut body = Vec::new();
    let mut next = 0u32;
    let mut fresh = || {
        let v = ValueId::new(next);
        next += 1;
        v
    };
    let mut value = |body: &mut Vec<InstrNode>, inst: Inst| {
        let v = fresh();
        body.push(InstrNode::new(inst).with_result(v));
        v
    };
    let int = |v: u128| match i128::try_from(v) {
        Ok(v) => Constant::Int(v),
        Err(_) => Constant::U128(v),
    };
    let n = value(&mut body, Inst::Const { ty: Ty::U64, value: int(u128::from(run.size.max(1))) });
    let buf = value(
        &mut body,
        Inst::Alloca { ty: Ty::I8, count: Some(n), align: Some(run.align.max(1)) },
    );
    if let Some((offset, bits, tag)) = run.tag {
        let ity = drop_glue::tag_int_ty(bits)?;
        let off = value(&mut body, Inst::Const { ty: Ty::I64, value: int(u128::from(offset)) });
        let tp = value(
            &mut body,
            Inst::GEP { pointee_ty: Ty::I8, base: buf, indices: vec![off], inbounds: true },
        );
        let tv = value(&mut body, Inst::Const { ty: ity.clone(), value: int(tag) });
        body.push(InstrNode::new(Inst::Store {
            ty: ity,
            ptr: tp,
            value: tv,
            volatile: false,
            align: None,
        }));
    }
    let arg = match run.elements {
        Some(elements) => {
            let len =
                value(&mut body, Inst::Const { ty: Ty::U64, value: int(u128::from(elements)) });
            value(
                &mut body,
                Inst::PtrFromParts {
                    ptr_ty: fat.clone(),
                    metadata_ty: Ty::U64,
                    data: buf,
                    metadata: len,
                },
            )
        }
        None => buf,
    };
    body.push(InstrNode::new(Inst::Call { callee: glue_id, args: vec![arg] }));
    body.push(InstrNode::new(Inst::Return { values: vec![] }));
    let mut driver =
        Function::new(driver_id, "trust-drop-glue-oracle-driver", unit_sig, BlockId::new(0));
    driver.blocks = vec![trust_ir::Block { id: BlockId::new(0), params: vec![], body }];
    module.try_add_function(driver).map_err(|refusal| refusal.to_string())?;

    let recorder = Recorder::default();
    Interpreter::with_module(&module)
        .with_host(&recorder)
        .execute_func(driver_id, [])
        .map_err(|e| format!("the reference interpreter refused the glue: {e:?}"))?;
    let calls = recorder.calls.into_inner().map_err(|_| "the recorder was poisoned".to_string())?;
    // Every pointer must be into the one buffer: the first allocation any call names.
    let base = calls.iter().find_map(|(_, p, _)| p.map(|(a, _)| a));
    let mut out = Vec::with_capacity(calls.len());
    for (name, ptr, metadata) in calls {
        let Some((allocation, offset)) = ptr else {
            return Err(format!("`{name}` was called without a pointer"));
        };
        if Some(allocation) != base {
            return Err(format!("`{name}` was called on another allocation"));
        }
        out.push((name, offset, metadata));
    }
    Ok(out)
}

/// THE EXECUTED COMPARISON: run the synthesized glue of `plan` ([`run_synthesized`]), once per
/// inhabited variant at the tag rustc's const-eval writes for it, and require the calls it makes
/// to equal rustc's shim events (`oracle`) for that variant, each child at the offset rustc's
/// layout gives its path. Returns how many runs agreed.
pub fn execute_glue<'tcx>(
    tcx: TyCtxt<'tcx>,
    glue: ty::Instance<'tcx>,
    plan: &GluePlan<'tcx>,
    oracle: &[GlueEvent],
) -> Result<usize, String> {
    let Some(dropped) = drop_glue::glue_instance_ty(glue) else {
        return Err("not a drop-glue instance with a type".to_string());
    };
    if let Some(e) = oracle.iter().find(|e| matches!(e, GlueEvent::Unmodelled { .. })) {
        return Err(format!("the shim has an event the executor cannot expect: {e:?}"));
    }
    let env = ty::TypingEnv::fully_monomorphized();
    let layout = tcx
        .layout_of(env.as_query_input(dropped))
        .map_err(|e| format!("`layout_of({dropped})` failed: {e:?}"))?;
    let named = plan.try_map(|i| Ok::<String, String>(drop_glue::glue_symbol(tcx, *i)))?;
    let glue_name = drop_glue::glue_symbol(tcx, glue);
    let elem_stride = match dropped.kind() {
        ty::Slice(elem) => Some(
            tcx.layout_of(env.as_query_input(*elem))
                .map_err(|e| format!("`layout_of({elem})` failed: {e:?}"))?
                .size
                .bytes(),
        ),
        _ => None,
    };
    let size = match elem_stride {
        Some(stride) => stride * ELEMENTS,
        None => layout.size.bytes(),
    };
    let align = layout.align.bytes();
    let elements = elem_stride.map(|_| ELEMENTS);

    // The runs: `(tag to store, the variant whose trace to expect)`.
    let mut runs: Vec<(Option<(u64, u32, u128)>, Option<u32>)> = Vec::new();
    match (&named, layout.layout.variants()) {
        (GlueShape::Enum { .. }, Variants::Multiple { tag, tag_encoding, tag_field, .. }) => {
            let bits = u32::try_from(tag.size(&tcx).bits()).map_err(|_| "tag width".to_string())?;
            let offset = layout.fields.offset(tag_field.as_usize()).bytes();
            let cx = ty::layout::LayoutCx::new(tcx, env);
            let ty::Adt(adt, _) = dropped.kind() else {
                return Err(format!("`{dropped}` has a tag but is not an ADT"));
            };
            for v in adt.variants().indices() {
                if layout.for_variant(&cx, v).is_uninhabited() {
                    continue;
                }
                let value = match tcx.tag_for_variant(env.as_query_input((dropped, v))) {
                    Some(scalar) => scalar.to_bits_unchecked(),
                    None => match tag_encoding {
                        // The untagged variant: any tag outside the niche range decodes to it.
                        TagEncoding::Niche { niche_start, .. } => {
                            niche_start.wrapping_sub(1) & drop_glue::width_mask(bits)
                        }
                        TagEncoding::Direct => {
                            return Err(format!(
                                "variant {} of `{dropped}` has no direct tag",
                                v.as_u32()
                            ));
                        }
                    },
                };
                runs.push((Some((offset, bits, value)), Some(v.as_u32())));
            }
        }
        (GlueShape::Enum { .. }, Variants::Single { index }) => {
            runs.push((None, Some(index.as_u32())));
        }
        (GlueShape::Enum { .. }, _) => return Err(format!("`{dropped}` has no executable layout")),
        _ => runs.push((None, None)),
    }

    let mut agreed = 0;
    for (tag, variant) in runs {
        let mut expected: Vec<ExecutedCall> = Vec::new();
        for e in oracle {
            if variant.is_some() && e.variant().is_some_and(|ev| Some(ev) != variant) {
                continue;
            }
            match e {
                GlueEvent::Destructor { callee } => expected.push((callee.clone(), 0, None)),
                GlueEvent::Child { path, glue } => {
                    expected.push((glue.clone(), path_offset(tcx, layout, path)?, None));
                }
                GlueEvent::SliceDelegate { glue, len } => {
                    expected.push((glue.clone(), 0, Some(u128::from(*len))));
                }
                GlueEvent::ElementLoop { glue } => {
                    let stride = elem_stride.ok_or("an element loop over a non-slice")?;
                    for i in 0..ELEMENTS {
                        expected.push((glue.clone(), i * stride, None));
                    }
                }
                GlueEvent::Unmodelled { what } => return Err(format!("unmodelled: {what}")),
            }
        }
        let run = GlueRun { size, align, tag, elements };
        let got = run_synthesized(&glue_name, &named, &run)?;
        if got != expected {
            return Err(format!(
                "variant {variant:?} (tag {tag:?}): the executed glue called {got:?}; rustc's shim \
                 drops {expected:?}"
            ));
        }
        agreed += 1;
    }
    Ok(agreed)
}

/// What [`check_glue`] found for one glue instance.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GlueOracleVerdict {
    /// The producer refuses this glue (`drop_glue::glue_plan`); nothing to compare. `class` is
    /// `upstream-body` or `shape`.
    Refused { class: &'static str, detail: String },
    /// Compared. `executed` is the number of interpreter runs that agreed, or why it failed.
    Checked { comparison: GlueComparison, executed: Result<usize, String> },
    /// The oracle itself could not read the shim.
    OracleFailed(String),
}

impl GlueOracleVerdict {
    /// Agreement on both comparisons.
    pub fn agrees(&self) -> bool {
        matches!(self, GlueOracleVerdict::Checked { comparison, executed: Ok(_) } if comparison.agrees())
    }
}

/// THE ORACLE for one drop-glue instance: the plan's events against rustc's shim, and the
/// synthesized body executed against the shim's events.
pub fn check_glue<'tcx>(tcx: TyCtxt<'tcx>, glue: ty::Instance<'tcx>) -> GlueOracleVerdict {
    // Types and paths in full: trimmed paths may be computed only for an emitted diagnostic.
    rustc_middle::ty::print::with_no_trimmed_paths!(check_glue_inner(tcx, glue))
}

fn check_glue_inner<'tcx>(tcx: TyCtxt<'tcx>, glue: ty::Instance<'tcx>) -> GlueOracleVerdict {
    let Some(dropped) = drop_glue::glue_instance_ty(glue) else {
        return GlueOracleVerdict::OracleFailed("not a drop-glue instance with a type".to_string());
    };
    let plan = match drop_glue::glue_plan(tcx, dropped) {
        Ok(plan) => plan,
        Err(refusal) => {
            let class = match refusal.class {
                drop_glue::GlueRefusalClass::UpstreamBody => "upstream-body",
                drop_glue::GlueRefusalClass::Shape => "shape",
            };
            return GlueOracleVerdict::Refused { class, detail: refusal.detail };
        }
    };
    let oracle = match shim_events(tcx, glue) {
        Ok(events) => events,
        Err(why) => return GlueOracleVerdict::OracleFailed(why),
    };
    let producer = drop_glue::plan_events(tcx, &plan);
    let comparison = compare_events(&oracle, &producer);
    let executed = execute_glue(tcx, glue, &plan, &oracle);
    GlueOracleVerdict::Checked { comparison, executed }
}

#[cfg(test)]
mod tests;
