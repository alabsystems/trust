//! Trust (step 2 increment 4c, 2026-10-02): DROP GLUE AS TRUST-IR — the glue PRODUCER.
//!
//! Design: `docs/design/2026-09-29-step2-inc4-drops.md` §4; D18 (OD-2: synthesized
//! glue and shims splice under D17's rule — structural checks plus the test-oracle differential,
//! no per-instance MIR seam differential) and D20 (`docs/DECISION_QUEUE.md`).
//!
//! # What this file is
//!
//! The PRODUCER of drop glue, in the sense that `lib.rs` is the producer of bodies: it computes
//! what `core::ptr::drop_glue::<T>` does from rustc's own layout and `Drop` impls, and writes it
//! as one table-free trust-ir function. It is NOT frozen (it is the producer under test). Two
//! frozen files judge and consume it:
//!
//! * `drop_glue_oracle.rs` (SAMPLE-MORE-OR-REFUSE-MORE) — the TEST ORACLE: the plan's events
//!   against rustc's own drop shim (`instance_mir(Shim(DropGlue(T)))`), and the synthesized body
//!   EXECUTED by the reference interpreter against the shim's events at rustc's own tag
//!   encoding (`tag_for_variant`);
//! * `rustc_codegen_trust_cg`'s `trust_ir_frontend/drop_glue_lane.rs` (BYTE-IDENTICAL) — the
//!   SPLICE DECISION: which glue bodies enter the codegen module, the resolution of every
//!   `Inst::Drop { ty, ptr }` to `Inst::Call { glue(T), [ptr] }`, and its postcondition.
//!
//! # The two halves
//!
//! * **Rustc half** ([`glue_plan`]): a [`GluePlan`] from `layout_of`, `AdtDef::destructor`,
//!   `needs_drop` per field and the enum's `TagEncoding`, exactly the decomposition rustc's
//!   `build_drop_shim` / `DropShimElaborator` makes (`rustc_mir_transform/src/shim.rs`,
//!   `elaborate_drop.rs`): `Drop::drop` first, then each needs-drop field in declaration order
//!   through that field's OWN glue; per variant for an enum (a switch on the decoded tag); an
//!   array delegates to its slice glue; a slice is an ascending index loop over its elements.
//!   Every shape this cut does not synthesize is a [`GlueRefusal`] naming its increment.
//! * **Pure half** ([`synthesize_glue`], [`rewrite_drops`], [`first_surviving_drop`]): the
//!   trust-ir. TyCtxt-free and unit-tested (`drop_glue/tests.rs`), including by executing it.
//!
//! # Table-free by construction
//!
//! A glue body uses only `Ptr` values, byte-offset `GEP`s over `I8` (offsets and strides from
//! `layout_of`), integer `Load`s of the tag, `Switch` / `CondBr` / `Br`, and direct `Call`s.
//! It never names a struct, enum, tuple or global row, so it can enter the assembled module
//! without the frozen crate splice's table remap. The ONE exception is a slice's fat pointer
//! (`FatPtr(Slice(TyId))`), whose `TyId` the caller must supply from a row the module already
//! has (the lane takes it from the dropped array's own `Ty::Array(TyId, _)` spelling).
//!
//! # Deviation from §4.2: children are direct calls, not `Inst::Drop`
//!
//! §4.2 had glue compose "through the same `Inst::Drop` the producer emits, so resolution
//! recurses". A child `Inst::Drop` must carry the child's trust-ir TYPE, and for a struct that is
//! a table row (`Ty::Struct(StructId)`) the glue would have to mint. So a glue body calls each
//! child's glue DIRECTLY; the resolution the design describes happens here, at synthesis, and
//! the module the lane builds holds no `Inst::Drop` at all (the postcondition).
//!
//! # The v55 drop-glue table (amendment D Part 1, D20) — keep this move possible
//!
//! The pinned trust-ir contains the v55 table (a module drop-glue table, rows resolved by type);
//! the lane registers no row (restated by step 2 increment 4d.0a, 2026-10-08 and 2026-10-13,
//! without the pin's current wire version, which every pin train moves; this text said "the pin
//! is v47" until then).
//! Each drop is resolved to a DIRECT CALL at the codegen seam. Rule S3
//! of v55 (`docs/first-party-pin-ledger.md` entry (g)) refuses a direct call of REGISTERED glue, so
//! either the lane keeps rewriting drops into calls and registers NO table row for that glue (what
//! it does), or it stops rewriting and registers every glue body as a row (leaving `Inst::Drop`
//! resolved by the table), a waiver of the frozen `drop_glue_lane.rs`. Never both for one glue
//! function. [`synthesize_glue`] names its callees by `FuncId` only, so either choice is
//! a change in the lane, not here.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com> | Copyright 2026 | License: MIT OR Apache-2.0

use rustc_abi::{Primitive, TagEncoding, Variants};
use rustc_middle::ty::{self, Ty as RustcTy, TyCtxt, TypeVisitableExt};
use trust_ir::{
    BinOp, Block, BlockId, BodyGate, CallingConv, Constant, FuncId, FuncTy, FuncTyId, Function,
    ICmpOp, Inst, InstrNode, Module, Producer, SwitchCase, Ty, ValueId,
};

use crate::drop_glue_oracle::{GlueEvent, PathElem};

/// The body-gate AUTHORITY a synthesized glue body carries.
///
/// What it asserts — exactly this, and nothing more: the body was synthesized by
/// [`synthesize_glue`] from [`glue_plan`] (rustc's layout and `Drop` impls), and the lane that
/// spliced it (`drop_glue_lane.rs`) checked its structural preconditions. It asserts NO MIR seam
/// differential (glue has no source body; D18 OD-2) and no discharged obligation. The test-oracle
/// differential against rustc's shim (`drop_glue_oracle.rs`) is a test, run over a corpus, not a
/// per-instance check.
///
/// NOTE for increment 5.4 (D31): the F1 codegen license recognizes exactly
/// `trust-direct-lane-structural` and `trust-instance-lane-structural`; until it also recognizes
/// this authority, a glue body is refused there, fail-closed.
pub const TRUST_DROP_GLUE_AUTHORITY: &str = "trust-drop-glue-lane-structural";

// =============================================================================================
// The plan: TyCtxt-free shapes, generic over the callee handle.
// =============================================================================================

/// One needs-drop child of a glue body: field `field` (declaration index) at byte `offset`,
/// dropped through its own glue `glue`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GlueChild<C> {
    pub field: u32,
    pub offset: u64,
    pub glue: C,
}

/// The needs-drop fields of one enum variant.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GlueArm<C> {
    pub variant: u32,
    pub fields: Vec<GlueChild<C>>,
}

/// How a tag decodes to a variant (rustc's `TagEncoding`, read off `layout_of`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TagScheme {
    /// The tag stores the discriminant, truncated to the tag's width: `(variant, tag bits)`.
    Direct { tags: Vec<(u32, u128)> },
    /// rustc's niche encoding: `relative = tag - niche_start` (wrapping, at the tag's width);
    /// `relative <= end - start` decodes to variant `start + relative`, anything else to
    /// `untagged`.
    Niche { untagged: u32, start: u32, end: u32, niche_start: u128 },
}

/// Where the tag lives and how it decodes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TagDecode {
    pub offset: u64,
    /// The tag's width in bits: 8, 16, 32, 64 or 128.
    pub bits: u32,
    pub scheme: TagScheme,
}

/// What one glue body does. `C` is the callee handle: a `ty::Instance` in a [`GluePlan`], a
/// `FuncId` at synthesis.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GlueShape<C> {
    /// `!needs_drop`: an empty body.
    Noop,
    /// A struct, tuple, union or closure environment: the destructor (if any), then each
    /// needs-drop field in declaration order. A union lists no field (its fields are never
    /// dropped).
    Fields { dtor: Option<C>, fields: Vec<GlueChild<C>> },
    /// An enum: the destructor (if any), then the arm of the variant the tag decodes to. `tag`
    /// is `None` when rustc stores no tag (`Variants::Single { index }`); then the arm of
    /// `untagged_index` is the only reachable one. `arms` lists every variant with a needs-drop
    /// field, inhabited or not, as rustc's shim does.
    Enum { dtor: Option<C>, tag: Option<TagDecode>, untagged_index: u32, arms: Vec<GlueArm<C>> },
    /// `[E; N]`: rustc's shim casts the pointer to `*mut [E]` and calls the slice glue.
    ArrayDelegate { slice_glue: C, len: u64 },
    /// `[E]`: an ascending index loop dropping each element through `elem_glue`.
    ElementLoop { elem_glue: C, stride: u64 },
}

impl<C> GlueShape<C> {
    /// The same shape with every callee mapped.
    pub fn try_map<D, E>(&self, mut f: impl FnMut(&C) -> Result<D, E>) -> Result<GlueShape<D>, E> {
        Ok(match self {
            GlueShape::Noop => GlueShape::Noop,
            GlueShape::Fields { dtor, fields } => {
                let dtor = match dtor {
                    Some(d) => Some(f(d)?),
                    None => None,
                };
                let mut out = Vec::with_capacity(fields.len());
                for c in fields {
                    out.push(GlueChild { field: c.field, offset: c.offset, glue: f(&c.glue)? });
                }
                GlueShape::Fields { dtor, fields: out }
            }
            GlueShape::Enum { dtor, tag, untagged_index, arms } => {
                let dtor = match dtor {
                    Some(d) => Some(f(d)?),
                    None => None,
                };
                let mut out = Vec::with_capacity(arms.len());
                for arm in arms {
                    let mut fields = Vec::with_capacity(arm.fields.len());
                    for c in &arm.fields {
                        fields.push(GlueChild {
                            field: c.field,
                            offset: c.offset,
                            glue: f(&c.glue)?,
                        });
                    }
                    out.push(GlueArm { variant: arm.variant, fields });
                }
                GlueShape::Enum {
                    dtor,
                    tag: tag.clone(),
                    untagged_index: *untagged_index,
                    arms: out,
                }
            }
            GlueShape::ArrayDelegate { slice_glue, len } => {
                GlueShape::ArrayDelegate { slice_glue: f(slice_glue)?, len: *len }
            }
            GlueShape::ElementLoop { elem_glue, stride } => {
                GlueShape::ElementLoop { elem_glue: f(elem_glue)?, stride: *stride }
            }
        })
    }

    /// Every callee the body names, in body order (the destructor first).
    pub fn callees(&self) -> Vec<&C> {
        match self {
            GlueShape::Noop => Vec::new(),
            GlueShape::Fields { dtor, fields } => {
                dtor.iter().chain(fields.iter().map(|c| &c.glue)).collect()
            }
            GlueShape::Enum { dtor, arms, .. } => dtor
                .iter()
                .chain(arms.iter().flat_map(|a| a.fields.iter().map(|c| &c.glue)))
                .collect(),
            GlueShape::ArrayDelegate { slice_glue, .. } => vec![slice_glue],
            GlueShape::ElementLoop { elem_glue, .. } => vec![elem_glue],
        }
    }

    /// The callees that are OTHER GLUE (not the destructor), in body order.
    pub fn child_glue(&self) -> Vec<&C> {
        match self {
            GlueShape::Noop => Vec::new(),
            GlueShape::Fields { fields, .. } => fields.iter().map(|c| &c.glue).collect(),
            GlueShape::Enum { arms, .. } => {
                arms.iter().flat_map(|a| a.fields.iter().map(|c| &c.glue)).collect()
            }
            GlueShape::ArrayDelegate { slice_glue, .. } => vec![slice_glue],
            GlueShape::ElementLoop { elem_glue, .. } => vec![elem_glue],
        }
    }

    /// The destructor, if the body calls one.
    pub fn destructor(&self) -> Option<&C> {
        match self {
            GlueShape::Fields { dtor, .. } | GlueShape::Enum { dtor, .. } => dtor.as_ref(),
            _ => None,
        }
    }

    /// Does this body's parameter have to be a fat slice pointer?
    pub fn takes_fat_pointer(&self) -> bool {
        matches!(self, GlueShape::ElementLoop { .. })
    }

    /// Does this body CALL a function taking a fat slice pointer?
    pub fn passes_fat_pointer(&self) -> bool {
        matches!(self, GlueShape::ArrayDelegate { .. })
    }
}

/// A glue plan as rustc's half computes it: callees are the destructor's `Drop::drop` instance
/// and each child's own drop-glue instance.
pub type GluePlan<'tcx> = GlueShape<ty::Instance<'tcx>>;

// =============================================================================================
// The pure half: synthesis.
// =============================================================================================

/// The signature of a glue function of `shape`: `(ptr) -> ()`, or `(fat) -> ()` for a slice.
/// `fat` is the slice's fat-pointer type (`Ty::FatPtr(FatPtrKind::Slice(TyId))`), required for
/// a slice glue.
pub fn glue_signature<C>(shape: &GlueShape<C>, fat: Option<&Ty>) -> Result<FuncTy, String> {
    let param = if shape.takes_fat_pointer() {
        fat.cloned().ok_or("a slice glue needs its fat-pointer type")?
    } else {
        Ty::Ptr
    };
    Ok(FuncTy { params: vec![param], returns: Vec::new(), is_vararg: false, abi: None })
}

/// The trust-ir integer type of a `bits`-wide tag.
pub fn tag_int_ty(bits: u32) -> Result<Ty, String> {
    match bits {
        8 => Ok(Ty::U8),
        16 => Ok(Ty::U16),
        32 => Ok(Ty::U32),
        64 => Ok(Ty::U64),
        128 => Ok(Ty::U128),
        other => Err(format!("a {other}-bit tag")),
    }
}

/// The all-ones mask of a `bits`-wide value.
pub fn width_mask(bits: u32) -> u128 {
    if bits >= 128 { u128::MAX } else { (1u128 << bits) - 1 }
}

fn int_constant(value: u128) -> Constant {
    match i128::try_from(value) {
        Ok(v) => Constant::Int(v),
        Err(_) => Constant::U128(value),
    }
}

/// A straight-line block builder. Parameters of the function are the entry block's parameters
/// (`ValueId(0)` is the glue's pointer).
struct Builder {
    next_value: u32,
    next_block: u32,
    blocks: Vec<Block>,
    cur: Option<Block>,
}

impl Builder {
    fn new(param: Ty) -> Self {
        Builder {
            next_value: 1,
            next_block: 1,
            blocks: Vec::new(),
            cur: Some(Block::new(BlockId::new(0)).with_param(ValueId::new(0), param)),
        }
    }

    fn fresh(&mut self) -> ValueId {
        let v = ValueId::new(self.next_value);
        self.next_value += 1;
        v
    }

    fn cur(&mut self) -> Result<&mut Block, String> {
        self.cur.as_mut().ok_or_else(|| "glue synthesis: no open block".to_string())
    }

    fn value(&mut self, inst: Inst) -> Result<ValueId, String> {
        let v = self.fresh();
        self.cur()?.body.push(InstrNode::new(inst).with_result(v));
        Ok(v)
    }

    fn effect(&mut self, inst: Inst) -> Result<(), String> {
        self.cur()?.body.push(InstrNode::new(inst));
        Ok(())
    }

    fn terminate(&mut self, inst: Inst) -> Result<(), String> {
        self.effect(inst)?;
        let block = self.cur.take().ok_or("glue synthesis: no open block")?;
        self.blocks.push(block);
        Ok(())
    }

    fn reserve(&mut self) -> BlockId {
        let b = BlockId::new(self.next_block);
        self.next_block += 1;
        b
    }

    fn open(&mut self, id: BlockId, params: Vec<(ValueId, Ty)>) -> Result<(), String> {
        if self.cur.is_some() {
            return Err("glue synthesis: a block was left open".to_string());
        }
        self.cur = Some(Block { id, params, body: Vec::new() });
        Ok(())
    }

    /// `base + offset` as a byte-offset GEP over `I8` (or `base` itself at offset 0).
    fn addr(&mut self, base: ValueId, offset: u64) -> Result<ValueId, String> {
        if offset == 0 {
            return Ok(base);
        }
        let off = i128::from(offset);
        let o = self.value(Inst::Const { ty: Ty::I64, value: Constant::Int(off) })?;
        self.value(Inst::GEP { pointee_ty: Ty::I8, base, indices: vec![o], inbounds: true })
    }

    fn call(&mut self, callee: FuncId, arg: ValueId) -> Result<(), String> {
        self.effect(Inst::Call { callee, args: vec![arg] })
    }

    fn drop_children(&mut self, base: ValueId, fields: &[GlueChild<FuncId>]) -> Result<(), String> {
        for c in fields {
            let a = self.addr(base, c.offset)?;
            self.call(c.glue, a)?;
        }
        Ok(())
    }

    fn ret(&mut self) -> Result<(), String> {
        self.terminate(Inst::Return { values: Vec::new() })
    }

    fn br(&mut self, target: BlockId, args: Vec<ValueId>) -> Result<(), String> {
        self.terminate(Inst::Br { target, args })
    }

    fn finish(self) -> Result<Vec<Block>, String> {
        if self.cur.is_some() {
            return Err("glue synthesis: the last block has no terminator".to_string());
        }
        Ok(self.blocks)
    }
}

/// SYNTHESIZE one glue function: `id` / `name` / `func_ty` as the caller interns them, the body
/// from `shape` (callees as `FuncId`s of the module the function will live in). `fat` is the
/// slice fat-pointer type: the parameter of an [`GlueShape::ElementLoop`], the argument an
/// [`GlueShape::ArrayDelegate`] passes. PURE.
///
/// The body's calling convention is `Rust`, its producer `TRust`, and it carries the
/// [`TRUST_DROP_GLUE_AUTHORITY`] body gate.
pub fn synthesize_glue(
    id: FuncId,
    name: &str,
    func_ty: FuncTyId,
    shape: &GlueShape<FuncId>,
    fat: Option<&Ty>,
) -> Result<Function, String> {
    let param = if shape.takes_fat_pointer() {
        fat.cloned().ok_or("a slice glue needs its fat-pointer type")?
    } else {
        Ty::Ptr
    };
    let mut b = Builder::new(param);
    let p = ValueId::new(0);
    match shape {
        GlueShape::Noop => b.ret()?,
        GlueShape::Fields { dtor, fields } => {
            if let Some(d) = dtor {
                b.call(*d, p)?;
            }
            b.drop_children(p, fields)?;
            b.ret()?;
        }
        GlueShape::Enum { dtor, tag: None, untagged_index, arms } => {
            if let Some(d) = dtor {
                b.call(*d, p)?;
            }
            // No tag: rustc's verdict that only `untagged_index` is inhabited. Every other arm
            // belongs to an uninhabited variant no value can be.
            if let Some(arm) = arms.iter().find(|a| a.variant == *untagged_index) {
                b.drop_children(p, &arm.fields)?;
            }
            b.ret()?;
        }
        GlueShape::Enum { dtor, tag: Some(tag), untagged_index: _, arms } => {
            if let Some(d) = dtor {
                b.call(*d, p)?;
            }
            let ity = tag_int_ty(tag.bits)?;
            let mask = width_mask(tag.bits);
            let ret_bb = b.reserve();
            let arm_bbs: Vec<(u32, BlockId)> =
                arms.iter().map(|a| (a.variant, b.reserve())).collect();
            let tp = b.addr(p, tag.offset)?;
            let t =
                b.value(Inst::Load { ty: ity.clone(), ptr: tp, volatile: false, align: None })?;
            match &tag.scheme {
                TagScheme::Direct { tags } => {
                    let mut cases = Vec::with_capacity(arm_bbs.len());
                    for (v, bb) in &arm_bbs {
                        let Some((_, bits)) = tags.iter().find(|(tv, _)| tv == v) else {
                            return Err(format!("variant {v} has no direct tag"));
                        };
                        let value = int_constant(*bits & mask);
                        if cases.iter().any(|c: &SwitchCase| c.value == value) {
                            return Err(format!("two variants share the direct tag {bits}"));
                        }
                        cases.push(SwitchCase { value, target: *bb, args: Vec::new() });
                    }
                    b.terminate(Inst::Switch {
                        value: t,
                        default: ret_bb,
                        default_args: Vec::new(),
                        cases,
                        exhaustive_enum_unreachable: false,
                    })?;
                }
                TagScheme::Niche { untagged, start, end, niche_start } => {
                    if end < start {
                        return Err(format!("an empty niche range {start}..={end}"));
                    }
                    let ns = b.value(Inst::Const {
                        ty: ity.clone(),
                        value: int_constant(*niche_start & mask),
                    })?;
                    let rel =
                        b.value(Inst::BinOp { op: BinOp::Sub, ty: ity.clone(), lhs: t, rhs: ns })?;
                    let span = u128::from(end - start);
                    let max =
                        b.value(Inst::Const { ty: ity.clone(), value: int_constant(span & mask) })?;
                    let inr = b.value(Inst::ICmp {
                        op: ICmpOp::Ule,
                        ty: ity.clone(),
                        lhs: rel,
                        rhs: max,
                    })?;
                    let niche_bb = b.reserve();
                    let untagged_bb = b.reserve();
                    b.terminate(Inst::CondBr {
                        cond: inr,
                        then_target: niche_bb,
                        then_args: Vec::new(),
                        else_target: untagged_bb,
                        else_args: Vec::new(),
                    })?;
                    b.open(niche_bb, Vec::new())?;
                    let mut cases = Vec::new();
                    for (v, bb) in &arm_bbs {
                        if (*start..=*end).contains(v) {
                            let value = int_constant(u128::from(v - start));
                            cases.push(SwitchCase { value, target: *bb, args: Vec::new() });
                        }
                    }
                    b.terminate(Inst::Switch {
                        value: rel,
                        default: ret_bb,
                        default_args: Vec::new(),
                        cases,
                        exhaustive_enum_unreachable: false,
                    })?;
                    b.open(untagged_bb, Vec::new())?;
                    let target =
                        arm_bbs.iter().find(|(v, _)| v == untagged).map_or(ret_bb, |(_, bb)| *bb);
                    b.br(target, Vec::new())?;
                }
            }
            for (arm, (_, bb)) in arms.iter().zip(&arm_bbs) {
                b.open(*bb, Vec::new())?;
                b.drop_children(p, &arm.fields)?;
                b.br(ret_bb, Vec::new())?;
            }
            b.open(ret_bb, Vec::new())?;
            b.ret()?;
        }
        GlueShape::ArrayDelegate { slice_glue, len } => {
            let fat = fat.ok_or("an array glue needs its slice's fat-pointer type")?;
            let n = b.value(Inst::Const { ty: Ty::U64, value: Constant::Int(i128::from(*len)) })?;
            let fp = b.value(Inst::PtrFromParts {
                ptr_ty: fat.clone(),
                metadata_ty: Ty::U64,
                data: p,
                metadata: n,
            })?;
            b.call(*slice_glue, fp)?;
            b.ret()?;
        }
        GlueShape::ElementLoop { elem_glue, stride } => {
            let fat = fat.ok_or("a slice glue needs its fat-pointer type")?;
            let data = b.value(Inst::PtrData { ptr_ty: fat.clone(), ptr: p })?;
            let len =
                b.value(Inst::PtrMetadata { ptr_ty: fat.clone(), metadata_ty: Ty::U64, ptr: p })?;
            let zero = b.value(Inst::Const { ty: Ty::U64, value: Constant::Int(0) })?;
            let head = b.reserve();
            let body = b.reserve();
            let exit = b.reserve();
            b.br(head, vec![zero])?;
            let i = b.fresh();
            b.open(head, vec![(i, Ty::U64)])?;
            let more = b.value(Inst::ICmp { op: ICmpOp::Ult, ty: Ty::U64, lhs: i, rhs: len })?;
            b.terminate(Inst::CondBr {
                cond: more,
                then_target: body,
                then_args: Vec::new(),
                else_target: exit,
                else_args: Vec::new(),
            })?;
            b.open(body, Vec::new())?;
            let s =
                b.value(Inst::Const { ty: Ty::U64, value: Constant::Int(i128::from(*stride)) })?;
            let off = b.value(Inst::BinOp { op: BinOp::Mul, ty: Ty::U64, lhs: i, rhs: s })?;
            let ep = b.value(Inst::GEP {
                pointee_ty: Ty::I8,
                base: data,
                indices: vec![off],
                inbounds: true,
            })?;
            b.call(*elem_glue, ep)?;
            let one = b.value(Inst::Const { ty: Ty::U64, value: Constant::Int(1) })?;
            let next = b.value(Inst::BinOp { op: BinOp::Add, ty: Ty::U64, lhs: i, rhs: one })?;
            b.br(head, vec![next])?;
            b.open(exit, Vec::new())?;
            b.ret()?;
        }
    }
    let mut function = Function::new(id, name, func_ty, BlockId::new(0));
    function.blocks = b.finish()?;
    function.calling_conv = CallingConv::Rust;
    function.producer = Some(Producer::TRust);
    function.body_gate =
        Some(BodyGate::Gated { authority: TRUST_DROP_GLUE_AUTHORITY.to_string(), evidence: None });
    Ok(function)
}

// =============================================================================================
// The pure half: the resolution rewrite and its postcondition.
// =============================================================================================

/// One `Inst::Drop` of a function: where it is, what it drops, through which pointer.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DropNode {
    pub block: BlockId,
    pub index: usize,
    pub ty: Ty,
    pub ptr: ValueId,
}

/// Every `Inst::Drop` of `function`, in block order. PURE.
pub fn drop_nodes(function: &Function) -> Vec<DropNode> {
    let mut out = Vec::new();
    for block in &function.blocks {
        for (index, node) in block.body.iter().enumerate() {
            if let Inst::Drop { ty, ptr } = &node.inst {
                out.push(DropNode { block: block.id, index, ty: ty.clone(), ptr: *ptr });
            }
        }
    }
    out
}

/// THE RESOLUTION REWRITE of one function: each `Inst::Drop { ty, ptr }` becomes
/// `Inst::Call { callee: resolve(node), args: [ptr] }`, keeping the node's span and scope.
///
/// ALL OR NOTHING: every drop is resolved before any is rewritten, so an `Err` leaves `function`
/// exactly as it was. Returns how many drops were rewritten. PURE.
pub fn rewrite_drops(
    function: &mut Function,
    mut resolve: impl FnMut(&DropNode) -> Result<FuncId, String>,
) -> Result<usize, String> {
    let nodes = drop_nodes(function);
    let mut resolved = Vec::with_capacity(nodes.len());
    for node in &nodes {
        resolved.push((node.block, node.index, node.ptr, resolve(node)?));
    }
    for (block, index, ptr, callee) in &resolved {
        let Some(b) = function.blocks.iter_mut().find(|b| b.id == *block) else {
            return Err(format!("internal: block {block:?} vanished during the rewrite"));
        };
        let Some(node) = b.body.get_mut(*index) else {
            return Err(format!("internal: instruction {index} of {block:?} vanished"));
        };
        if !node.results.is_empty() {
            return Err(format!("a drop at {block:?}:{index} defines a value"));
        }
        node.inst = Inst::Call { callee: *callee, args: vec![*ptr] };
    }
    Ok(resolved.len())
}

/// THE POSTCONDITION of the resolution: the first `Inst::Drop` that survives in any function of
/// `module`, or `None`. A codegen module must answer `None`. PURE.
pub fn first_surviving_drop(module: &Module) -> Option<(FuncId, BlockId, usize)> {
    for function in &module.functions {
        for block in &function.blocks {
            for (index, node) in block.body.iter().enumerate() {
                if matches!(node.inst, Inst::Drop { .. }) {
                    return Some((function.id, block.id, index));
                }
            }
        }
    }
    None
}

// =============================================================================================
// The rustc half: the plan from layout.
// =============================================================================================

/// The class of a shape this cut does not synthesize, which the lane maps onto the trust-cg
/// frontend's refusal classes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum GlueRefusalClass {
    /// The glue needs a body from another crate: a `Drop::drop` or dealloc in `core` / `alloc` /
    /// `std` (`Vec`, `String`, `Box`, `Rc`, ...) or in any upstream crate. Increment 6 (trust-ir
    /// in metadata) with increment 5 (real calls). Frontend class `[upstream-body]`.
    UpstreamBody,
    /// A shape this cut does not synthesize (`dyn`, coroutine, async drop, a packed struct with a
    /// needs-drop field, a zero-variant enum, a generic destructor, a non-concrete type) or a
    /// layout question rustc could not answer. Frontend class `[synthesized-instance]`.
    Shape,
}

/// Why no glue is synthesized for a type.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GlueRefusal {
    pub class: GlueRefusalClass,
    pub detail: String,
}

fn refused(class: GlueRefusalClass, detail: impl Into<String>) -> GlueRefusal {
    GlueRefusal { class, detail: detail.into() }
}

/// The type a drop-glue instance drops: `Some(T)` for `Shim(DropGlue(_, Some(T)))`.
pub fn glue_instance_ty<'tcx>(instance: ty::Instance<'tcx>) -> Option<RustcTy<'tcx>> {
    match instance.def {
        ty::InstanceKind::Shim(ty::ShimKind::DropGlue(_, ty)) => ty,
        _ => None,
    }
}

/// `<T as Drop>::drop`, resolved at `fully_monomorphized()`.
fn destructor_instance<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: RustcTy<'tcx>,
) -> Result<ty::Instance<'tcx>, GlueRefusal> {
    let env = ty::TypingEnv::fully_monomorphized();
    let drop_trait =
        tcx.require_lang_item(rustc_attr_ir::lang_items::LangItem::Drop, rustc_span::DUMMY_SP);
    let Some(&drop_fn) = tcx.associated_item_def_ids(drop_trait).first() else {
        return Err(refused(GlueRefusalClass::Shape, "the `Drop` trait has no method"));
    };
    let resolved = ty::Instance::try_resolve(tcx, env, drop_fn, tcx.mk_args(&[ty.into()]));
    let Ok(Some(instance)) = resolved else {
        return Err(refused(
            GlueRefusalClass::Shape,
            format!("`<{ty} as Drop>::drop` does not resolve"),
        ));
    };
    if !matches!(instance.def, ty::InstanceKind::Item(_)) {
        return Err(refused(
            GlueRefusalClass::Shape,
            format!("`<{ty} as Drop>::drop` resolves to {:?}, not a plain item", instance.def),
        ));
    }
    let def_id = instance.def_id();
    if !def_id.is_local() {
        return Err(refused(
            GlueRefusalClass::UpstreamBody,
            format!(
                "the destructor `{}` is in crate `{}` (trust-ir in metadata, increment 6; real \
                 calls, increment 5)",
                tcx.def_path_str(def_id),
                tcx.crate_name(def_id.krate)
            ),
        ));
    }
    if instance.args.iter().any(|arg| arg.as_region().is_none()) {
        return Err(refused(
            GlueRefusalClass::Shape,
            format!(
                "the destructor `{}` is a generic impl's instance; a monomorphic local `Drop` impl \
                 only in this cut",
                tcx.def_path_str(def_id)
            ),
        ));
    }
    Ok(instance)
}

fn normalized<'tcx>(
    tcx: TyCtxt<'tcx>,
    value: ty::Unnormalized<'tcx, RustcTy<'tcx>>,
) -> Result<RustcTy<'tcx>, GlueRefusal> {
    let env = ty::TypingEnv::fully_monomorphized();
    tcx.try_normalize_erasing_regions(env, value).map_err(|e| {
        refused(GlueRefusalClass::Shape, format!("a field type does not normalize: {e:?}"))
    })
}

fn needs_drop<'tcx>(tcx: TyCtxt<'tcx>, ty: RustcTy<'tcx>) -> bool {
    ty.needs_drop(tcx, ty::TypingEnv::fully_monomorphized())
}

/// `TRUST_IR_GLUE_MUTATE`: a TEST-ONLY mutation of the plan, so a fixture can show that the
/// oracle (`drop_glue_oracle.rs`) catches a wrong glue — each mutation is one a structural
/// comparison or an execution must see. Unset in every real build.
///
/// * `drop-dtor` — the destructor call is left out (a MISS);
/// * `reverse-fields` — a struct's or a variant's fields are dropped in reverse order (ORDER);
/// * `shift-offsets` — every child is dropped one byte past its field (only EXECUTION sees it);
/// * `skew-tags` — every direct tag and the niche start are off by one (only EXECUTION sees it).
fn mutation() -> Option<&'static str> {
    static M: std::sync::OnceLock<Option<&'static str>> = std::sync::OnceLock::new();
    *M.get_or_init(|| match std::env::var("TRUST_IR_GLUE_MUTATE").ok().as_deref() {
        Some("drop-dtor") => Some("drop-dtor"),
        Some("reverse-fields") => Some("reverse-fields"),
        Some("shift-offsets") => Some("shift-offsets"),
        Some("skew-tags") => Some("skew-tags"),
        _ => None,
    })
}

fn mutate<C>(mut plan: GlueShape<C>) -> GlueShape<C> {
    let Some(m) = mutation() else { return plan };
    let mut children = |fields: &mut Vec<GlueChild<C>>| match m {
        "reverse-fields" => fields.reverse(),
        "shift-offsets" => fields.iter_mut().for_each(|c| c.offset += 1),
        _ => {}
    };
    match &mut plan {
        GlueShape::Fields { dtor, fields } => {
            if m == "drop-dtor" {
                *dtor = None;
            }
            children(fields);
        }
        GlueShape::Enum { dtor, tag, arms, .. } => {
            if m == "drop-dtor" {
                *dtor = None;
            }
            arms.iter_mut().for_each(|a| children(&mut a.fields));
            if let (Some(tag), "skew-tags") = (tag, m) {
                let mask = width_mask(tag.bits);
                match &mut tag.scheme {
                    TagScheme::Direct { tags } => {
                        tags.iter_mut().for_each(|(_, t)| *t = t.wrapping_add(1) & mask)
                    }
                    TagScheme::Niche { niche_start, .. } => {
                        *niche_start = niche_start.wrapping_add(1) & mask
                    }
                }
            }
        }
        _ => {}
    }
    plan
}

/// THE RUSTC HALF: what `core::ptr::drop_glue::<ty>` does, as a [`GluePlan`], or why this cut
/// does not synthesize it. `ty` must be concrete (no parameter, inference variable, alias or
/// opaque). Codegen-time only (it asks `layout_of` and resolves instances); never call it inside
/// a `mir_built` frame.
///
/// Refusal details spell types and paths in full (`with_no_trimmed_paths`): trimmed paths may be
/// computed only for a diagnostic that is emitted.
pub fn glue_plan<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: RustcTy<'tcx>,
) -> Result<GluePlan<'tcx>, GlueRefusal> {
    rustc_middle::ty::print::with_no_trimmed_paths!(glue_plan_unmutated(tcx, ty)).map(mutate)
}

fn glue_plan_unmutated<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: RustcTy<'tcx>,
) -> Result<GluePlan<'tcx>, GlueRefusal> {
    use GlueRefusalClass::{Shape, UpstreamBody};
    let env = ty::TypingEnv::fully_monomorphized();
    if ty.has_non_region_param() || ty.has_infer() || ty.has_aliases() || ty.has_opaque_types() {
        return Err(refused(Shape, format!("`{ty}` is not a concrete type")));
    }
    if !needs_drop(tcx, ty) {
        return Ok(GlueShape::Noop);
    }
    let layout_of = |t: RustcTy<'tcx>| {
        tcx.layout_of(env.as_query_input(t))
            .map_err(|e| refused(Shape, format!("`layout_of({t})` failed: {e:?}")))
    };
    let child = |fty: RustcTy<'tcx>| ty::Instance::resolve_drop_glue(tcx, fty);
    match *ty.kind() {
        ty::Adt(adt, args) => {
            if adt.is_box() {
                return Err(refused(
                    UpstreamBody,
                    format!(
                        "`{ty}`: a `Box` drops its contents, then `Box`'s own destructor, whose \
                         dealloc is in `alloc` (increment 6)"
                    ),
                ));
            }
            if adt.async_destructor(tcx).is_some() {
                return Err(refused(Shape, format!("`{ty}` has an async destructor")));
            }
            let dtor = if adt.destructor(tcx).is_some() {
                Some(destructor_instance(tcx, ty)?)
            } else {
                None
            };
            if adt.is_union() || adt.is_manually_drop() {
                return Ok(GlueShape::Fields { dtor, fields: Vec::new() });
            }
            if adt.variants().is_empty() {
                return Err(refused(
                    Shape,
                    format!("`{ty}` is a zero-variant enum (rustc: unreachable)"),
                ));
            }
            let layout = layout_of(ty)?;
            let cx = ty::layout::LayoutCx::new(tcx, env);
            let field_children =
                |variant: &ty::VariantDef,
                 vlayout: &ty::layout::TyAndLayout<'tcx>|
                 -> Result<Vec<GlueChild<ty::Instance<'tcx>>>, GlueRefusal> {
                    let mut out = Vec::new();
                    for (i, f) in variant.fields.iter().enumerate() {
                        let fty = normalized(tcx, f.ty(tcx, args))?;
                        if !needs_drop(tcx, fty) {
                            continue;
                        }
                        if i >= vlayout.fields.count() {
                            return Err(refused(
                                Shape,
                                format!("`{ty}`: the layout carries no offset for field {i}"),
                            ));
                        }
                        let offset = vlayout.fields.offset(i).bytes();
                        out.push(GlueChild { field: i as u32, offset, glue: child(fty) });
                    }
                    Ok(out)
                };
            if adt.repr().packed() {
                let any = adt.all_fields().any(|f| {
                    normalized(tcx, f.ty(tcx, args)).map_or(true, |fty| needs_drop(tcx, fty))
                });
                if any {
                    return Err(refused(
                        Shape,
                        format!(
                            "`{ty}` is a packed struct with a needs-drop field (rustc moves it to \
                             an aligned temporary before dropping it)"
                        ),
                    ));
                }
            }
            if !adt.is_enum() {
                let variant = adt.non_enum_variant();
                let fields = field_children(variant, &layout)?;
                return Ok(GlueShape::Fields { dtor, fields });
            }
            let mut arms = Vec::new();
            for (v, variant) in adt.variants().iter_enumerated() {
                let vlayout = layout.for_variant(&cx, v);
                let fields = field_children(variant, &vlayout)?;
                if !fields.is_empty() {
                    arms.push(GlueArm { variant: v.as_u32(), fields });
                }
            }
            let (tag, untagged_index) = match layout.layout.variants() {
                Variants::Empty => {
                    return Err(refused(Shape, format!("`{ty}` has no valid variant")));
                }
                Variants::Single { index } => (None, index.as_u32()),
                Variants::Multiple { tag, tag_encoding, tag_field, .. } => {
                    if matches!(tag.primitive(), Primitive::Float(_)) {
                        return Err(refused(Shape, format!("`{ty}` has a float tag")));
                    }
                    let bits = tag.size(&tcx).bits();
                    let bits = u32::try_from(bits)
                        .map_err(|_| refused(Shape, format!("`{ty}` has a {bits}-bit tag")))?;
                    tag_int_ty(bits).map_err(|why| refused(Shape, format!("`{ty}` has {why}")))?;
                    let tag_field = tag_field.as_usize();
                    if tag_field >= layout.fields.count() {
                        return Err(refused(
                            Shape,
                            format!("`{ty}`: the tag field is out of range"),
                        ));
                    }
                    let offset = layout.fields.offset(tag_field).bytes();
                    let mask = width_mask(bits);
                    let (scheme, untagged) = match tag_encoding {
                        TagEncoding::Direct => (
                            TagScheme::Direct {
                                tags: adt
                                    .variants()
                                    .indices()
                                    .map(|v| {
                                        (
                                            v.as_u32(),
                                            adt.discriminant_for_variant(tcx, v).val & mask,
                                        )
                                    })
                                    .collect(),
                            },
                            u32::MAX,
                        ),
                        TagEncoding::Niche { untagged_variant, niche_variants, niche_start } => (
                            TagScheme::Niche {
                                untagged: untagged_variant.as_u32(),
                                start: niche_variants.start.as_u32(),
                                end: niche_variants.last.as_u32(),
                                niche_start: *niche_start,
                            },
                            untagged_variant.as_u32(),
                        ),
                    };
                    (Some(TagDecode { offset, bits, scheme }), untagged)
                }
            };
            Ok(GlueShape::Enum { dtor, tag, untagged_index, arms })
        }
        ty::Tuple(tys) => {
            let layout = layout_of(ty)?;
            let mut fields = Vec::new();
            for (i, fty) in tys.iter().enumerate() {
                let fty = normalized(tcx, ty::Unnormalized::new_wip(fty))?;
                if needs_drop(tcx, fty) {
                    fields.push(GlueChild {
                        field: i as u32,
                        offset: layout.fields.offset(i).bytes(),
                        glue: child(fty),
                    });
                }
            }
            Ok(GlueShape::Fields { dtor: None, fields })
        }
        ty::Closure(_, args) => {
            let layout = layout_of(ty)?;
            let mut fields = Vec::new();
            for (i, fty) in args.as_closure().upvar_tys().iter().enumerate() {
                let fty = normalized(tcx, ty::Unnormalized::new_wip(fty))?;
                if needs_drop(tcx, fty) {
                    if i >= layout.fields.count() {
                        return Err(refused(Shape, format!("`{ty}`: no offset for upvar {i}")));
                    }
                    fields.push(GlueChild {
                        field: i as u32,
                        offset: layout.fields.offset(i).bytes(),
                        glue: child(fty),
                    });
                }
            }
            Ok(GlueShape::Fields { dtor: None, fields })
        }
        ty::Array(elem, len) => {
            let Some(len) = len.try_to_target_usize(tcx) else {
                return Err(refused(Shape, format!("`{ty}` has no concrete length")));
            };
            Ok(GlueShape::ArrayDelegate { slice_glue: child(RustcTy::new_slice(tcx, elem)), len })
        }
        ty::Slice(elem) => {
            let stride = layout_of(elem)?.size.bytes();
            Ok(GlueShape::ElementLoop { elem_glue: child(elem), stride })
        }
        ty::Dynamic(..) => Err(refused(
            Shape,
            format!("`{ty}`: `dyn` glue calls vtable slot 0 (relocated statics, step 4)"),
        )),
        ty::Coroutine(..) | ty::CoroutineClosure(..) | ty::CoroutineWitness(..) => {
            Err(refused(Shape, format!("`{ty}`: coroutine glue (`coroutine_drop`)")))
        }
        _ => Err(refused(Shape, format!("drop glue for `{ty}` is not synthesized in this cut"))),
    }
}

/// The glue's link-time symbol.
pub fn glue_symbol<'tcx>(tcx: TyCtxt<'tcx>, instance: ty::Instance<'tcx>) -> String {
    tcx.symbol_name(instance).name.to_string()
}

/// THE PRODUCER'S CLAIM, as the test oracle compares it (`drop_glue_oracle.rs`): the events the
/// glue performs, in order — the destructor, then each child by its field path, an enum's arms
/// in variant order.
pub fn plan_events<'tcx>(tcx: TyCtxt<'tcx>, plan: &GluePlan<'tcx>) -> Vec<GlueEvent> {
    let sym = |i: &ty::Instance<'tcx>| glue_symbol(tcx, *i);
    let mut out = Vec::new();
    match plan {
        GlueShape::Noop => {}
        GlueShape::Fields { dtor, fields } => {
            if let Some(d) = dtor {
                out.push(GlueEvent::Destructor { callee: sym(d) });
            }
            for c in fields {
                out.push(GlueEvent::Child {
                    path: vec![PathElem::Field(c.field)],
                    glue: sym(&c.glue),
                });
            }
        }
        GlueShape::Enum { dtor, arms, .. } => {
            if let Some(d) = dtor {
                out.push(GlueEvent::Destructor { callee: sym(d) });
            }
            for arm in arms {
                for c in &arm.fields {
                    out.push(GlueEvent::Child {
                        path: vec![PathElem::Variant(arm.variant), PathElem::Field(c.field)],
                        glue: sym(&c.glue),
                    });
                }
            }
        }
        GlueShape::ArrayDelegate { slice_glue, len } => {
            out.push(GlueEvent::SliceDelegate { glue: sym(slice_glue), len: *len });
        }
        GlueShape::ElementLoop { elem_glue, .. } => {
            out.push(GlueEvent::ElementLoop { glue: sym(elem_glue) });
        }
    }
    out
}

#[cfg(test)]
mod tests;
