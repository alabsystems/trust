//! Trust (step 2 increment 6): THE LEVEL-S TEMPLATE LANE.
//!
//! Plan: `docs/design/2026-10-08-step2-inc6-step5-level-s-producer-plan.md` §1; design:
//! `docs/design/2026-10-02-step2-inc6-trust-ir-in-metadata.md` §2.3 and §10 "6.5"; the carrier is
//! trust-ir amendment S (`trust_ir::template`, `trust_ir_build::template`). Not frozen.
//!
//! # What this lane is
//!
//! A definition with a TEMPLATE PARAMETER (a type or const parameter of its flattened generics
//! that is not one of rustc's synthetic closure, coroutine, coroutine-closure or inline-const
//! parameters, whose `def_id` is the owning definition itself) is lowered a SECOND time at
//! `mir_built`, inside the producer's existing entry ([`capture`], called by
//! `lower_module_from_thir` after the mainline lowering returns), in TEMPLATE MODE
//! (INC6.5-LANE). Nothing about the mainline lowering changes; the second lowering registers
//! nothing the mainline registers (`register_direct_obligations` is false), and its census inputs
//! reach the effect-conservation registry by their own call (`record_template_body`).
//!
//! Template mode spells (INC6.5-SENTINEL) — inside the per-body module, which stays a level-R
//! `Module`:
//!
//! * a type parameter `p` (its index in the lane) as `Ty::Dialect(trust_template, param_<p>, 1)`.
//!   The producer emits no other `Ty::Dialect`, so the spelling is unambiguous, and any other
//!   dialect type in a template is refused;
//! * a scalar const parameter `p`, at the root of an `Inst::Const` of its scalar type, as
//!   `Constant::SymbolAddr { symbol: "!trust_template_param::<p>", addend: 0 }`;
//! * a pointer by a DETERMINATION of its metadata, never by the absence of one
//!   (INC6.5-POINTER-META, `LowerCx::template_pointer_ty`).
//!
//! Generic Rust callees and builtin Fn calls carry owner-bound stable host keys
//! and complete declarations from the source signature. Fn calls retain their
//! receiver and tuple; no runtime havoc lowering is reused. Unsupported type,
//! layout, intrinsic, caller-location and binder shapes remain explicit refusals.
//!
//! [`abstract_template`] then maps a captured sentinel module to an amendment-S [`Template`] by a
//! total level map, after an ESCAPE CHECK that no sentinel sits where the level map does not
//! reach (a ground table, a global initializer, an aggregate constant's child).
//!
//! # What it grants
//!
//! Nothing (INC6.5-NO-AUTHORITY). A template is judged and recorded, and since 6.5.4
//! (687eab86c1) its authenticated level-S row is written to rmeta. No consumer admits one: no
//! admission, splice, strict, scorecard or sidecar path reads a template or a template verdict.
//! The only reader is the default-off, driver-fenced template-instance equivalence TEST-ORACLE
//! (`template_metadata/oracle.rs`), which returns no IR, token or gate (pinned by
//! `no_codegen_or_admission_path_reads_a_template` in `lib.rs`).
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com> | Copyright 2026 | License: MIT OR Apache-2.0

use std::collections::{BTreeMap, BTreeSet};
use std::convert::Infallible;

use rustc_hir::def::DefKind;
use rustc_middle::thir::{BodyTy, ExprId, Thir};
use rustc_middle::ty::{self, TyCtxt};
use rustc_span::def_id::LocalDefId;
use trust_ir::template::{
    TEMPLATE_BODY_NAME, Template, TemplateError, TemplateHeader, TemplateParam,
    HoleDef, HoleKind, TemplateArg, hole_row_name,
};
use trust_ir::{
    Constant, ConstantG, DialectTy, FatPtrKind, FuncId, FuncTy, FuncTyId, HoleId, Module, ModuleG, ParamId,
    TemplateRef, Ty, TyG, TyId,
};
use trust_ir_build::template::TemplateViolation;

mod callable;

/// Source-only template construction; never metadata or codegen admission.
pub mod pending;

use crate::BodyKind;
use crate::effect_conservation::LedgeredLanes;
use crate::rmeta_entry::{CaptureRefusal, EntryRefusal, StoredTemplate};

/// The dialect namespace of the lane's type sentinels (Trust-reserved).
pub const SENTINEL_NAMESPACE: &str = "trust_template";
/// The dialect version of the lane's type sentinels.
pub const SENTINEL_VERSION: u32 = 1;
/// A type parameter's sentinel name: `param_<p>`.
pub const TYPE_PARAM_SENTINEL_PREFIX: &str = "param_";
/// A hole's sentinel name (step 6.5.2): `hole_<h>`. Only [`embed_template`] spells it in 6.5.1.
pub const TYPE_HOLE_SENTINEL_PREFIX: &str = "hole_";
/// A scalar const parameter's sentinel symbol: `!trust_template_param::<p>`. The leading `!` is
/// trust-ir's reserved-name mark, so no link symbol can collide with it.
pub const CONST_PARAM_SENTINEL_PREFIX: &str = "!trust_template_param::";
/// A const hole's sentinel symbol (step 6.5.2). Only [`embed_template`] spells it in 6.5.1.
pub const CONST_HOLE_SENTINEL_PREFIX: &str = "!trust_template_hole::";

/// One template parameter, as the header will carry it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LaneParam {
    /// A type parameter: `TemplateParam::Type`.
    Type,
    /// A scalar const parameter of this trust-ir type: `TemplateParam::Const { ty }`.
    Const(Ty),
}

/// A callee's complete declared signature and stable Rust host identity. It is
/// unresolved only at level S; instantiation must answer it with a real body or
/// authentic external declaration at exactly this substituted signature.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CalleeHole {
    /// Position in the common, dense Type/Callee hole namespace.
    pub id: HoleId,
    pub decl: FuncId,
    pub key: crate::template_key::HoleKey,
    pub signature: FuncTy,
    /// Rust parameter index and its owner-bound level-S argument, first use order.
    pub dependencies: Vec<(u32, TemplateArg)>,
}

/// A type requested from an actual Rust source type. Its opaque contract permits
/// transport only; it supplies no field, width, layout or destructor judgement.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypeHole {
    pub id: HoleId,
    pub key: crate::template_key::HoleKey,
    pub dependencies: Vec<(u32, TemplateArg)>,
}

/// Everything about one template lowering that [`abstract_template`] and the template builder's
/// extraction check read besides the sentinel module and its callee ledger. Lifetime-free: it
/// waits in the session registry until metadata is encoded.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct LaneFacts {
    /// Stable definition that owns every Rust parameter index in the keys.
    pub owner: Option<crate::template_key::StableDef>,
    /// Lane order -> original Rust generic index, retained for independent binding checks.
    pub parameter_indices: Vec<u32>,
    pub callee_holes: Vec<CalleeHole>,
    pub type_holes: Vec<TypeHole>,
    /// The template parameters, in lane order (`ParamId(i)` is `params[i]`).
    pub params: Vec<LaneParam>,
    /// The struct rows (`StructId` indices) registered from an ADT whose generic args mention a
    /// parameter. Any one of them, with or without a visible sentinel, is
    /// `template-unsupported(parameter-dependent ADT row (6.5.2))`; a sentinel in any other
    /// ground row is `invalid`.
    pub param_adt_structs: BTreeSet<u32>,
    /// The same, for enum rows (`EnumId` indices).
    pub param_adt_enums: BTreeSet<u32>,
    /// `ir_census`'s `degraded` input as the lowering ledgered it (`StructId` indices).
    pub degraded_structs: Vec<u32>,
    /// `ir_census`'s `lanes` input as the lowering ledgered it.
    pub lanes: LedgeredLanes,
}

/// The lane state a template-mode lowering carries (`LowerCx::template`).
pub(crate) struct TemplateLane<'tcx> {
    pub(crate) owner: Option<crate::template_key::StableDef>,
    pub(crate) callee_holes: Vec<CalleeHole>,
    pub(crate) type_holes: Vec<TypeHole>,
    /// Every template parameter: rustc's `ParamTy`/`ParamConst` index and its lane spelling.
    pub(crate) params: Vec<(u32, LaneParam)>,
    /// rustc's parameter index -> the template's `ParamId`.
    pub(crate) index_map: BTreeMap<u32, ParamId>,
    /// The lane's own refusals, `(where, what)`: each becomes `template-unsupported(<what>)`,
    /// never a `Lowered::unsupported` tag, so the mainline coverage counts never move.
    pub(crate) refusals: Vec<(String, &'static str)>,
    /// See [`LaneFacts::param_adt_structs`]; filled from the lowering's ADT ledgers.
    pub(crate) param_adt_structs: BTreeSet<u32>,
    /// See [`LaneFacts::param_adt_enums`].
    pub(crate) param_adt_enums: BTreeSet<u32>,
    /// See [`LaneFacts::degraded_structs`]; filled when the lowering finishes.
    pub(crate) degraded_structs: Vec<u32>,
    /// See [`LaneFacts::lanes`]; filled when the lowering finishes.
    pub(crate) lanes: LedgeredLanes,
    /// The definition's own environment (`TypingEnv::non_body_analysis`), in which the
    /// pointer-metadata rule asks whether a parameter is `Sized`.
    pub(crate) typing_env: ty::TypingEnv<'tcx>,
}

impl<'tcx> TemplateLane<'tcx> {
    /// A lane over `params` (rustc index, spelling), in lane order.
    pub(crate) fn new(typing_env: ty::TypingEnv<'tcx>, params: Vec<(u32, LaneParam)>) -> Self {
        let index_map = params
            .iter()
            .enumerate()
            .map(|(p, (index, _))| (*index, ParamId::new(p as u32)))
            .collect();
        TemplateLane {
            owner: None,
            callee_holes: Vec::new(),
            type_holes: Vec::new(),
            params,
            index_map,
            refusals: Vec::new(),
            param_adt_structs: BTreeSet::new(),
            param_adt_enums: BTreeSet::new(),
            degraded_structs: Vec::new(),
            lanes: LedgeredLanes::default(),
            typing_env,
        }
    }

    /// The template `ParamId` of rustc's TYPE parameter `index`, if the lane carries it as one.
    pub(crate) fn type_param(&self, index: u32) -> Option<ParamId> {
        let p = *self.index_map.get(&index)?;
        matches!(self.params.get(p.as_usize()), Some((_, LaneParam::Type))).then_some(p)
    }

    /// The template `ParamId` and scalar type of rustc's CONST parameter `index`, if the lane
    /// carries it as one.
    pub(crate) fn const_param(&self, index: u32) -> Option<(ParamId, Ty)> {
        let p = *self.index_map.get(&index)?;
        match self.params.get(p.as_usize()) {
            Some((_, LaneParam::Const(ty))) => Some((p, ty.clone())),
            _ => None,
        }
    }

    /// Record a lane refusal (`template-unsupported(<what>)`).
    pub(crate) fn refuse(&mut self, at: String, what: &'static str) {
        self.refusals.push((at, what));
    }

    /// The lane's facts, lifetime-free.
    pub(crate) fn facts(&self) -> LaneFacts {
        LaneFacts {
            owner: self.owner,
            parameter_indices: self.params.iter().map(|(i, _)| *i).collect(),
            callee_holes: self.callee_holes.clone(),
            type_holes: self.type_holes.clone(),
            params: self.params.iter().map(|(_, p)| p.clone()).collect(),
            param_adt_structs: self.param_adt_structs.clone(),
            param_adt_enums: self.param_adt_enums.clone(),
            degraded_structs: self.degraded_structs.clone(),
            lanes: self.lanes,
        }
    }

    /// The lane refusals' labels, sorted and deduplicated.
    pub(crate) fn refusal_labels(&self) -> Vec<String> {
        let mut labels: Vec<&str> = self.refusals.iter().map(|(_, what)| *what).collect();
        labels.sort_unstable();
        labels.dedup();
        labels.into_iter().map(str::to_string).collect()
    }
}

// =============================================================================================
// The sentinels
// =============================================================================================

/// The sentinel type of template parameter `p`.
pub fn type_param_sentinel(p: u32) -> Ty {
    Ty::Dialect(Box::new(DialectTy::new(
        SENTINEL_NAMESPACE,
        format!("{TYPE_PARAM_SENTINEL_PREFIX}{p}"),
        SENTINEL_VERSION,
    )))
}

/// The sentinel constant of scalar const parameter `p` (the root of an `Inst::Const`).
pub fn const_param_sentinel(p: u32) -> Constant {
    Constant::SymbolAddr { symbol: format!("{CONST_PARAM_SENTINEL_PREFIX}{p}"), addend: 0 }
}

/// What a dialect type or a symbol address is, to the lane.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Sentinel {
    /// The sentinel of parameter `p`.
    Param(u32),
    /// A type hole minted from a checked owner-bound Rust key.
    Hole(u32),
    /// The lane's namespace or prefix, but not a well-formed parameter sentinel.
    Malformed,
    /// Not the lane's at all.
    Foreign,
}

/// The decimal index after `prefix` in `name`, if `name` is exactly `prefix<digits>` with no
/// leading zero (one spelling per index).
fn sentinel_index(name: &str, prefix: &str) -> Option<u32> {
    let digits = name.strip_prefix(prefix)?;
    if digits.is_empty()
        || !digits.bytes().all(|b| b.is_ascii_digit())
        || (digits.len() > 1 && digits.starts_with('0'))
    {
        return None;
    }
    digits.parse().ok()
}

fn dialect_sentinel(d: &DialectTy) -> Sentinel {
    if d.namespace != SENTINEL_NAMESPACE {
        return Sentinel::Foreign;
    }
    if d.version != SENTINEL_VERSION { return Sentinel::Malformed; }
    if let Some(p) = sentinel_index(&d.name, TYPE_PARAM_SENTINEL_PREFIX) {
        Sentinel::Param(p)
    } else if let Some(h) = sentinel_index(&d.name, TYPE_HOLE_SENTINEL_PREFIX) {
        Sentinel::Hole(h)
    } else { Sentinel::Malformed }
}

fn symbol_sentinel(c: &Constant) -> Sentinel {
    let ConstantG::SymbolAddr { symbol, addend } = c else {
        return Sentinel::Foreign;
    };
    if !symbol.starts_with(CONST_PARAM_SENTINEL_PREFIX) {
        return Sentinel::Foreign;
    }
    match sentinel_index(symbol, CONST_PARAM_SENTINEL_PREFIX) {
        Some(p) if *addend == 0 => Sentinel::Param(p),
        _ => Sentinel::Malformed,
    }
}

/// Does `c` (the root or any child) spell a const sentinel or anything in the lane's const
/// sentinel space?
fn constant_mentions_sentinel(c: &Constant) -> bool {
    match c {
        ConstantG::SymbolAddr { symbol, .. } => symbol.starts_with(CONST_PARAM_SENTINEL_PREFIX),
        ConstantG::Aggregate(children)
        | ConstantG::Array(children)
        | ConstantG::Vector(children)
        | ConstantG::Sequence(children)
        | ConstantG::Set(children) => children.iter().any(constant_mentions_sentinel),
        ConstantG::Closure { captures, .. } => captures.iter().any(constant_mentions_sentinel),
        ConstantG::Record(fields) => fields.iter().any(|(_, c)| constant_mentions_sentinel(c)),
        ConstantG::Splat { elem, .. } => constant_mentions_sentinel(elem),
        ConstantG::Int(_)
        | ConstantG::U128(_)
        | ConstantG::Bytes { .. }
        | ConstantG::Float(_)
        | ConstantG::Bool(_)
        | ConstantG::FnDef(_)
        | ConstantG::PhantomData
        | ConstantG::Uninit
        // A trust-ir v70 weight names its bytes by digest, never by symbol, so it spells no
        // sentinel. It is refused by name on its own (`constant_names_tensor_blob`).
        | ConstantG::TensorBlob { .. } => false,
        ConstantG::Ext(never) => match *never {},
    }
}

/// The name of a trust-ir v67-v69 tensor instruction, or `None` for any other instruction.
fn tensor_inst_name(inst: &trust_ir::Inst) -> Option<&'static str> {
    use trust_ir::Inst;
    Some(match inst {
        Inst::TensorContract { .. } => "TensorContract",
        Inst::TensorMap { .. } => "TensorMap",
        Inst::TensorReduce { .. } => "TensorReduce",
        Inst::TensorView { .. } => "TensorView",
        Inst::TensorGather { .. } => "TensorGather",
        Inst::TensorScatter { .. } => "TensorScatter",
        _ => return None,
    })
}

/// Does `c` (the root or any child) carry a trust-ir v70 `Constant::TensorBlob`? A template
/// carries no blob table (the escape check requires it empty), so such a constant could only
/// dangle: the lane refuses it by name wherever it meets one.
fn constant_names_tensor_blob(c: &Constant) -> bool {
    let mut found = false;
    c.visit_constants(|child| found |= matches!(child, ConstantG::TensorBlob { .. }));
    found
}

// =============================================================================================
// The escape check, the level map, the body row: `abstract_template`
// =============================================================================================

fn invalid(what: String) -> EntryRefusal {
    EntryRefusal::Invalid(what)
}

/// Does a type mention the lane's sentinel space, directly or through a `types` / `func_types`
/// row? Memoized per row; a row on the current path contributes nothing more (cycles end).
///
/// Every row a type names is followed, `FatPtr(Slice(row))`'s element row included. trust-ir's
/// own row walk (`TyG::for_each_row`, at the pin `3d315a17`) does not follow a slice's element
/// row, so amendment S's T2 and T5 (`GenericRows`, `ground_ty_names_generic_row`) do not see a
/// parameter that reaches a ground table or a declaration only as a slice element; this walk is
/// what refuses those (INC6.5-SENTINEL, the 2026-10-13 amendment).
struct SentinelWalk<'m> {
    types: &'m [Ty],
    func_types: &'m [trust_ir::FuncTy],
    ty_memo: BTreeMap<u32, bool>,
    fty_memo: BTreeMap<u32, bool>,
    on_path_ty: BTreeSet<u32>,
    on_path_fty: BTreeSet<u32>,
    /// Whether the walk met a trust-ir v67 `Ty::Tensor`. The escape check refuses it by name:
    /// the tables this walk reads are cloned unmapped, where `abstract_ty`'s refusal of a
    /// tensor does not reach.
    saw_tensor: bool,
}

impl<'m> SentinelWalk<'m> {
    fn new(module: &'m Module) -> Self {
        SentinelWalk {
            types: &module.types,
            func_types: &module.func_types,
            ty_memo: BTreeMap::new(),
            fty_memo: BTreeMap::new(),
            on_path_ty: BTreeSet::new(),
            on_path_fty: BTreeSet::new(),
            saw_tensor: false,
        }
    }

    fn ty(&mut self, ty: &Ty) -> bool {
        match ty {
            TyG::Dialect(d) => d.namespace == SENTINEL_NAMESPACE,
            TyG::Vector(inner, _)
            | TyG::Ref(inner)
            | TyG::RefMut(inner)
            | TyG::PtrConst(inner)
            | TyG::PtrMut(inner)
            | TyG::Rc(inner) => self.ty(inner),
            TyG::Tuple(elems) => elems.iter().any(|e| self.ty(e)),
            // A tensor's element is a type like any other (a sentinel can hide in it), and the
            // tensor itself is recorded for the escape check's by-name refusal.
            TyG::Tensor(elem, _) => {
                self.saw_tensor = true;
                self.ty(elem)
            }
            TyG::Array(row, _)
            | TyG::Set(row, _)
            | TyG::Sequence(row)
            | TyG::Refine(row, _)
            | TyG::FatPtr(FatPtrKind::Slice(row)) => self.ty_row(*row),
            TyG::Func(row) => self.func_ty_row(*row),
            // No row: a string, a trait object's id, or a container whose tail is not recorded.
            TyG::FatPtr(
                FatPtrKind::Str
                | FatPtrKind::TraitObject { .. }
                | FatPtrKind::ContainerLen
                | FatPtrKind::ContainerVtable,
            ) => false,
            TyG::I8
            | TyG::I16
            | TyG::I32
            | TyG::I64
            | TyG::I128
            | TyG::U8
            | TyG::U16
            | TyG::U32
            | TyG::U64
            | TyG::U128
            | TyG::Isize
            | TyG::Usize
            | TyG::Char
            | TyG::Error
            | TyG::F16
            | TyG::F32
            | TyG::F64
            | TyG::Bool
            | TyG::Ptr
            | TyG::Unit
            | TyG::Never
            // Geometry has no type children, row ids or generic sentinels.
            | TyG::Storage(_)
            // A struct, enum, record or closure row is checked as a row of its own table.
            | TyG::Struct(_)
            | TyG::Enum(_)
            | TyG::Record(_)
            | TyG::Closure(_)
            | TyG::Handle(_) => false,
            TyG::Ext(never) => match *never {},
        }
    }

    fn ty_row(&mut self, row: TyId) -> bool {
        let key = row.index();
        if let Some(found) = self.ty_memo.get(&key) {
            return *found;
        }
        if !self.on_path_ty.insert(key) {
            return false;
        }
        let found = match self.types.get(row.as_usize()) {
            Some(ty) => self.ty(ty),
            None => false,
        };
        self.on_path_ty.remove(&key);
        self.ty_memo.insert(key, found);
        found
    }

    fn func_ty_row(&mut self, row: FuncTyId) -> bool {
        let key = row.index();
        if let Some(found) = self.fty_memo.get(&key) {
            return *found;
        }
        if !self.on_path_fty.insert(key) {
            return false;
        }
        let found = match self.func_types.get(row.as_usize()) {
            Some(signature) => {
                signature.params.iter().chain(&signature.returns).any(|t| self.ty(t))
            }
            None => false,
        };
        self.on_path_fty.remove(&key);
        self.fty_memo.insert(key, found);
        found
    }
}

/// THE ESCAPE CHECK (INC6.5-SENTINEL): no sentinel may sit where the level map does not reach,
/// and no row may be parameter-dependent where 6.5.1 has no rule for it.
///
/// `ModuleG` is destructured EXHAUSTIVELY, with no `..`, so a new trust-ir table does not compile
/// here until it is classified (pinned by `the_escape_check_destructures_every_module_table`).
/// The level map maps `functions`, `globals` (their types), `func_types` and `types`; every other
/// table is CLONED unmapped, so a sentinel in one would survive as a level-R dialect type that
/// no template rule names. Of those, the typed tables are walked here; the proof tables,
/// `spec_modules`, `imports` and `completeness` are T7's (any content is refused there); and
/// `universes`, `predicates` and `closure_layouts` (trust-ir wire v58), which nothing in amendment
/// S checks, must be empty, as must `blobs` (wire v70). Every trust-ir v67-v70 tensor construct
/// (a `Ty::Tensor`, a tensor instruction, a `Constant::TensorBlob`) is refused by name, here or
/// in the level map: no 6.5.1 rule carries one. A struct or enum row's nominal `origin` (also v58) carries no type, so
/// no sentinel can hide in it, but it is a MONOMORPHIC identity (trust-ir's `TypeOrigin` keys a
/// definition on its concrete arguments) that the level map clones unread: a template's row must
/// carry none (the producer stamps none today).
///
/// Two rules read MAPPED rows (the 2026-10-13 amendment of INC6.5-SENTINEL):
///
/// * a declaration's signature (every function but the body) and a global's type name no
///   parameter: amendment S's T2 makes such a row a hole row, 6.5.1 has no hole, and trust-ir's T2
///   does not see a parameter that reaches the row only as a slice element ([`SentinelWalk`]), so
///   the lane refuses it here, `invalid` as T2 classes it;
/// * EVERY struct or enum row registered from an ADT whose generic args mention a parameter
///   (`LaneFacts::param_adt_structs`/`param_adt_enums`) is `template-unsupported(parameter-
///   dependent ADT row (6.5.2))`, whether or not a sentinel is visible in it. A generic row with
///   no visible sentinel (`Option<&T>` is `enum { None, Some(ptr) }` with no layout) is still
///   parameter-dependent: its layout, niche and field offsets are the instance's (plan §0.14).
fn escape_check(sentinel: &Module, facts: &LaneFacts) -> Result<(), EntryRefusal> {
    let ModuleG {
        // Not typed.
        name: _,
        // Mapped by the level map (the constant map checks every root it is handed); every
        // declaration's signature row WALKED below.
        functions,
        // WALKED below.
        structs,
        enums,
        records,
        closure_types,
        // Types mapped by the level map and WALKED below; initializers and names WALKED below.
        globals,
        // Mapped by the level map; read below only through rows a ground table names.
        func_types: _,
        types: _,
        // T7's: any content refuses the template there.
        proof_obligations: _,
        proof_certificates: _,
        obligation_diagnostics: _,
        spec_modules: _,
        imports: _,
        completeness: _,
        global_asm: _,
        // Not typed.
        target_info: _,
        files: _,
        // Nothing in amendment S checks them: required EMPTY below.
        universes,
        predicates,
        // WALKED below.
        tuple_layouts,
        drop_glue,
        // Not typed (closure-type ids and byte offsets), and nothing in amendment S checks it
        // (trust-ir wire v58 postdates the amendment): required EMPTY below.
        closure_layouts,
        // Not typed (content-addressed tensor weight bytes), and nothing in amendment S checks
        // it (trust-ir wire v70 postdates the amendment): required EMPTY below.
        blobs,
    } = sentinel;
    if !universes.is_empty() || !predicates.is_empty() {
        return Err(EntryRefusal::TemplateUnsupported(
            "universes or predicates in a template".to_string(),
        ));
    }
    if !closure_layouts.is_empty() {
        return Err(EntryRefusal::TemplateUnsupported("closure layouts in a template".to_string()));
    }
    if !blobs.is_empty() {
        return Err(EntryRefusal::TemplateUnsupported(
            "tensor weight blobs in a template".to_string(),
        ));
    }
    // trust-ir v67-v69 tensor instructions, named whatever type they are spelled at (the level
    // map refuses a tensor-typed one through `abstract_ty`): no 6.5.1 rule carries them.
    if let Some(name) = functions
        .iter()
        .flat_map(|f| &f.blocks)
        .flat_map(|b| &b.body)
        .find_map(|node| tensor_inst_name(&node.inst))
    {
        return Err(EntryRefusal::TemplateUnsupported(format!(
            "a tensor instruction `{name}` in a template"
        )));
    }
    if structs.iter().any(|row| row.origin.is_some())
        || enums.iter().any(|row| row.origin.is_some())
    {
        return Err(EntryRefusal::TemplateUnsupported(
            "a nominal type origin in a template".to_string(),
        ));
    }
    let mut walk = SentinelWalk::new(sentinel);
    let mut first_invalid: Option<String> = None;
    let mut found_invalid = |what: String| {
        if first_invalid.is_none() {
            first_invalid = Some(what);
        }
    };
    for (i, row) in structs.iter().enumerate() {
        if row.fields.iter().any(|f| walk.ty(&f.ty))
            && !facts.param_adt_structs.contains(&row.id.index())
        {
            found_invalid(format!("sentinel in ground table structs row {i}"));
        }
    }
    for (i, row) in enums.iter().enumerate() {
        if row.variants.iter().any(|v| v.fields.iter().any(|t| walk.ty(t)))
            && !facts.param_adt_enums.contains(&row.id.index())
        {
            found_invalid(format!("sentinel in ground table enums row {i}"));
        }
    }
    for (i, row) in records.iter().enumerate() {
        if row.fields.iter().any(|f| walk.ty(&f.ty)) {
            found_invalid(format!("sentinel in ground table records row {i}"));
        }
    }
    for (i, row) in closure_types.iter().enumerate() {
        if walk.func_ty_row(row.func) || row.captures.iter().any(|t| walk.ty(t)) {
            found_invalid(format!("sentinel in ground table closure_types row {i}"));
        }
    }
    for (i, row) in tuple_layouts.iter().enumerate() {
        if walk.ty_row(row.tuple_type) {
            found_invalid(format!("sentinel in ground table tuple_layouts row {i}"));
        }
    }
    for (i, row) in drop_glue.iter().enumerate() {
        if walk.ty(&row.ty) {
            found_invalid(format!("sentinel in ground table drop_glue row {i}"));
        }
    }
    for (i, function) in functions.iter().enumerate().skip(1) {
        if walk.func_ty_row(function.ty) {
            let hole = facts.callee_holes.iter().find(|h| h.decl == function.id);
            if !hole.is_some_and(|row| {
                function.name == hole_row_name(row.id)
                    && sentinel.func_types.get(function.ty.as_usize()) == Some(&row.signature)
            }) {
                found_invalid(format!("sentinel in the signature of unkeyed declaration row {i}"));
            }
        }
    }
    for (i, global) in globals.iter().enumerate() {
        if walk.ty(&global.ty) {
            found_invalid(format!(
                "sentinel in the type of global row {i} (T2: no hole row in 6.5.1)"
            ));
        }
        if global.name.starts_with(CONST_PARAM_SENTINEL_PREFIX) {
            found_invalid(format!("sentinel as the name of global row {i} (a GlobalAddr target)"));
        }
        if global.initializer.as_ref().is_some_and(constant_mentions_sentinel) {
            found_invalid(format!("sentinel in the initializer of global row {i}"));
        }
    }
    if let Some(what) = first_invalid {
        return Err(invalid(what));
    }
    // trust-ir v67-v70 tensors, in the tables the level map clones unmapped (a mapped one is
    // `abstract_ty`'s and `abstract_root_const`'s): no 6.5.1 rule carries them.
    if walk.saw_tensor {
        return Err(EntryRefusal::TemplateUnsupported(
            "a tensor type in a template table".to_string(),
        ));
    }
    if globals.iter().any(|g| g.initializer.as_ref().is_some_and(constant_names_tensor_blob)) {
        return Err(EntryRefusal::TemplateUnsupported(
            "a tensor weight blob in a template global initializer".to_string(),
        ));
    }
    if !facts.param_adt_structs.is_empty() || !facts.param_adt_enums.is_empty() {
        return Err(EntryRefusal::TemplateUnsupported(
            "parameter-dependent ADT row (6.5.2)".to_string(),
        ));
    }
    Ok(())
}

/// The type half of the level map: TOTAL and EXHAUSTIVE over `TyG`, so a new trust-ir type does
/// not compile here until it is classified. A type parameter's sentinel becomes `Ext(Param)`;
/// every other type is rebuilt unchanged (a row id is an index the template's own tables give
/// meaning to).
fn abstract_ty(ty: &Ty, facts: &LaneFacts) -> Result<TyG<TemplateRef>, EntryRefusal> {
    let map = |inner: &Ty| abstract_ty(inner, facts).map(Box::new);
    Ok(match ty {
        TyG::Dialect(d) => match dialect_sentinel(d) {
            Sentinel::Param(p) => match facts.params.get(p as usize) {
                Some(LaneParam::Type) => TyG::Ext(TemplateRef::Param(ParamId::new(p))),
                Some(LaneParam::Const(_)) => {
                    return Err(invalid(format!(
                        "the sentinel of const parameter ${p} in a type position"
                    )));
                }
                None => {
                    return Err(invalid(format!(
                        "the sentinel of parameter ${p}, which the lane does not carry"
                    )));
                }
            },
            Sentinel::Malformed => {
                return Err(invalid(format!("a malformed type sentinel `{}`", d.name)));
            }
            Sentinel::Hole(h) => {
                let id = HoleId::new(h);
                if !facts.type_holes.iter().any(|hole| hole.id == id) {
                    return Err(invalid(format!("the sentinel of unowned type hole #{h}")));
                }
                TyG::Ext(TemplateRef::Hole(id))
            }
            Sentinel::Foreign => {
                return Err(invalid(format!(
                    "a dialect type the template lane did not mint (`{}`)",
                    d.namespace
                )));
            }
        },
        TyG::Vector(inner, lanes) => TyG::Vector(map(inner)?, *lanes),
        TyG::Ref(inner) => TyG::Ref(map(inner)?),
        TyG::RefMut(inner) => TyG::RefMut(map(inner)?),
        TyG::PtrConst(inner) => TyG::PtrConst(map(inner)?),
        TyG::PtrMut(inner) => TyG::PtrMut(map(inner)?),
        TyG::Rc(inner) => TyG::Rc(map(inner)?),
        TyG::Tuple(elems) => {
            TyG::Tuple(elems.iter().map(|e| abstract_ty(e, facts)).collect::<Result<_, _>>()?)
        }
        TyG::I8 => TyG::I8,
        TyG::I16 => TyG::I16,
        TyG::I32 => TyG::I32,
        TyG::I64 => TyG::I64,
        TyG::I128 => TyG::I128,
        TyG::U8 => TyG::U8,
        TyG::U16 => TyG::U16,
        TyG::U32 => TyG::U32,
        TyG::U64 => TyG::U64,
        TyG::U128 => TyG::U128,
        TyG::Isize => TyG::Isize,
        TyG::Usize => TyG::Usize,
        TyG::Char => TyG::Char,
        TyG::Error => TyG::Error,
        TyG::F16 => TyG::F16,
        TyG::F32 => TyG::F32,
        TyG::F64 => TyG::F64,
        TyG::Bool => TyG::Bool,
        TyG::Ptr => TyG::Ptr,
        TyG::FatPtr(kind) => TyG::FatPtr(*kind),
        TyG::Unit => TyG::Unit,
        TyG::Never => TyG::Never,
        TyG::Struct(id) => TyG::Struct(*id),
        TyG::Array(row, len) => TyG::Array(*row, *len),
        TyG::Enum(id) => TyG::Enum(*id),
        TyG::Func(id) => TyG::Func(*id),
        TyG::Set(row, repr) => TyG::Set(*row, *repr),
        TyG::Sequence(row) => TyG::Sequence(*row),
        TyG::Record(id) => TyG::Record(*id),
        TyG::Closure(id) => TyG::Closure(*id),
        TyG::Refine(row, pred) => TyG::Refine(*row, *pred),
        TyG::Handle(h) => TyG::Handle(h.clone()),
        // This maps type syntax only; storage stays allocation geometry and
        // grants no initialized value or by-value ABI lane.
        TyG::Storage(layout) => TyG::Storage(*layout),
        // A trust-ir v67 tensor: no 6.5.1 rule carries one, so it is refused by name.
        TyG::Tensor(..) => {
            return Err(EntryRefusal::TemplateUnsupported(format!(
                "a tensor type `{ty}` in a template"
            )));
        }
        TyG::Ext(never) => match *never {},
    })
}

/// The constant half of the level map: the ROOT of an `Inst::Const`, at the type it is spelled
/// at. A const parameter's sentinel there, at exactly the parameter's scalar type, becomes
/// `Ext(Param)`; anywhere else (an aggregate's child) a sentinel is `invalid`.
fn abstract_root_const(
    c: &Constant,
    ty: &Ty,
    facts: &LaneFacts,
) -> Result<ConstantG<TemplateRef>, EntryRefusal> {
    match symbol_sentinel(c) {
        Sentinel::Param(p) => match facts.params.get(p as usize) {
            Some(LaneParam::Const(param_ty)) if param_ty == ty => {
                Ok(ConstantG::Ext(TemplateRef::Param(ParamId::new(p))))
            }
            Some(LaneParam::Const(param_ty)) => Err(invalid(format!(
                "the sentinel of const parameter ${p} ({param_ty}) at the type {ty}"
            ))),
            Some(LaneParam::Type) => {
                Err(invalid(format!("the sentinel of type parameter ${p} in a constant position")))
            }
            None => Err(invalid(format!(
                "the sentinel of parameter ${p}, which the lane does not carry"
            ))),
        },
        Sentinel::Malformed | Sentinel::Hole(_) => Err(invalid("a malformed const sentinel".to_string())),
        Sentinel::Foreign if constant_mentions_sentinel(c) => {
            Err(invalid("a const sentinel inside an aggregate constant".to_string()))
        }
        // A trust-ir v70 weight blob names bytes in a table a template does not carry.
        Sentinel::Foreign if constant_names_tensor_blob(c) => Err(EntryRefusal::TemplateUnsupported(
            "a tensor weight blob constant in a template".to_string(),
        )),
        Sentinel::Foreign => Ok(c.embed()),
    }
}

/// Step 2 of [`abstract_template`], the level map alone (the unit tests' teeth build a template
/// with it and [`finish_template`] to measure what the escape check adds).
fn level_map(sentinel: &Module, facts: &LaneFacts) -> Result<ModuleG<TemplateRef>, EntryRefusal> {
    let mut map_ty = |ty: &Ty| abstract_ty(ty, facts);
    let mut map_const = |c: &Constant, ty: &Ty| abstract_root_const(c, ty, facts);
    sentinel.try_map_level(&mut map_ty, &mut map_const)
}

/// The header's parameters, in lane order.
fn header_params(facts: &LaneFacts) -> Vec<TemplateParam> {
    facts
        .params
        .iter()
        .map(|p| match p {
            LaneParam::Type => TemplateParam::Type,
            LaneParam::Const(ty) => TemplateParam::Const { ty: ty.clone() },
        })
        .collect()
}

/// THE ABSTRACTION (INC6.5-SENTINEL): a captured, assembled sentinel module to an amendment-S
/// template. PURE. In order:
///
/// 1. the escape check ([`escape_check`]);
/// 2. the level map: a sentinel type becomes `Ext(Param)` (total over `TyG`), a const sentinel at
///    an `Inst::Const` root becomes `Ext(Param)` (anywhere else it is `invalid`);
/// 3. the body row (`functions[0]`) is named [`TEMPLATE_BODY_NAME`] and every fact the host
///    answers (T7) is left at its default: linkage, visibility, calling convention, attributes,
///    body gate, display path, section, retention and source provenance;
/// 4. the header: `identity`, parameters in lane order, and typed callee holes.
/// The Rust owner and original parameter map remain in the capture facts until
/// metadata has an authenticated framing for them; this stage writes no bytes.
pub fn abstract_template(
    sentinel: &Module,
    facts: &LaneFacts,
    identity: String,
) -> Result<Template, EntryRefusal> {
    escape_check(sentinel, facts)?;
    finish_template(level_map(sentinel, facts)?, facts, identity)
}

/// Steps 3 and 4 of [`abstract_template`]: the body row and the header.
fn finish_template(
    mut module: ModuleG<TemplateRef>,
    facts: &LaneFacts,
    identity: String,
) -> Result<Template, EntryRefusal> {
    let Some(body) = module.functions.first_mut() else {
        return Err(invalid("the sentinel module carries no body".to_string()));
    };
    body.name = TEMPLATE_BODY_NAME.to_string();
    body.linkage = trust_ir::Linkage::default();
    body.visibility = trust_ir::Visibility::default();
    body.calling_conv = trust_ir::CallingConv::default();
    body.attrs = trust_ir::FuncAttrs::default();
    body.body_gate = None;
    body.display_path = None;
    body.section = None;
    body.retained = false;
    body.source_provenance = None;
    let mut holes = vec![None; facts.callee_holes.len() + facts.type_holes.len()];
    let mut declarations = BTreeSet::new();
    for hole in &facts.callee_holes {
        if facts.owner.is_none() || !declarations.insert(hole.decl) {
            return Err(invalid("callee holes have no owner or duplicate declarations".into()));
        }
        check_key_dependencies(facts, &hole.key, &hole.dependencies)?;
        insert_hole(&mut holes, hole.id, HoleDef {
            kind: HoleKind::Callee { decl: hole.decl },
            key: crate::template_key::encode(&hole.key).map_err(|e| invalid(e.to_string()))?,
            args: hole.dependencies.iter().map(|(_, a)| a.clone()).collect(),
        })?;
    }
    for hole in &facts.type_holes {
        if facts.owner.is_none() || !matches!(hole.key, crate::template_key::HoleKey::Type(_)) {
            return Err(invalid("type hole has no owner or has a non-type key".into()));
        }
        check_key_dependencies(facts, &hole.key, &hole.dependencies)?;
        insert_hole(&mut holes, hole.id, HoleDef {
            kind: HoleKind::Type { contract: trust_ir::template::TypeContract::Opaque },
            key: crate::template_key::encode(&hole.key).map_err(|e| invalid(e.to_string()))?,
            args: hole.dependencies.iter().map(|(_, a)| a.clone()).collect(),
        })?;
    }
    let holes = holes.into_iter().map(|h| h.ok_or_else(|| invalid("hole IDs are not dense".into())))
        .collect::<Result<_, _>>()?;
    Ok(Template {
        header: TemplateHeader { identity, params: header_params(facts), holes },
        module,
    })
}

fn insert_hole(holes: &mut [Option<HoleDef>], id: HoleId, hole: HoleDef) -> Result<(), EntryRefusal> {
    let slot = holes.get_mut(id.as_usize()).ok_or_else(|| invalid("hole ID is out of range".into()))?;
    if slot.replace(hole).is_some() { return Err(invalid("duplicate hole ID".into())); }
    Ok(())
}

/// Reconstruct arguments from the original Rust generic positions, independently
/// of the arguments retained by either source-hole producer.
fn check_key_dependencies(
    facts: &LaneFacts,
    key: &crate::template_key::HoleKey,
    dependencies: &[(u32, TemplateArg)],
) -> Result<(), EntryRefusal> {
    if facts.parameter_indices.len() != facts.params.len()
        || facts.parameter_indices.windows(2).any(|w| w[0] >= w[1])
    { return Err(invalid("hole key parameter map is not owner ordered".into())); }
    let indices = crate::template_key::parameters(key).map_err(|e| invalid(e.to_string()))?;
    if indices.is_empty() { return Err(invalid("a source hole has no owner parameter dependency".into())); }
    let mut expected = Vec::with_capacity(indices.len());
    for index in indices {
        let p = facts.parameter_indices.iter().position(|i| *i == index)
            .ok_or_else(|| invalid("hole key parameter is outside its owner map".into()))?;
        let param = TemplateRef::Param(ParamId::new(p as u32));
        let arg = match &facts.params[p] {
            LaneParam::Type => TemplateArg::Type(TyG::Ext(param)),
            LaneParam::Const(ty) => TemplateArg::Const { value: ConstantG::Ext(param), ty: ty.clone() },
        };
        expected.push((index, arg));
    }
    if dependencies != expected {
        return Err(invalid("hole key dependencies differ from the owner-bound arguments".into()));
    }
    Ok(())
}

/// The type sentinel of a template reference.
fn type_sentinel_of(r: &TemplateRef) -> Ty {
    match r {
        TemplateRef::Param(p) => type_param_sentinel(p.index()),
        TemplateRef::Hole(h) => Ty::Dialect(Box::new(DialectTy::new(
            SENTINEL_NAMESPACE,
            format!("{TYPE_HOLE_SENTINEL_PREFIX}{}", h.index()),
            SENTINEL_VERSION,
        ))),
    }
}

/// The const sentinel of a template reference.
fn const_sentinel_of(r: &TemplateRef) -> Constant {
    match r {
        TemplateRef::Param(p) => const_param_sentinel(p.index()),
        TemplateRef::Hole(h) => Constant::SymbolAddr {
            symbol: format!("{CONST_HOLE_SENTINEL_PREFIX}{}", hole_index(*h)),
            addend: 0,
        },
    }
}

fn hole_index(h: HoleId) -> u32 {
    h.index()
}

/// THE EMBEDDING: the inverse of [`abstract_template`]'s level map, every `Ext` back to its
/// sentinel (the body row keeps its reserved name and default facts). Used by the round-trip
/// test. PURE and total.
pub fn embed_template(t: &Template) -> Module {
    let mut map_ty = |ty: &TyG<TemplateRef>| -> Result<Ty, Infallible> {
        ty.try_map_ext::<trust_ir::NoExt, Infallible>(&mut |r| Ok(type_sentinel_of(r)))
    };
    let mut map_const =
        |c: &ConstantG<TemplateRef>, _ty: &TyG<TemplateRef>| -> Result<Constant, Infallible> {
            c.try_map_ext::<trust_ir::NoExt, Infallible>(&mut |r| Ok(const_sentinel_of(r)))
        };
    match t.module.try_map_level(&mut map_ty, &mut map_const) {
        Ok(module) => module,
        Err(never) => match never {},
    }
}

/// THE CLASSES (INC6.5-CLASSES): a template `validate_template` refused, classed by its FIRST
/// violation's VARIANT (no variant carries a rule number, amendment S as landed):
///
/// * `Structure(TemplateUnsupported)`, `Structure(OpaqueOperation)` and
///   `Structure(ParamDependentLiteral)`: `template-unsupported(<display>)` — a construct level S
///   does not carry yet, or an operation that inspects a parameter;
/// * EXCEPT `validate_template`'s no-skolem fallback, which it reports as a `Structure
///   (TemplateUnsupported)` for a template with NO structural violation: recognised by exactly
///   that (`t.structural_violations()` is empty), and `invalid(..)`;
/// * every other `Structure` variant, and every `LevelR` (T6), `invalid(<display>)`.
pub fn template_refusal(t: &Template, v: &[TemplateViolation]) -> EntryRefusal {
    let Some(first) = v.first() else {
        return invalid("validate_template refused with no violation".to_string());
    };
    match first {
        TemplateViolation::Structure(
            e @ (TemplateError::TemplateUnsupported { .. }
            | TemplateError::OpaqueOperation { .. }
            | TemplateError::ParamDependentLiteral { .. }),
        ) => {
            if matches!(e, TemplateError::TemplateUnsupported { .. })
                && t.structural_violations().is_empty()
            {
                invalid(format!("{first}"))
            } else {
                EntryRefusal::TemplateUnsupported(format!("{first}"))
            }
        }
        TemplateViolation::Structure(_) | TemplateViolation::LevelR(_) => {
            invalid(format!("{first}"))
        }
    }
}

// =============================================================================================
// The rustc half: which parameters, which definitions, the capture
// =============================================================================================

/// The trust-ir spelling `map_ty` gives a scalar const parameter's type (`bool`, `char`, an
/// integer; `isize`/`usize` on a 64-bit target only), or `None`: exactly the types
/// `lower_const_param` admits.
fn scalar_const_ty<'tcx>(tcx: TyCtxt<'tcx>, ty: ty::Ty<'tcx>) -> Option<Ty> {
    let pointer_64 = tcx.data_layout.pointer_size().bits() == 64;
    Some(match ty.kind() {
        ty::Bool => Ty::Bool,
        ty::Char => Ty::Char,
        ty::Int(ty::IntTy::I8) => Ty::I8,
        ty::Int(ty::IntTy::I16) => Ty::I16,
        ty::Int(ty::IntTy::I32) => Ty::I32,
        ty::Int(ty::IntTy::I64) => Ty::I64,
        ty::Int(ty::IntTy::I128) => Ty::I128,
        ty::Int(ty::IntTy::Isize) if pointer_64 => Ty::Isize,
        ty::Uint(ty::UintTy::U8) => Ty::U8,
        ty::Uint(ty::UintTy::U16) => Ty::U16,
        ty::Uint(ty::UintTy::U32) => Ty::U32,
        ty::Uint(ty::UintTy::U64) => Ty::U64,
        ty::Uint(ty::UintTy::U128) => Ty::U128,
        ty::Uint(ty::UintTy::Usize) if pointer_64 => Ty::Usize,
        _ => return None,
    })
}

/// The definition's TEMPLATE PARAMETERS, parents first, lifetimes skipped, and rustc's synthetic
/// parameters excluded: a closure's (3), a coroutine's (5), a coroutine-closure's (4) and an
/// inline const block's (1) "junk type parameter defs", whose `def_id` is the owning definition
/// itself (`rustc_hir_analysis::collect::generics_of`). Only those owners are tested: a trait's
/// `Self` also carries its owner's `def_id`, and it IS a template parameter. A const parameter
/// whose type has no scalar spelling is `Err` (a lane refusal).
fn template_params(
    tcx: TyCtxt<'_>,
    def: LocalDefId,
) -> Vec<(u32, Result<LaneParam, &'static str>)> {
    let mut levels = Vec::new();
    let mut owner = Some(def.to_def_id());
    while let Some(o) = owner {
        let generics = tcx.generics_of(o);
        levels.push((o, generics));
        owner = generics.parent;
    }
    let mut out = Vec::new();
    for (owner, generics) in levels.into_iter().rev() {
        let synthetic_owner =
            tcx.def_kind(owner) == DefKind::Closure || crate::is_inline_const(tcx, owner);
        for param in &generics.own_params {
            if synthetic_owner && param.def_id == owner {
                continue;
            }
            match param.kind {
                ty::GenericParamDefKind::Lifetime => {}
                ty::GenericParamDefKind::Type { .. } => {
                    out.push((param.index, Ok(LaneParam::Type)))
                }
                ty::GenericParamDefKind::Const { .. } => {
                    let ty = tcx.type_of(param.def_id).instantiate_identity().skip_normalization();
                    out.push((
                        param.index,
                        scalar_const_ty(tcx, ty)
                            .map(LaneParam::Const)
                            .ok_or("non-scalar const parameter"),
                    ));
                }
            }
        }
    }
    out
}

/// A closure, coroutine, coroutine-closure, synthetic coroutine body or inline const definition,
/// by kind (INC6.5-CLOSURES: none is a template in 6.5).
fn closure_like_kind(tcx: TyCtxt<'_>, def: LocalDefId) -> Option<&'static str> {
    match tcx.def_kind(def) {
        DefKind::Closure => Some(match tcx.hir_node_by_def_id(def) {
            rustc_hir::Node::Expr(&rustc_hir::Expr {
                kind: rustc_hir::ExprKind::Closure(rustc_hir::Closure { kind, .. }),
                ..
            }) => match kind {
                rustc_hir::ClosureKind::Closure => "closure",
                rustc_hir::ClosureKind::Coroutine(_) => "coroutine",
                rustc_hir::ClosureKind::CoroutineClosure(_) => "coroutine-closure",
            },
            _ => "closure",
        }),
        DefKind::SyntheticCoroutineBody => Some("synthetic coroutine"),
        DefKind::AnonConst if crate::is_inline_const(tcx, def.to_def_id()) => Some("inline const"),
        _ => None,
    }
}

/// The body kind, as the mainline lowering classes it.
fn body_kind_of(tcx: TyCtxt<'_>, def: LocalDefId, thir: &Thir<'_>) -> BodyKind {
    match thir.body_type {
        BodyTy::Fn(_) | BodyTy::GlobalAsm(_) => BodyKind::Fn,
        BodyTy::Const(_) => match tcx.def_kind(def) {
            DefKind::Static { .. } => BodyKind::StaticInit,
            _ => BodyKind::ConstInit,
        },
    }
}

/// THE CAPTURE (INC6.5-LANE). Called by `lower_module_from_thir` after the mainline lowering
/// returned. Does nothing unless all hold: `-Ztrust-ir-lower-templates`, this session builds
/// rmeta entries (`rmeta_entry::entries_enabled`), the definition has a template parameter, and
/// its body is a fn body. A closure, coroutine, coroutine-closure, synthetic coroutine body or
/// inline const is recorded BY KIND and not lowered (INC6.5-CLOSURES).
///
/// The capture-time gates run here, in the builder's order, and a refused capture stores only
/// its reason (the precedent of `record_candidate`): the lane's refusals, the producer's
/// not-fully-lowered reasons, then a reachable unsited check (INC6.5-SITES).
pub(crate) fn capture<'tcx>(tcx: TyCtxt<'tcx>, def: LocalDefId, thir: &Thir<'tcx>, root: ExprId) {
    if !tcx.sess.opts.unstable_opts.trust_ir_lower_templates
        || !crate::rmeta_entry::entries_enabled(tcx)
    {
        return;
    }
    // Capture original typed source facts independently of the lowered module.
    crate::effect_conservation::thir_source::record(tcx, def);
    if let Some(stored) = lower_stored(tcx, def, thir, root) {
        crate::rmeta_entry::record_template(tcx, def, stored);
    }
}

/// The actual template lowering shared by metadata storage and pending inspection.
/// This carries source data only; the existing frozen builder decides metadata.
struct SourceCapture<'tcx> {
    body_kind: BodyKind,
    lowered: Result<(crate::Lowered, TemplateLane<'tcx>), CaptureRefusal>,
}

fn lower_stored<'tcx>(
    tcx: TyCtxt<'tcx>, def: LocalDefId, thir: &Thir<'tcx>, root: ExprId,
) -> Option<StoredTemplate> {
    let source = lower_capture(tcx, def, thir, root)?;
    Some(match source.lowered {
        Err(reason) => StoredTemplate::refused(source.body_kind, reason),
        Ok((lowered, lane)) => StoredTemplate::of_lowering(&lowered, &lane),
    })
}

fn lower_capture<'tcx>(
    tcx: TyCtxt<'tcx>, def: LocalDefId, thir: &Thir<'tcx>, root: ExprId,
) -> Option<SourceCapture<'tcx>> {
    let params = template_params(tcx, def);
    let body_kind = body_kind_of(tcx, def, thir);
    if let Some(kind) = closure_like_kind(tcx, def) {
        return Some(SourceCapture {
            body_kind,
            lowered: Err(CaptureRefusal::ClosureKind { kind, generic: !params.is_empty() }),
        });
    }
    if params.is_empty() || !matches!(thir.body_type, BodyTy::Fn(_)) {
        return None;
    }
    let mut refused_params: Vec<(String, &'static str)> = Vec::new();
    let lane_params: Vec<(u32, LaneParam)> = params
        .into_iter()
        .filter_map(|(index, spelled)| match spelled {
            Ok(param) => Some((index, param)),
            Err(what) => {
                refused_params.push((format!("parameter {index}"), what));
                None
            }
        })
        .collect();
    let mut lane = TemplateLane::new(ty::TypingEnv::non_body_analysis(tcx, def), lane_params);
    lane.owner = Some(crate::template_key::rustc::stable_def(tcx, def.to_def_id()));
    lane.refusals.extend(refused_params);
    let (lowered, _drop_refusal, lane) = crate::lower_template(tcx, def, thir, root, lane);
    Some(SourceCapture {
        body_kind,
        lowered: lane.map(|lane| (lowered, lane)).ok_or_else(|| {
            CaptureRefusal::Lane(vec!["the template lane was not returned".to_string()])
        }),
    })
}

#[cfg(test)]
mod tests;
