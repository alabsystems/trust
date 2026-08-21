//! Exact literal TrustIR → temporal-model refinement certificates.
//!
//! This lane closes the gap left by digest-only or short-trace bindings.  A
//! certificate retains the canonical TrustIR module bytes, deterministically
//! lowers every instruction in the validated scalar fragment to Clean's
//! authoritative EvalIR literal, derives `Init` and `Next` directly from
//! `ir_init`/`ir_step`, and kernel-checks universal equalities for every machine
//! state and successor.
//! Replay decodes and re-canonicalizes the exact bytes, regenerates the source,
//! rebuilds a fresh EvalIR + temporal environment, and compares both serialized
//! theorem types and proof terms before checking the stored terms again.
//!
//! Unsupported operational constructs fail closed with concrete extension
//! choices.  Proof/debug/contract metadata remains bound through the canonical
//! module bytes but is intentionally absent from the operational literal.

use std::collections::BTreeSet;
use std::fmt;
use std::sync::OnceLock;

use clean_elab::FileContext;
use clean_kernel::env::Environment;
use clean_kernel::expr::Expr;
use clean_kernel::name::Name;
use clean_kernel::tc::TypeChecker;
use trust_ir::{BinOp, CastOp, Constant, Function, ICmpOp, Inst, Module, Ty, UnOp};

use crate::clean_surface::{
    CLEAN_TEMPORAL_PRELUDE, CleanTemporalCertificateError, checked_theorem,
    elaborate_suffix_with_parser_prelude, elaborate_unit,
};

/// Retired wire schema for the pre-inline-aggregate EvalIR state ABI.
///
/// Version 1 carried a `next_aggregate` invocation field and generated calls to
/// the old aggregate-arena forms of `ir_init` and `IRMachine.mk`. It remains
/// named so replay can reject legacy evidence explicitly; producers never emit
/// it.
pub const LITERAL_REFINEMENT_SCHEMA_V1: &str = "trust.literal-evalir-refinement/v1";

/// Current wire schema for exact literal EvalIR refinement evidence.
pub const LITERAL_REFINEMENT_SCHEMA_V2: &str = "trust.literal-evalir-refinement/v2";

const MAX_MODULE_BYTES: usize = 16 * 1024 * 1024;
const MAX_OPERATIONAL_ITEMS: usize = 65_536;
const MAX_GENERATED_SOURCE_BYTES: usize = 32 * 1024 * 1024;

const THEOREM_NAMES: [&str; 6] = [
    "Trust.LiteralRefinement.artifact_binding",
    "Trust.LiteralRefinement.init_exact",
    "Trust.LiteralRefinement.next_exact",
    "Trust.LiteralRefinement.halted_exact",
    "Trust.LiteralRefinement.initial_running",
    "Trust.LiteralRefinement.first_step_is_in_model",
];

/// Closed-call scalar carried by the v2 wire schema.
///
/// The current proved operational fragment accepts only `Bool`, canonical
/// fixed-width `Int`, and `Unit`. The other variants remain decodable so old v2
/// evidence fails with a precise supported-fragment diagnostic rather than a
/// misleading schema error; they confer no authority.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(rename_all = "snake_case", tag = "kind", deny_unknown_fields)]
pub enum LiteralScalar {
    Undef,
    Bool { value: bool },
    Int { raw: u128 },
    FloatBits { bits: u64 },
    Unit,
    Pointer { address: u64 },
    NullPointer,
    FatPointer { data: u64, metadata: u64 },
    Function { id: u32 },
}

/// Exact closed invocation from which the temporal model's `Init` is derived.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LiteralInvocation {
    pub arguments: Vec<LiteralScalar>,
    /// First address available to `Alloca`; must be beyond every global cell.
    pub next_address: u64,
}

impl LiteralInvocation {
    #[must_use]
    pub fn closed(arguments: Vec<LiteralScalar>, global_count: usize) -> Self {
        Self { arguments, next_address: u64::try_from(global_count).unwrap_or(u64::MAX) }
    }
}

/// One independently replayable Clean theorem artifact.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LiteralRefinementTheorem {
    pub theorem: String,
    pub theorem_type: Vec<u8>,
    pub proof_term: Vec<u8>,
}

/// Exact-input-bound universal refinement evidence.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LiteralRefinementCertificate {
    pub schema: String,
    /// Canonical `trust_ir::binary` bytes, not merely a digest.
    pub module_bytes: Vec<u8>,
    pub function_id: u32,
    pub invocation: LiteralInvocation,
    /// Deterministically generated Clean program, model, and proof source.
    pub clean_source: String,
    /// Fixed, complete theorem set in [`THEOREM_NAMES`] order.
    pub theorems: Vec<LiteralRefinementTheorem>,
}

/// Fail-closed literal-refinement diagnostics.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LiteralRefinementError {
    SchemaMismatch {
        found: String,
    },
    ModuleTooLarge {
        bytes: usize,
        maximum: usize,
    },
    ModuleDecode(String),
    NonCanonicalModule,
    ModuleMismatch,
    FunctionMismatch {
        expected: u32,
        found: u32,
    },
    InvocationMismatch,
    MissingFunction(u32),
    DuplicateFunction(u32),
    DuplicateBlock {
        function: u32,
        block: u32,
    },
    MissingEntryBlock {
        function: u32,
        entry: u32,
    },
    InvocationArity {
        expected: usize,
        found: usize,
    },
    InvalidInvocation(String),
    OperationalItemLimit {
        items: usize,
        maximum: usize,
    },
    GeneratedSourceLimit {
        bytes: usize,
        maximum: usize,
    },
    /// A supported-fragment decline, always accompanied by actionable choices.
    Unsupported {
        path: String,
        construct: String,
        repair: String,
    },
    CleanSpecBuild(String),
    Clean(CleanTemporalCertificateError),
    SourceMismatch,
    TheoremSetMismatch,
    ArtifactMismatch {
        theorem: String,
        field: &'static str,
    },
    MalformedArtifact(String),
    KernelRejected(String),
}

impl fmt::Display for LiteralRefinementError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::SchemaMismatch { found } => {
                write!(formatter, "unsupported literal-refinement schema `{found}`")
            }
            Self::ModuleTooLarge { bytes, maximum } => write!(
                formatter,
                "TrustIR module is {bytes} bytes; literal-refinement limit is {maximum}"
            ),
            Self::ModuleDecode(detail) => write!(formatter, "cannot decode TrustIR module: {detail}"),
            Self::NonCanonicalModule => formatter.write_str(
                "TrustIR bytes are not the canonical binary encoding; decode and re-emit them first",
            ),
            Self::ModuleMismatch => {
                formatter.write_str("literal-refinement certificate is bound to different module bytes")
            }
            Self::FunctionMismatch { expected, found } => write!(
                formatter,
                "literal-refinement function mismatch: expected {expected}, certificate carries {found}"
            ),
            Self::InvocationMismatch => formatter.write_str(
                "literal-refinement certificate is bound to a different closed invocation",
            ),
            Self::MissingFunction(id) => write!(formatter, "TrustIR module has no function id {id}"),
            Self::DuplicateFunction(id) => write!(formatter, "TrustIR module repeats function id {id}"),
            Self::DuplicateBlock { function, block } => {
                write!(formatter, "TrustIR function {function} repeats block id {block}")
            }
            Self::MissingEntryBlock { function, entry } => write!(
                formatter,
                "TrustIR function {function} has no entry block {entry}"
            ),
            Self::InvocationArity { expected, found } => write!(
                formatter,
                "closed invocation has {found} arguments; selected function requires {expected}"
            ),
            Self::InvalidInvocation(detail) => write!(formatter, "invalid closed invocation: {detail}"),
            Self::OperationalItemLimit { items, maximum } => write!(
                formatter,
                "literal program contains {items} operational items; limit is {maximum}; split the module or raise the audited parser-cost bound",
            ),
            Self::GeneratedSourceLimit { bytes, maximum } => write!(
                formatter,
                "generated Clean source is {bytes} bytes; limit is {maximum}; add a kernel binary decoder or partition the module",
            ),
            Self::Unsupported { path, construct, repair } => write!(
                formatter,
                "literal refinement declines {construct} at {path}; repair options: {repair}"
            ),
            Self::CleanSpecBuild(detail) => write!(formatter, "cannot build Clean EvalIR spec: {detail}"),
            Self::Clean(error) => write!(formatter, "Clean literal-refinement check failed: {error}"),
            Self::SourceMismatch => formatter.write_str(
                "stored Clean refinement source differs from regeneration of the exact TrustIR bytes",
            ),
            Self::TheoremSetMismatch => formatter.write_str(
                "literal-refinement certificate does not carry the complete ordered theorem set",
            ),
            Self::ArtifactMismatch { theorem, field } => {
                write!(formatter, "{field} for `{theorem}` differs from fresh elaboration")
            }
            Self::MalformedArtifact(detail) => write!(formatter, "malformed refinement artifact: {detail}"),
            Self::KernelRejected(detail) => {
                write!(formatter, "Clean kernel rejected stored refinement proof: {detail}")
            }
        }
    }
}

impl std::error::Error for LiteralRefinementError {}

impl From<CleanTemporalCertificateError> for LiteralRefinementError {
    fn from(value: CleanTemporalCertificateError) -> Self {
        Self::Clean(value)
    }
}

fn unsupported(
    path: impl Into<String>,
    construct: impl Into<String>,
    repair: impl Into<String>,
) -> LiteralRefinementError {
    LiteralRefinementError::Unsupported {
        path: path.into(),
        construct: construct.into(),
        repair: repair.into(),
    }
}

fn clean_bool(value: bool) -> &'static str {
    if value { "Bool.true" } else { "Bool.false" }
}

fn clean_list(element_type: &str, values: impl IntoIterator<Item = String>) -> String {
    let values = values.into_iter().collect::<Vec<_>>();
    values.into_iter().rev().fold(format!("IRList.nil {element_type}"), |tail, value| {
        format!("IRList.cons {element_type} ({value}) ({tail})")
    })
}

fn id_list(values: &[trust_ir::ValueId]) -> String {
    clean_list("Nat", values.iter().map(|value| value.index().to_string()))
}

fn int_width(ty: &Ty, path: &str) -> Result<u32, LiteralRefinementError> {
    let width = match ty {
        Ty::I8 | Ty::U8 => 8,
        Ty::I16 | Ty::U16 => 16,
        Ty::I32 | Ty::U32 | Ty::Char => 32,
        Ty::I64 | Ty::U64 => 64,
        Ty::I128 | Ty::U128 => 128,
        other => {
            return Err(unsupported(
                path,
                format!("non-integer type {other:?}"),
                "use an integer-typed constant or extend the literal constant translator for this representation",
            ));
        }
    };
    Ok(width)
}

fn ty_expr(ty: &Ty, path: &str) -> Result<String, LiteralRefinementError> {
    Ok(match ty {
        Ty::I8 => "IRTy.int_ 8".to_owned(),
        Ty::I16 => "IRTy.int_ 16".to_owned(),
        Ty::I32 => "IRTy.int_ 32".to_owned(),
        Ty::I64 => "IRTy.int_ 64".to_owned(),
        Ty::I128 => "IRTy.int_ 128".to_owned(),
        Ty::U8 => "IRTy.uint_ 8".to_owned(),
        Ty::U16 => "IRTy.uint_ 16".to_owned(),
        Ty::U32 | Ty::Char => "IRTy.uint_ 32".to_owned(),
        Ty::U64 => "IRTy.uint_ 64".to_owned(),
        Ty::U128 => "IRTy.uint_ 128".to_owned(),
        Ty::Bool => "IRTy.bool_".to_owned(),
        Ty::Unit => "IRTy.unit_".to_owned(),
        Ty::Never => "IRTy.never_".to_owned(),
        Ty::F16
        | Ty::F32
        | Ty::F64
        | Ty::Isize
        | Ty::Usize
        | Ty::Refine(_, _)
        | Ty::Ptr
        | Ty::FatPtr(_)
        | Ty::Struct(_)
        | Ty::Enum(_)
        | Ty::Func(_)
        | Ty::Tuple(_)
        | Ty::Array(_, _)
        | Ty::Ref(_)
        | Ty::RefMut(_)
        | Ty::PtrConst(_)
        | Ty::PtrMut(_)
        | Ty::Rc(_)
        | Ty::Vector(_, _)
        | Ty::Set(_, _)
        | Ty::Sequence(_)
        | Ty::Record(_)
        | Ty::Closure(_) => {
            return Err(unsupported(
                path,
                format!("type outside the exact scalar operational fragment: {ty:?}"),
                "lower to Bool, fixed-width integer, Unit, or Never, or supply a checked TrustIR-to-EvalIR adequacy theorem for this carrier",
            ));
        }
        Ty::Error => {
            return Err(unsupported(
                path,
                "producer-internal Ty::Error",
                "repair the producer typing hole; Ty::Error is not wire-legal program semantics",
            ));
        }
    })
}

fn constant_expr(ty: &Ty, value: &Constant, path: &str) -> Result<String, LiteralRefinementError> {
    match (ty, value) {
        (Ty::Ptr, Constant::Int(0)) => Ok("IRConst.null_".to_owned()),
        (integer_ty, Constant::Int(value))
            if matches!(
                integer_ty,
                Ty::I8
                    | Ty::I16
                    | Ty::I32
                    | Ty::I64
                    | Ty::I128
                    | Ty::U8
                    | Ty::U16
                    | Ty::U32
                    | Ty::U64
                    | Ty::U128
                    | Ty::Char
            ) =>
        {
            let width = int_width(integer_ty, path)?;
            let mask = if width == 128 { u128::MAX } else { (1_u128 << width) - 1 };
            Ok(format!("IRConst.int_ {}", (*value as u128) & mask))
        }
        (Ty::U128, Constant::U128(value)) => Ok(format!("IRConst.int_ {value}")),
        (Ty::Bool, Constant::Bool(value)) => Ok(format!("IRConst.bool_ {}", clean_bool(*value))),
        (Ty::F64, Constant::Float(value)) => Ok(format!("IRConst.float_ {}", value.to_bits())),
        (Ty::F32, Constant::Float(value)) => {
            Ok(format!("IRConst.float_ {}", (*value as f32).to_bits()))
        }
        (Ty::F16, Constant::Float(_)) => Err(unsupported(
            path,
            "F16 constant conversion",
            "add the reference interpreter's exact f64→binary16 rounding routine as a shared primitive, or emit the canonical 16-bit payload upstream",
        )),
        (Ty::Unit, Constant::PhantomData) => Ok("IRConst.unit_".to_owned()),
        (Ty::Func(_), Constant::FnDef(function)) => {
            Ok(format!("IRConst.func_ {}", function.index()))
        }
        (_, Constant::PhantomData) => Err(unsupported(
            path,
            "non-unit PhantomData constant",
            "lower its exact representation in EvalIR, or restrict PhantomData to Ty::Unit before certification",
        )),
        (
            _,
            Constant::Bytes { .. }
            | Constant::Aggregate(_)
            | Constant::Array(_)
            | Constant::Vector(_)
            | Constant::Sequence(_)
            | Constant::Set(_)
            | Constant::Record(_)
            | Constant::Closure { .. }
            | Constant::SymbolAddr { .. },
        ) => Err(unsupported(
            path,
            format!("aggregate/relocatable constant {value:?}"),
            "lower the constant into typed scalar globals plus arena construction with a proved layout bridge, or extend IRConst with an exact byte/layout carrier",
        )),
        _ => Err(unsupported(
            path,
            format!("constant {value:?} at type {ty:?}"),
            "repair the TrustIR constant/type mismatch or add an exact typed constant case to EvalIR and its differential suite",
        )),
    }
}

/// `None` for operators EvalIR's `IRBinOp` does not model. The boolean
/// 0/1-carrier connectives are deliberately NOT mapped onto
/// `IRBinOp.and_`/`or_`/`xor_`: `semIntBinOp` denotes those through the opaque
/// integer carrier, which is exactly the misdenotation `trust_ir::BinOp::BAnd`
/// exists to rule out.
fn binop_expr(op: BinOp) -> Option<&'static str> {
    match op {
        BinOp::BAnd | BinOp::BOr | BinOp::BXor => return None,
        BinOp::Add => Some("IRBinOp.add"),
        BinOp::Sub => Some("IRBinOp.sub"),
        BinOp::Mul => Some("IRBinOp.mul"),
        BinOp::UDiv => Some("IRBinOp.udiv"),
        BinOp::SDiv => Some("IRBinOp.sdiv"),
        BinOp::URem => Some("IRBinOp.urem"),
        BinOp::SRem => Some("IRBinOp.srem"),
        BinOp::FAdd => Some("IRBinOp.fadd"),
        BinOp::FSub => Some("IRBinOp.fsub"),
        BinOp::FMul => Some("IRBinOp.fmul"),
        BinOp::FDiv => Some("IRBinOp.fdiv"),
        BinOp::FRem => Some("IRBinOp.frem"),
        BinOp::FMin => Some("IRBinOp.fmin"),
        BinOp::FMax => Some("IRBinOp.fmax"),
        BinOp::And => Some("IRBinOp.and_"),
        BinOp::Or => Some("IRBinOp.or_"),
        BinOp::Xor => Some("IRBinOp.xor_"),
        BinOp::Shl => Some("IRBinOp.shl"),
        BinOp::LShr => Some("IRBinOp.lshr"),
        BinOp::AShr => Some("IRBinOp.ashr"),
    }
}

fn unop_expr(op: UnOp) -> &'static str {
    match op {
        UnOp::Neg => "IRUnOp.neg",
        UnOp::FNeg => "IRUnOp.fneg",
        UnOp::FAbs => "IRUnOp.fabs",
        UnOp::FSqrt => "IRUnOp.fsqrt",
        UnOp::FFloor => "IRUnOp.ffloor",
        UnOp::FCeil => "IRUnOp.fceil",
        UnOp::FTrunc => "IRUnOp.ftrunc",
        UnOp::Not => "IRUnOp.not_",
        UnOp::CtPop => "IRUnOp.ctpop",
    }
}

fn icmp_expr(op: ICmpOp) -> &'static str {
    match op {
        ICmpOp::Eq => "IRICmpOp.eq_",
        ICmpOp::Ne => "IRICmpOp.ne_",
        ICmpOp::Ult => "IRICmpOp.ult",
        ICmpOp::Ule => "IRICmpOp.ule",
        ICmpOp::Ugt => "IRICmpOp.ugt",
        ICmpOp::Uge => "IRICmpOp.uge",
        ICmpOp::Slt => "IRICmpOp.slt",
        ICmpOp::Sle => "IRICmpOp.sle",
        ICmpOp::Sgt => "IRICmpOp.sgt",
        ICmpOp::Sge => "IRICmpOp.sge",
    }
}

fn cast_expr(op: CastOp) -> &'static str {
    match op {
        CastOp::Trunc => "IRCastOp.trunc",
        CastOp::ZExt => "IRCastOp.zext",
        CastOp::SExt => "IRCastOp.sext",
        CastOp::FPTrunc => "IRCastOp.fptrunc",
        CastOp::FPExt => "IRCastOp.fpext",
        CastOp::FPToUI => "IRCastOp.fptoui",
        CastOp::FPToSI => "IRCastOp.fptosi",
        CastOp::UIToFP => "IRCastOp.uitofp",
        CastOp::SIToFP => "IRCastOp.sitofp",
        CastOp::PtrToInt => "IRCastOp.ptrtoint",
        CastOp::IntToPtr => "IRCastOp.inttoptr",
        CastOp::PtrToPtr => "IRCastOp.ptrtoptr",
        CastOp::Bitcast => "IRCastOp.bitcast",
        CastOp::Transmute => "IRCastOp.transmute",
        CastOp::ReifyFnPointer => "IRCastOp.reifyfnpointer",
        CastOp::FPToSISat => "IRCastOp.fptosisat",
        CastOp::FPToUISat => "IRCastOp.fptouisat",
    }
}

fn inst_expr(_module: &Module, inst: &Inst, path: &str) -> Result<String, LiteralRefinementError> {
    let ty = |value: &Ty, suffix: &str| ty_expr(value, &format!("{path}.{suffix}"));
    Ok(match inst {
        Inst::BinOp { op, ty: value_ty, lhs, rhs } => {
            if matches!(
                op,
                BinOp::FAdd
                    | BinOp::FSub
                    | BinOp::FMul
                    | BinOp::FDiv
                    | BinOp::FRem
                    | BinOp::FMin
                    | BinOp::FMax
            ) {
                return Err(unsupported(
                    path,
                    format!("floating binary operation {op:?}"),
                    "supply a checked floating-point adequacy theorem before admitting this operation",
                ));
            }
            let Some(op_expr) = binop_expr(*op) else {
                return Err(unsupported(
                    path,
                    format!("boolean-carrier binary operation {op:?} with no EvalIR model"),
                    "extend EvalIR's IRBinOp with band/bor/bxor and their 0/1-carrier semantics (with refinement lemmas), or lower the connective to ICmp/Select before this pass",
                ));
            };
            format!(
                "IRInst.binop {} ({}) {} {}",
                op_expr,
                ty(value_ty, "ty")?,
                lhs.index(),
                rhs.index()
            )
        }
        Inst::UnOp { op, ty: value_ty, operand } => {
            if matches!(
                op,
                UnOp::FNeg | UnOp::FAbs | UnOp::FSqrt | UnOp::FFloor | UnOp::FCeil | UnOp::FTrunc
            ) {
                return Err(unsupported(
                    path,
                    format!("floating unary operation {op:?}"),
                    "supply a checked floating-point adequacy theorem before admitting this operation",
                ));
            }
            format!("IRInst.unop {} ({}) {}", unop_expr(*op), ty(value_ty, "ty")?, operand.index())
        }
        Inst::Overflow { .. } => {
            return Err(unsupported(
                path,
                "checked-overflow instruction whose EvalIR arm is explicitly unmodelled",
                "lower the exact result/overflow pair to proved scalar operations or add the missing adequacy theorem",
            ));
        }
        Inst::ICmp { op, ty: value_ty, lhs, rhs } => {
            if matches!(value_ty, Ty::Bool) && !matches!(op, ICmpOp::Eq | ICmpOp::Ne) {
                return Err(unsupported(
                    path,
                    format!("ordered Boolean comparison {op:?}"),
                    "lower the comparison to Eq/Ne or add the missing one-bit ordered-comparison adequacy theorem",
                ));
            }
            format!(
                "IRInst.icmp {} ({}) {} {}",
                icmp_expr(*op),
                ty(value_ty, "ty")?,
                lhs.index(),
                rhs.index()
            )
        }
        Inst::FCmp { .. } => {
            return Err(unsupported(
                path,
                "floating comparison whose EvalIR arm is explicitly unmodelled",
                "supply a checked floating-point adequacy theorem before admitting this operation",
            ));
        }
        Inst::Cast { op, src_ty, dst_ty, operand } => {
            if !matches!(op, CastOp::Trunc | CastOp::ZExt | CastOp::SExt) {
                return Err(unsupported(
                    path,
                    format!("cast outside the exact integer fragment: {op:?}"),
                    "lower to trunc/zext/sext or supply a checked adequacy theorem for this cast",
                ));
            }
            if matches!(dst_ty, Ty::Char) {
                return Err(unsupported(
                    path,
                    format!("integer cast to Char without a Unicode-scalar range proof: {op:?}"),
                    "retain the integer carrier or supply a checked proof that the result excludes surrogates and values above U+10FFFF",
                ));
            }
            format!(
                "IRInst.cast {} ({}) ({}) {}",
                cast_expr(*op),
                ty(src_ty, "src_ty")?,
                ty(dst_ty, "dst_ty")?,
                operand.index()
            )
        }
        Inst::Load { .. }
        | Inst::Store { .. }
        | Inst::Alloca { .. }
        | Inst::GEP { .. }
        | Inst::PtrData { .. }
        | Inst::PtrMetadata { .. }
        | Inst::PtrFromParts { .. } => {
            return Err(unsupported(
                path,
                format!(
                    "memory or pointer instruction with no checked TrustIR-to-EvalIR adequacy edge: {inst:?}"
                ),
                "scalarize the operation or supply the alignment, volatile, provenance, bounds, and layout adequacy theorem",
            ));
        }
        Inst::Br { target, args } => {
            format!("IRInst.br {} ({})", target.index(), id_list(args))
        }
        Inst::CondBr { cond, then_target, then_args, else_target, else_args } => format!(
            "IRInst.condbr {} {} ({}) {} ({})",
            cond.index(),
            then_target.index(),
            id_list(then_args),
            else_target.index(),
            id_list(else_args)
        ),
        Inst::Switch { .. } => {
            return Err(unsupported(
                path,
                "switch whose case constants lack an exact selector-typed normalization edge",
                "lower to CondBr or add selector-width case normalization plus differential witnesses before admission",
            ));
        }
        Inst::Call { .. } | Inst::CallIndirect { .. } => {
            return Err(unsupported(
                path,
                format!(
                    "call instruction with no checked signature/calling-convention adequacy edge: {inst:?}"
                ),
                "inline the callee into the scalar fragment or supply a checked call-boundary adequacy theorem",
            ));
        }
        Inst::Return { values } => format!("IRInst.ret ({})", id_list(values)),
        Inst::ExtractField { .. } | Inst::InsertField { .. } | Inst::ExtractElement { .. } => {
            return Err(unsupported(
                path,
                format!("aggregate instruction outside the exact scalar fragment: {inst:?}"),
                "scalarize the aggregate or supply a checked representation adequacy theorem",
            ));
        }
        Inst::Const { ty: value_ty, value } => format!(
            "IRInst.const_ ({}) ({})",
            ty(value_ty, "ty")?,
            constant_expr(value_ty, value, &format!("{path}.value"))?
        ),
        Inst::GlobalAddr { .. } | Inst::Undef { .. } => {
            return Err(unsupported(
                path,
                format!("instruction outside the exact initialized scalar fragment: {inst:?}"),
                "replace it with an initialized scalar value or supply a checked memory/undef adequacy theorem",
            ));
        }
        Inst::Assert { .. } => {
            return Err(unsupported(
                path,
                "assertion whose failure outcome is Panic in TrustIR but undefined behavior in EvalIR",
                "prove the assertion before lowering it away, or add and prove an exact panic outcome in EvalIR",
            ));
        }
        Inst::Unreachable => "IRInst.unreachable".to_owned(),
        Inst::Select { ty: value_ty, cond, then_val, else_val } => format!(
            "IRInst.select ({}) {} {} {}",
            ty(value_ty, "ty")?,
            cond.index(),
            then_val.index(),
            else_val.index()
        ),
        other => {
            return Err(unsupported(
                path,
                format!("instruction {other:?}"),
                "lower it to the 28-instruction EvalIR core with a translation proof, or add a matching IRInst constructor, exact ir_exec arm, differential witnesses, and vacuity-firewall coverage",
            ));
        }
    })
}

fn block_expr(
    module: &Module,
    function: &Function,
    block_index: usize,
) -> Result<String, LiteralRefinementError> {
    let block = &function.blocks[block_index];
    let params = clean_list("Nat", block.params.iter().map(|(value, _)| value.index().to_string()));
    let nodes = clean_list(
        "IRNode",
        block
            .body
            .iter()
            .enumerate()
            .map(|(index, node)| {
                let path = format!(
                    "function[{}].block[{}].node[{index}]",
                    function.id.index(),
                    block.id.index()
                );
                Ok(format!(
                    "IRNode.mk ({}) ({})",
                    inst_expr(module, &node.inst, &path)?,
                    id_list(&node.results)
                ))
            })
            .collect::<Result<Vec<_>, LiteralRefinementError>>()?,
    );
    Ok(format!("IRBlock.mk {} ({params}) ({nodes})", block.id.index()))
}

fn function_expr(module: &Module, function: &Function) -> Result<String, LiteralRefinementError> {
    if function.blocks.is_empty() {
        return Err(unsupported(
            format!("function[{}]", function.id.index()),
            "contract-only/external function",
            "link a body into the certified module, or extend EvalIR with an explicit environment transition relation and certify that contract boundary",
        ));
    }
    let entry = function.blocks.iter().find(|block| block.id == function.entry).ok_or(
        LiteralRefinementError::MissingEntryBlock {
            function: function.id.index(),
            entry: function.entry.index(),
        },
    )?;
    let params = clean_list("Nat", entry.params.iter().map(|(value, _)| value.index().to_string()));
    let blocks = clean_list(
        "IRBlock",
        (0..function.blocks.len())
            .map(|index| block_expr(module, function, index))
            .collect::<Result<Vec<_>, LiteralRefinementError>>()?,
    );
    Ok(format!(
        "IRFunc.mk {} ({params}) {} ({blocks})",
        function.id.index(),
        function.entry.index()
    ))
}

fn module_expr(module: &Module) -> Result<String, LiteralRefinementError> {
    let functions = clean_list(
        "IRFunc",
        module
            .functions
            .iter()
            .map(|function| function_expr(module, function))
            .collect::<Result<Vec<_>, LiteralRefinementError>>()?,
    );
    if !module.globals.is_empty() {
        return Err(unsupported(
            "module.globals",
            "global memory without a checked TrustIR-to-EvalIR layout/aliasing adequacy edge",
            "lower the closed program to the initialized scalar fragment or supply the missing memory adequacy theorem",
        ));
    }
    let globals = "IRList.nil IRGlobal";
    Ok(format!("IRModule.mk ({functions}) ({globals})"))
}

fn scalar_expr(value: &LiteralScalar) -> String {
    match value {
        LiteralScalar::Undef => "IRScalar.undef_".to_owned(),
        LiteralScalar::Bool { value } => format!("IRScalar.bool_ {}", clean_bool(*value)),
        LiteralScalar::Int { raw } => format!("IRScalar.int_ {raw}"),
        LiteralScalar::FloatBits { bits } => format!("IRScalar.float_ {bits}"),
        LiteralScalar::Unit => "IRScalar.unit_".to_owned(),
        LiteralScalar::Pointer { address } => format!("IRScalar.ptr_ {address}"),
        LiteralScalar::NullPointer => "IRScalar.nullptr_".to_owned(),
        LiteralScalar::FatPointer { data, metadata } => {
            format!("IRScalar.fat_ {data} {metadata}")
        }
        LiteralScalar::Function { id } => format!("IRScalar.fnptr_ {id}"),
    }
}

fn invocation_matches_ty(value: &LiteralScalar, ty: &Ty) -> bool {
    match value {
        LiteralScalar::Undef => true,
        LiteralScalar::Bool { .. } => matches!(ty, Ty::Bool),
        LiteralScalar::Int { .. } => matches!(
            ty,
            Ty::I8
                | Ty::I16
                | Ty::I32
                | Ty::I64
                | Ty::I128
                | Ty::U8
                | Ty::U16
                | Ty::U32
                | Ty::U64
                | Ty::U128
                | Ty::Isize
                | Ty::Usize
                | Ty::Char
        ),
        LiteralScalar::FloatBits { .. } => matches!(ty, Ty::F16 | Ty::F32 | Ty::F64),
        LiteralScalar::Unit => matches!(ty, Ty::Unit),
        LiteralScalar::Pointer { .. } | LiteralScalar::NullPointer => matches!(
            ty,
            Ty::Ptr | Ty::Ref(_) | Ty::RefMut(_) | Ty::PtrConst(_) | Ty::PtrMut(_) | Ty::Rc(_)
        ),
        LiteralScalar::FatPointer { .. } => matches!(ty, Ty::FatPtr(_)),
        LiteralScalar::Function { .. } => matches!(ty, Ty::Func(_)),
    }
}

fn validate_represented_types(module: &Module) -> Result<(), LiteralRefinementError> {
    for (signature_index, signature) in module.func_types.iter().enumerate() {
        if signature.is_vararg {
            return Err(unsupported(
                format!("func_type[{signature_index}]"),
                "variadic function signature",
                "lower varargs to an explicit aggregate parameter, or extend IRFunc and ir_call_exec with an exact variadic argument carrier",
            ));
        }
        for (index, ty) in signature.params.iter().enumerate() {
            ty_expr(ty, &format!("func_type[{signature_index}].param[{index}]"))?;
        }
        for (index, ty) in signature.returns.iter().enumerate() {
            ty_expr(ty, &format!("func_type[{signature_index}].return[{index}]"))?;
        }
    }

    for function in &module.functions {
        let signature = module.func_types.get(function.ty.as_usize()).ok_or_else(|| {
            unsupported(
                format!("function[{}].ty", function.id.index()),
                format!("dangling FuncTyId {}", function.ty.index()),
                "repair the TrustIR function-signature table and re-emit canonical bytes",
            )
        })?;
        if let Some(entry) = function.blocks.iter().find(|block| block.id == function.entry) {
            let entry_types = entry.params.iter().map(|(_, ty)| ty).collect::<Vec<_>>();
            let signature_types = signature.params.iter().collect::<Vec<_>>();
            if entry_types != signature_types {
                return Err(unsupported(
                    format!("function[{}].entry", function.id.index()),
                    "entry-block parameter types that differ from the function signature",
                    "repair the function signature/entry-block mismatch before literal refinement",
                ));
            }
        }
        for block in &function.blocks {
            for (index, (_, ty)) in block.params.iter().enumerate() {
                ty_expr(
                    ty,
                    &format!(
                        "function[{}].block[{}].param[{index}]",
                        function.id.index(),
                        block.id.index()
                    ),
                )?;
            }
        }
    }

    for (index, global) in module.globals.iter().enumerate() {
        ty_expr(&global.ty, &format!("global[{index}].ty"))?;
    }
    Ok(())
}

fn validate_invocation_argument(
    module: &Module,
    index: usize,
    value: &LiteralScalar,
    ty: &Ty,
) -> Result<(), LiteralRefinementError> {
    let path = format!("invocation.argument[{index}]");
    if matches!(value, LiteralScalar::Undef) {
        return Err(unsupported(
            path,
            "undefined invocation scalar",
            "supply an initialized Bool, canonical fixed-width integer, or Unit value",
        ));
    }
    // An invocation must not smuggle a type outside the exact EvalIR fragment.
    ty_expr(ty, &format!("{path}.ty"))?;
    if !invocation_matches_ty(value, ty) {
        return Err(LiteralRefinementError::InvalidInvocation(format!(
            "argument {index} ({value:?}) does not match entry type {ty:?}"
        )));
    }

    match value {
        LiteralScalar::Int { raw } => {
            let width = int_width(ty, &format!("{path}.ty"))?;
            if width < 128 && *raw >= (1_u128 << width) {
                return Err(LiteralRefinementError::InvalidInvocation(format!(
                    "argument {index} integer payload {raw} is not canonical for {width} bits"
                )));
            }
            if matches!(ty, Ty::Char) && (*raw > 0x10_ffff || (0xd800..=0xdfff).contains(raw)) {
                return Err(LiteralRefinementError::InvalidInvocation(format!(
                    "argument {index} integer payload {raw:#x} is not a Unicode scalar value"
                )));
            }
        }
        LiteralScalar::FloatBits { bits } => {
            let width = match ty {
                Ty::F16 => 16,
                Ty::F32 => 32,
                Ty::F64 => 64,
                _ => unreachable!("type compatibility checked above"),
            };
            if width < 64 && *bits >= (1_u64 << width) {
                return Err(LiteralRefinementError::InvalidInvocation(format!(
                    "argument {index} floating payload {bits:#x} is not canonical for F{width}"
                )));
            }
        }
        LiteralScalar::Pointer { address } => {
            let global_count = u64::try_from(module.globals.len()).map_err(|_| {
                LiteralRefinementError::InvalidInvocation("global count exceeds u64".to_owned())
            })?;
            if *address >= global_count {
                return Err(LiteralRefinementError::InvalidInvocation(format!(
                    "argument {index} pointer address {address} does not name one of the module's {global_count} global cells"
                )));
            }
        }
        LiteralScalar::FatPointer { data, .. } => {
            let global_count = u64::try_from(module.globals.len()).map_err(|_| {
                LiteralRefinementError::InvalidInvocation("global count exceeds u64".to_owned())
            })?;
            if *data >= global_count {
                return Err(LiteralRefinementError::InvalidInvocation(format!(
                    "argument {index} fat-pointer data address {data} does not name one of the module's {global_count} global cells"
                )));
            }
        }
        LiteralScalar::Function { id } => {
            let pointee = module.functions.iter().find(|function| function.id.index() == *id);
            let Some(pointee) = pointee else {
                return Err(LiteralRefinementError::InvalidInvocation(format!(
                    "argument {index} function id {id} is absent from the closed module"
                )));
            };
            let Ty::Func(expected_signature) = ty else {
                unreachable!("type compatibility checked above")
            };
            if pointee.ty != *expected_signature {
                return Err(LiteralRefinementError::InvalidInvocation(format!(
                    "argument {index} function id {id} has signature {}, not expected signature {}",
                    pointee.ty.index(),
                    expected_signature.index()
                )));
            }
        }
        LiteralScalar::Undef
        | LiteralScalar::Bool { .. }
        | LiteralScalar::Unit
        | LiteralScalar::NullPointer => {}
    }
    Ok(())
}

struct PreparedLiteral {
    source: String,
}

fn prepare(
    module_bytes: &[u8],
    function_id: u32,
    invocation: &LiteralInvocation,
) -> Result<PreparedLiteral, LiteralRefinementError> {
    if module_bytes.len() > MAX_MODULE_BYTES {
        return Err(LiteralRefinementError::ModuleTooLarge {
            bytes: module_bytes.len(),
            maximum: MAX_MODULE_BYTES,
        });
    }
    let module = trust_ir::binary::deserialize_module(module_bytes)
        .map_err(|error| LiteralRefinementError::ModuleDecode(error.to_string()))?;
    if trust_ir::binary::serialize_module(&module) != module_bytes {
        return Err(LiteralRefinementError::NonCanonicalModule);
    }

    let validation_errors = trust_ir_build::validate_module(&module);
    if !validation_errors.is_empty() {
        let summary = validation_errors
            .iter()
            .take(8)
            .map(ToString::to_string)
            .collect::<Vec<_>>()
            .join("; ");
        return Err(unsupported(
            "module",
            format!(
                "canonical but invalid TrustIR ({summary}{})",
                if validation_errors.len() > 8 {
                    format!("; and {} more validation errors", validation_errors.len() - 8)
                } else {
                    String::new()
                }
            ),
            "repair every trust-ir-build validation error before requesting literal refinement",
        ));
    }

    validate_represented_types(&module)?;

    let mut function_ids = BTreeSet::new();
    for function in &module.functions {
        if !function_ids.insert(function.id.index()) {
            return Err(LiteralRefinementError::DuplicateFunction(function.id.index()));
        }
        let mut block_ids = BTreeSet::new();
        for block in &function.blocks {
            if !block_ids.insert(block.id.index()) {
                return Err(LiteralRefinementError::DuplicateBlock {
                    function: function.id.index(),
                    block: block.id.index(),
                });
            }
        }
    }
    let function = module
        .functions
        .iter()
        .find(|function| function.id.index() == function_id)
        .ok_or(LiteralRefinementError::MissingFunction(function_id))?;
    let entry = function.blocks.iter().find(|block| block.id == function.entry).ok_or(
        LiteralRefinementError::MissingEntryBlock {
            function: function_id,
            entry: function.entry.index(),
        },
    )?;
    if invocation.arguments.len() != entry.params.len() {
        return Err(LiteralRefinementError::InvocationArity {
            expected: entry.params.len(),
            found: invocation.arguments.len(),
        });
    }
    for (index, (argument, (_, ty))) in invocation.arguments.iter().zip(&entry.params).enumerate() {
        validate_invocation_argument(&module, index, argument, ty)?;
    }
    let minimum_next_address = u64::try_from(module.globals.len()).map_err(|_| {
        LiteralRefinementError::InvalidInvocation("global count exceeds u64".to_owned())
    })?;
    if invocation.next_address < minimum_next_address {
        return Err(LiteralRefinementError::InvalidInvocation(format!(
            "next_address {} aliases {} global cells; choose at least {minimum_next_address}",
            invocation.next_address,
            module.globals.len()
        )));
    }

    let items = module.functions.len()
        + module.globals.len()
        + module.functions.iter().map(|function| function.blocks.len()).sum::<usize>()
        + module
            .functions
            .iter()
            .flat_map(|function| &function.blocks)
            .map(|block| block.body.len())
            .sum::<usize>();
    if items > MAX_OPERATIONAL_ITEMS {
        return Err(LiteralRefinementError::OperationalItemLimit {
            items,
            maximum: MAX_OPERATIONAL_ITEMS,
        });
    }

    let program = module_expr(&module)?;
    let arguments = clean_list("IRScalar", invocation.arguments.iter().map(scalar_expr));
    let function_params =
        clean_list("Nat", entry.params.iter().map(|(value, _)| value.index().to_string()));
    let digest = module.stable_digest();
    let digest_literal = clean_list("Nat", digest.bytes.into_iter().map(|byte| byte.to_string()));
    let source = format!(
        r#"namespace Trust
namespace LiteralRefinement

def ArtifactLength : Nat := {artifact_length}
def ArtifactDigest : IRList Nat := {digest_literal}
def FunctionId : Nat := {function_id}
def EntryBlock : Nat := {entry_block}
def FunctionParams : IRList Nat := {function_params}
def Arguments : IRList IRScalar := {arguments}
def Program : IRModule := {program}

def Initial : IRConfig :=
  ir_init Program FunctionId Arguments (IRList.nil IRMemSlot)
    {next_address}

def InitialMachine : IRMachine :=
  IRMachine.mk
    (IRList.cons IRFrame
      (IRFrame.mk FunctionId EntryBlock 0
        (ir_bind_params FunctionParams Arguments (IRList.nil IRBinding))
        (IRList.nil Nat))
      (IRList.nil IRFrame))
    (ir_globals_mem (ir_mod_globals Program))
    {next_address}

def Init (state : IRConfig) : Prop := state = Initial

def Next (before after : IRConfig) : Prop :=
  match before with
  | IRConfig.running machine => after = ir_step Program machine
  | IRConfig.halted outcome => False

def Model : Trust.Temporal.StateMachine IRConfig :=
  {{ init := Init, next := Next }}

theorem artifact_binding :
    ArtifactLength = {artifact_length} ∧
      (ArtifactDigest = {digest_literal} ∧ FunctionId = {function_id}) :=
  And.intro rfl (And.intro rfl rfl)

theorem init_exact (state : IRConfig) :
    Model.init state =
      (state = ir_init Program FunctionId Arguments (IRList.nil IRMemSlot)
        {next_address}) := rfl

theorem next_exact (machine : IRMachine) (after : IRConfig) :
    Model.next (IRConfig.running machine) after =
      (after = ir_step Program machine) := rfl

theorem halted_exact (outcome : IROutcome) (after : IRConfig) :
    Model.next (IRConfig.halted outcome) after = False := rfl

theorem initial_running : Initial = IRConfig.running InitialMachine := rfl

theorem first_step_is_in_model :
    Model.next (IRConfig.running InitialMachine)
      (ir_step Program InitialMachine) := rfl

end LiteralRefinement
end Trust
"#,
        artifact_length = module_bytes.len(),
        entry_block = function.entry.index(),
        next_address = invocation.next_address,
    );
    if source.len() > MAX_GENERATED_SOURCE_BYTES {
        return Err(LiteralRefinementError::GeneratedSourceLimit {
            bytes: source.len(),
            maximum: MAX_GENERATED_SOURCE_BYTES,
        });
    }
    Ok(PreparedLiteral { source })
}

fn encode_expression(expression: &Expr) -> Result<Vec<u8>, LiteralRefinementError> {
    serde_json::to_vec(expression)
        .map_err(|error| LiteralRefinementError::MalformedArtifact(error.to_string()))
}

fn run_on_large_stack<T, F>(operation: F) -> Result<T, LiteralRefinementError>
where
    T: Send + 'static,
    F: FnOnce() -> Result<T, LiteralRefinementError> + Send + 'static,
{
    std::thread::Builder::new()
        .name("trust-literal-refinement".to_owned())
        .stack_size(64 * 1024 * 1024)
        .spawn(operation)
        .map_err(|error| {
            LiteralRefinementError::CleanSpecBuild(format!(
                "cannot spawn large-stack proof thread: {error}"
            ))
        })?
        .join()
        .map_err(|_| {
            LiteralRefinementError::CleanSpecBuild(
                "large-stack literal-refinement thread panicked".to_owned(),
            )
        })?
}

/// Return isolated owned clones of the authoritative EvalIR + temporal context.
///
/// Building EvalIR is expensive, but both the kernel environment and parser
/// context are persistent/cloneable. The cached pair is never exposed for
/// mutation, so every certification and replay still starts from the exact same
/// declaration and notation frontier with no certificate-authored state.
fn fresh_literal_context() -> Result<(Environment, FileContext), LiteralRefinementError> {
    static LITERAL_PRELUDE: OnceLock<Result<(Environment, FileContext), LiteralRefinementError>> =
        OnceLock::new();
    let cached = LITERAL_PRELUDE.get_or_init(|| {
        let spec = clean_verify::eval_ir::build_prelude_spec_with_stack()
            .map_err(|error| LiteralRefinementError::CleanSpecBuild(error.to_string()))?;
        let mut environment = spec.env().clone();
        let mut context = FileContext::new();
        context.disable_external_import_search();
        elaborate_unit(
            &mut environment,
            &mut context,
            CLEAN_TEMPORAL_PRELUDE,
            "temporal prelude in EvalIR environment",
            None,
        )?;
        Ok((environment, context))
    });
    cached.clone()
}

fn check_source(source: String) -> Result<Vec<LiteralRefinementTheorem>, LiteralRefinementError> {
    run_on_large_stack(move || {
        let (mut environment, mut context) = fresh_literal_context()?;
        elaborate_suffix_with_parser_prelude(
            &mut environment,
            &mut context,
            CLEAN_TEMPORAL_PRELUDE,
            &source,
            "generated literal refinement",
        )?;

        THEOREM_NAMES
            .iter()
            .map(|theorem| {
                let (theorem_type, proof_term) = checked_theorem(&environment, theorem)?;
                Ok(LiteralRefinementTheorem {
                    theorem: (*theorem).to_owned(),
                    theorem_type: encode_expression(theorem_type)?,
                    proof_term: encode_expression(proof_term)?,
                })
            })
            .collect()
    })
}

fn check_stored_artifacts(
    source: String,
    artifacts: Vec<LiteralRefinementTheorem>,
) -> Result<(), LiteralRefinementError> {
    run_on_large_stack(move || {
        let (mut environment, mut context) = fresh_literal_context()?;
        elaborate_suffix_with_parser_prelude(
            &mut environment,
            &mut context,
            CLEAN_TEMPORAL_PRELUDE,
            &source,
            "stored literal refinement",
        )?;
        for artifact in &artifacts {
            let stored_type: Expr = serde_json::from_slice(&artifact.theorem_type)
                .map_err(|error| LiteralRefinementError::MalformedArtifact(error.to_string()))?;
            let stored_proof: Expr = serde_json::from_slice(&artifact.proof_term)
                .map_err(|error| LiteralRefinementError::MalformedArtifact(error.to_string()))?;
            let declaration =
                environment.get_const(&Name::from_string(&artifact.theorem)).ok_or_else(|| {
                    LiteralRefinementError::MalformedArtifact(format!(
                        "fresh environment lacks theorem `{}`",
                        artifact.theorem
                    ))
                })?;
            if encode_expression(&declaration.type_)? != artifact.theorem_type {
                return Err(LiteralRefinementError::ArtifactMismatch {
                    theorem: artifact.theorem.clone(),
                    field: "registered theorem type",
                });
            }
            TypeChecker::with_mode(&environment, environment.mode())
                .check_type(&stored_proof, &stored_type)
                .map_err(|error| LiteralRefinementError::KernelRejected(error.to_string()))?;
        }
        Ok(())
    })
}

/// Produce and independently replay an exact literal TrustIR refinement.
pub fn certify_literal_refinement(
    module_bytes: &[u8],
    function_id: u32,
    invocation: &LiteralInvocation,
) -> Result<LiteralRefinementCertificate, LiteralRefinementError> {
    let prepared = prepare(module_bytes, function_id, invocation)?;
    let theorems = check_source(prepared.source.clone())?;
    let certificate = LiteralRefinementCertificate {
        schema: LITERAL_REFINEMENT_SCHEMA_V2.to_owned(),
        module_bytes: module_bytes.to_vec(),
        function_id,
        invocation: invocation.clone(),
        clean_source: prepared.source,
        theorems,
    };
    recheck_literal_refinement(&certificate, module_bytes, function_id, invocation)?;
    Ok(certificate)
}

/// Freshly replay a literal refinement against exact expected inputs.
pub fn recheck_literal_refinement(
    certificate: &LiteralRefinementCertificate,
    expected_module_bytes: &[u8],
    expected_function_id: u32,
    expected_invocation: &LiteralInvocation,
) -> Result<(), LiteralRefinementError> {
    if certificate.schema != LITERAL_REFINEMENT_SCHEMA_V2 {
        return Err(LiteralRefinementError::SchemaMismatch { found: certificate.schema.clone() });
    }
    if certificate.module_bytes != expected_module_bytes {
        return Err(LiteralRefinementError::ModuleMismatch);
    }
    if certificate.function_id != expected_function_id {
        return Err(LiteralRefinementError::FunctionMismatch {
            expected: expected_function_id,
            found: certificate.function_id,
        });
    }
    if &certificate.invocation != expected_invocation {
        return Err(LiteralRefinementError::InvocationMismatch);
    }
    let prepared = prepare(expected_module_bytes, expected_function_id, expected_invocation)?;
    if certificate.clean_source != prepared.source {
        return Err(LiteralRefinementError::SourceMismatch);
    }
    if certificate.theorems.len() != THEOREM_NAMES.len()
        || certificate
            .theorems
            .iter()
            .zip(THEOREM_NAMES)
            .any(|(artifact, expected)| artifact.theorem != expected)
    {
        return Err(LiteralRefinementError::TheoremSetMismatch);
    }
    let fresh = check_source(prepared.source)?;
    for (stored, fresh) in certificate.theorems.iter().zip(fresh) {
        if stored.theorem_type != fresh.theorem_type {
            return Err(LiteralRefinementError::ArtifactMismatch {
                theorem: stored.theorem.clone(),
                field: "theorem type",
            });
        }
        if stored.proof_term != fresh.proof_term {
            return Err(LiteralRefinementError::ArtifactMismatch {
                theorem: stored.theorem.clone(),
                field: "proof term",
            });
        }
    }

    // The byte-parity checks above bind stored evidence to fresh elaboration.
    // Decode and ask the kernel to check the stored terms too, so malformed
    // serialization cannot hide behind comparison behavior.
    check_stored_artifacts(certificate.clean_source.clone(), certificate.theorems.clone())
}

#[cfg(test)]
mod tests {
    use trust_ir::{Block, CallingConv, FuncId, FuncTy, FuncTyId, Function, InstrNode, ValueId};

    use super::*;

    fn fixture_bytes() -> Vec<u8> {
        let mut module = Module::new("literal_refinement_fixture");
        module.func_types.push(FuncTy { params: vec![], returns: vec![Ty::U8], is_vararg: false });
        let mut function =
            Function::new(FuncId::new(0), "answer", FuncTyId::new(0), trust_ir::BlockId::new(0));
        let mut block = Block::new(trust_ir::BlockId::new(0));
        block.body.push(
            InstrNode::new(Inst::Const { ty: Ty::U8, value: Constant::Int(255) })
                .with_result(ValueId::new(0)),
        );
        block.body.push(InstrNode::new(Inst::Return { values: vec![ValueId::new(0)] }));
        function.blocks.push(block);
        module.functions.push(function);
        trust_ir::binary::serialize_module(&module)
    }

    fn one_parameter_fixture(ty: Ty) -> Vec<u8> {
        let mut module = Module::new("literal_refinement_parameter_fixture");
        module.func_types.push(FuncTy {
            params: vec![ty.clone()],
            returns: vec![],
            is_vararg: false,
        });
        let mut function =
            Function::new(FuncId::new(0), "parameter", FuncTyId::new(0), trust_ir::BlockId::new(0));
        let mut block = Block::new(trust_ir::BlockId::new(0)).with_param(ValueId::new(0), ty);
        block.body.push(InstrNode::new(Inst::Return { values: vec![] }));
        function.blocks.push(block);
        module.functions.push(function);
        trust_ir::binary::serialize_module(&module)
    }

    #[test]
    fn literal_program_has_universal_freshly_replayed_refinement() {
        let bytes = fixture_bytes();
        let invocation = LiteralInvocation::closed(vec![], 0);
        let certificate = certify_literal_refinement(&bytes, 0, &invocation)
            .expect("literal program must certify and freshly replay");
        assert_eq!(certificate.schema, LITERAL_REFINEMENT_SCHEMA_V2);
        assert_eq!(certificate.theorems.len(), THEOREM_NAMES.len());
        let encoded = serde_json::to_vec(&certificate).expect("certificate must serialize");
        let decoded: LiteralRefinementCertificate =
            serde_json::from_slice(&encoded).expect("certificate must deserialize");
        recheck_literal_refinement(&decoded, &bytes, 0, &invocation)
            .expect("serialized evidence must freshly replay");
    }

    #[test]
    fn generated_source_uses_the_inline_aggregate_evalir_abi() {
        let bytes = fixture_bytes();
        let invocation = LiteralInvocation { arguments: vec![], next_address: 7 };
        let source = prepare(&bytes, 0, &invocation).expect("fixture must lower").source;

        assert_eq!(
            source.matches("ir_init Program FunctionId Arguments (IRList.nil IRMemSlot)").count(),
            2,
            "Initial and init_exact must both name the current five-argument ir_init"
        );
        assert_eq!(source.matches("IRMachine.mk").count(), 1);
        assert!(
            source.contains("ir_init Program FunctionId Arguments (IRList.nil IRMemSlot)\n    7"),
            "generated Init must pass only mem0 and next_address after the call arguments"
        );
        assert!(
            source.contains("(ir_globals_mem (ir_mod_globals Program))\n    7"),
            "generated IRMachine.mk must end with memory and next_address"
        );
        assert!(!source.contains("IRAggr"), "the retired aggregate arena must not reappear");
        assert!(
            !source.contains("next_aggregate"),
            "the retired aggregate counter must not reappear"
        );
    }

    #[test]
    fn invocation_wire_shape_rejects_the_retired_aggregate_counter() {
        let invocation = LiteralInvocation { arguments: vec![], next_address: 7 };
        let current = serde_json::to_value(&invocation).expect("invocation must serialize");
        assert_eq!(
            serde_json::from_value::<LiteralInvocation>(current.clone())
                .expect("current invocation must deserialize"),
            invocation
        );

        let mut legacy = current;
        legacy
            .as_object_mut()
            .expect("invocation is an object")
            .insert("next_aggregate".to_owned(), serde_json::json!(0));
        assert!(
            serde_json::from_value::<LiteralInvocation>(legacy).is_err(),
            "a relabelled v1 invocation must not silently discard next_aggregate"
        );
    }

    #[test]
    fn exact_binding_rejects_module_source_proof_and_invocation_tampering() {
        let bytes = fixture_bytes();
        let invocation = LiteralInvocation::closed(vec![], 0);
        let certificate =
            certify_literal_refinement(&bytes, 0, &invocation).expect("fixture must certify");

        let mut retired_schema = certificate.clone();
        retired_schema.schema = LITERAL_REFINEMENT_SCHEMA_V1.to_owned();
        assert!(matches!(
            recheck_literal_refinement(&retired_schema, &bytes, 0, &invocation),
            Err(LiteralRefinementError::SchemaMismatch { .. })
        ));

        let mut unknown_field =
            serde_json::to_value(&certificate).expect("certificate must serialize");
        unknown_field
            .as_object_mut()
            .expect("certificate is an object")
            .insert("future_authority".to_owned(), serde_json::json!(true));
        assert!(
            serde_json::from_value::<LiteralRefinementCertificate>(unknown_field).is_err(),
            "unknown certificate fields must fail closed"
        );

        let mut unknown_scalar_field =
            serde_json::to_value(&certificate).expect("certificate must serialize");
        unknown_scalar_field["invocation"]["arguments"] = serde_json::json!([{
            "kind": "int",
            "raw": 7,
            "future_authority": true
        }]);
        assert!(
            serde_json::from_value::<LiteralRefinementCertificate>(unknown_scalar_field).is_err(),
            "unknown nested scalar fields must fail closed"
        );

        let mut legacy_wire =
            serde_json::to_value(&certificate).expect("certificate must serialize");
        legacy_wire["schema"] = serde_json::json!(LITERAL_REFINEMENT_SCHEMA_V1);
        legacy_wire["invocation"]["next_aggregate"] = serde_json::json!(0);
        assert!(
            serde_json::from_value::<LiteralRefinementCertificate>(legacy_wire).is_err(),
            "the original v1 wire shape must not deserialize as current evidence"
        );

        let mut other_bytes = bytes.clone();
        *other_bytes.last_mut().expect("nonempty binary") ^= 1;
        assert!(matches!(
            recheck_literal_refinement(&certificate, &other_bytes, 0, &invocation),
            Err(LiteralRefinementError::ModuleMismatch)
        ));

        let mut source_tamper = certificate.clone();
        source_tamper.clean_source.push(' ');
        assert!(matches!(
            recheck_literal_refinement(&source_tamper, &bytes, 0, &invocation),
            Err(LiteralRefinementError::SourceMismatch)
        ));

        let mut proof_tamper = certificate.clone();
        proof_tamper.theorems[2].proof_term.push(0);
        assert!(matches!(
            recheck_literal_refinement(&proof_tamper, &bytes, 0, &invocation),
            Err(LiteralRefinementError::ArtifactMismatch { field: "proof term", .. })
        ));

        let different_invocation = LiteralInvocation { next_address: 1, ..invocation.clone() };
        assert!(matches!(
            recheck_literal_refinement(&certificate, &bytes, 0, &different_invocation),
            Err(LiteralRefinementError::InvocationMismatch)
        ));
    }

    #[test]
    fn unsupported_instruction_declines_with_repair_options() {
        let mut module = Module::new("unsupported_fixture");
        module.func_types.push(FuncTy {
            params: vec![Ty::U8],
            returns: vec![Ty::U8],
            is_vararg: false,
        });
        let mut function =
            Function::new(FuncId::new(0), "copy", FuncTyId::new(0), trust_ir::BlockId::new(0));
        let mut block = Block::new(trust_ir::BlockId::new(0)).with_param(ValueId::new(0), Ty::U8);
        block.body.push(
            InstrNode::new(Inst::Copy { ty: Ty::U8, operand: ValueId::new(0) })
                .with_result(ValueId::new(1)),
        );
        block.body.push(InstrNode::new(Inst::Return { values: vec![ValueId::new(1)] }));
        function.blocks.push(block);
        module.functions.push(function);
        let bytes = trust_ir::binary::serialize_module(&module);
        let invocation = LiteralInvocation::closed(vec![LiteralScalar::Int { raw: 7 }], 0);
        let error = certify_literal_refinement(&bytes, 0, &invocation)
            .expect_err("Copy is outside the exact EvalIR core");
        match error {
            LiteralRefinementError::Unsupported { repair, .. } => {
                assert!(repair.contains("lower"));
                assert!(repair.contains("IRInst"));
            }
            other => panic!("unexpected decline: {other:?}"),
        }
    }

    #[test]
    fn closed_invocation_rejects_noncanonical_or_unproved_scalars() {
        let bytes = one_parameter_fixture(Ty::U8);
        let oversized = LiteralInvocation::closed(vec![LiteralScalar::Int { raw: 256 }], 0);
        assert!(matches!(
            prepare(&bytes, 0, &oversized),
            Err(LiteralRefinementError::InvalidInvocation(detail))
                if detail.contains("not canonical for 8 bits")
        ));

        let bytes = one_parameter_fixture(Ty::F32);
        let oversized =
            LiteralInvocation::closed(vec![LiteralScalar::FloatBits { bits: 1_u64 << 32 }], 0);
        assert!(matches!(
            prepare(&bytes, 0, &oversized),
            Err(LiteralRefinementError::Unsupported { construct, .. })
                if construct.contains("exact scalar operational fragment")
                    && construct.contains("F32")
        ));

        let bytes = one_parameter_fixture(Ty::Ptr);
        let external = LiteralInvocation::closed(vec![LiteralScalar::Pointer { address: 0 }], 0);
        assert!(matches!(
            prepare(&bytes, 0, &external),
            Err(LiteralRefinementError::Unsupported { construct, .. })
                if construct.contains("exact scalar operational fragment")
                    && construct.contains("Ptr")
        ));
    }

    #[test]
    fn undef_does_not_bypass_the_supported_type_fragment() {
        let bytes = one_parameter_fixture(Ty::Vector(Box::new(Ty::U8), 4));
        let invocation = LiteralInvocation::closed(vec![LiteralScalar::Undef], 0);
        assert!(matches!(
            prepare(&bytes, 0, &invocation),
            Err(LiteralRefinementError::Unsupported { construct, .. })
                if construct.contains("exact scalar operational fragment")
                    && construct.contains("Vector")
        ));
    }

    #[test]
    fn undefined_and_target_sized_invocations_decline() {
        let bytes = one_parameter_fixture(Ty::U8);
        assert!(matches!(
            prepare(&bytes, 0, &LiteralInvocation::closed(vec![LiteralScalar::Undef], 0)),
            Err(LiteralRefinementError::Unsupported { construct, .. })
                if construct.contains("undefined invocation scalar")
        ));

        let refined = Ty::Refine(trust_ir::value::TyId::new(0), trust_ir::value::PredId::new(0));
        assert!(matches!(
            ty_expr(&refined, "refined parameter"),
            Err(LiteralRefinementError::Unsupported { construct, .. })
                if construct.contains("exact scalar operational fragment")
                    && construct.contains("Refine")
        ));

        let mut module = Module::new("target_sized_parameter_fixture");
        module.target_info = Some(trust_ir::TargetInfo {
            triple: "i686-unknown-linux-gnu".to_owned(),
            pointer_size: 4,
            endianness: trust_ir::Endianness::Little,
            abi: None,
            struct_passing: Default::default(),
        });
        module.func_types.push(FuncTy {
            params: vec![Ty::Usize],
            returns: vec![],
            is_vararg: false,
        });
        let mut function = Function::new(
            FuncId::new(0),
            "target_sized",
            FuncTyId::new(0),
            trust_ir::BlockId::new(0),
        );
        let mut block =
            Block::new(trust_ir::BlockId::new(0)).with_param(ValueId::new(0), Ty::Usize);
        block.body.push(InstrNode::new(Inst::Return { values: vec![] }));
        function.blocks.push(block);
        module.functions.push(function);
        let bytes = trust_ir::binary::serialize_module(&module);
        assert!(matches!(
            prepare(
                &bytes,
                0,
                &LiteralInvocation::closed(vec![LiteralScalar::Int { raw: 0 }], 0),
            ),
            Err(LiteralRefinementError::Unsupported { construct, .. })
                if construct.contains("exact scalar operational fragment")
                    && construct.contains("Usize")
        ));
    }

    #[test]
    fn function_arguments_decline_until_call_boundary_adequacy_is_checked() {
        let mut module = Module::new("literal_refinement_function_argument_fixture");
        module.func_types.push(FuncTy {
            params: vec![Ty::Func(FuncTyId::new(1))],
            returns: vec![],
            is_vararg: false,
        });
        module.func_types.push(FuncTy { params: vec![], returns: vec![], is_vararg: false });
        let mut function = Function::new(
            FuncId::new(0),
            "takes_function",
            FuncTyId::new(0),
            trust_ir::BlockId::new(0),
        );
        let mut block = Block::new(trust_ir::BlockId::new(0))
            .with_param(ValueId::new(0), Ty::Func(FuncTyId::new(1)));
        block.body.push(InstrNode::new(Inst::Return { values: vec![] }));
        function.blocks.push(block);
        module.functions.push(function);
        let bytes = trust_ir::binary::serialize_module(&module);
        let invocation = LiteralInvocation::closed(vec![LiteralScalar::Function { id: 99 }], 0);
        assert!(matches!(
            prepare(&bytes, 0, &invocation),
            Err(LiteralRefinementError::Unsupported { construct, .. })
                if construct.contains("exact scalar operational fragment")
                    && construct.contains("Func")
        ));
    }

    #[test]
    fn canonical_but_invalid_trust_ir_is_rejected_before_source_generation() {
        for (name, values) in
            [("dangling return value", vec![ValueId::new(99)]), ("return arity mismatch", vec![])]
        {
            let mut module = Module::new(format!("invalid_{name}"));
            module.func_types.push(FuncTy {
                params: vec![],
                returns: vec![Ty::U8],
                is_vararg: false,
            });
            let mut function = Function::new(
                FuncId::new(0),
                "invalid_return",
                FuncTyId::new(0),
                trust_ir::BlockId::new(0),
            );
            let mut block = Block::new(trust_ir::BlockId::new(0));
            block.body.push(InstrNode::new(Inst::Return { values }));
            function.blocks.push(block);
            module.functions.push(function);

            let bytes = trust_ir::binary::serialize_module(&module);
            assert_eq!(
                trust_ir::binary::serialize_module(
                    &trust_ir::binary::deserialize_module(&bytes).expect("canonical fixture")
                ),
                bytes,
                "{name} fixture must be canonical"
            );
            assert!(
                !trust_ir_build::validate_module(&module).is_empty(),
                "{name} fixture must exercise the authoritative validator"
            );
            assert!(matches!(
                prepare(&bytes, 0, &LiteralInvocation::closed(vec![], 0)),
                Err(LiteralRefinementError::Unsupported { path, construct, .. })
                    if path == "module" && construct.contains("canonical but invalid TrustIR")
            ));
        }
    }

    #[test]
    fn unproved_operational_fields_are_rejected_instead_of_erased() {
        let module = Module::new("field_fidelity_fixture");
        let cases = [
            (
                "load alignment and volatility",
                Inst::Load { ty: Ty::U8, ptr: ValueId::new(0), volatile: true, align: Some(64) },
                "memory or pointer instruction",
            ),
            (
                "alloca alignment",
                Inst::Alloca { ty: Ty::U8, count: None, align: Some(64) },
                "memory or pointer instruction",
            ),
            (
                "inbounds gep",
                Inst::GEP {
                    pointee_ty: Ty::U8,
                    base: ValueId::new(0),
                    indices: vec![ValueId::new(1)],
                    inbounds: true,
                },
                "memory or pointer instruction",
            ),
            (
                "exhaustive switch",
                Inst::Switch {
                    value: ValueId::new(0),
                    default: trust_ir::BlockId::new(0),
                    default_args: vec![],
                    cases: vec![],
                    exhaustive_enum_unreachable: true,
                },
                "switch",
            ),
            (
                "nonexhaustive switch with untyped case constants",
                Inst::Switch {
                    value: ValueId::new(0),
                    default: trust_ir::BlockId::new(0),
                    default_args: vec![],
                    cases: vec![trust_ir::SwitchCase {
                        value: Constant::Int(256),
                        target: trust_ir::BlockId::new(0),
                        args: vec![],
                    }],
                    exhaustive_enum_unreachable: false,
                },
                "switch",
            ),
            (
                "indirect calling convention",
                Inst::CallIndirect {
                    callee: ValueId::new(0),
                    sig: FuncTyId::new(0),
                    args: vec![],
                    calling_conv: CallingConv::Swift,
                },
                "call instruction",
            ),
        ];

        for (name, instruction, expected_construct) in cases {
            assert!(matches!(
                inst_expr(&module, &instruction, name),
                Err(LiteralRefinementError::Unsupported { construct, .. })
                    if construct.contains(expected_construct)
            ));
        }
    }

    #[test]
    fn semantic_mismatches_decline_instead_of_claiming_exact_refinement() {
        let module = Module::new("semantic_mismatch_fixture");

        assert!(
            inst_expr(
                &module,
                &Inst::ICmp {
                    op: ICmpOp::Eq,
                    ty: Ty::Bool,
                    lhs: ValueId::new(0),
                    rhs: ValueId::new(1),
                },
                "Boolean equality",
            )
            .is_ok(),
            "EvalIR has an exact Boolean equality arm"
        );
        assert!(matches!(
            inst_expr(
                &module,
                &Inst::ICmp {
                    op: ICmpOp::Ult,
                    ty: Ty::Bool,
                    lhs: ValueId::new(0),
                    rhs: ValueId::new(1),
                },
                "ordered Boolean comparison",
            ),
            Err(LiteralRefinementError::Unsupported { construct, .. })
                if construct.contains("ordered Boolean comparison")
        ));
        assert!(matches!(
            inst_expr(
                &module,
                &Inst::Assert { cond: ValueId::new(0) },
                "assertion outcome",
            ),
            Err(LiteralRefinementError::Unsupported { construct, .. })
                if construct.contains("Panic") && construct.contains("undefined behavior")
        ));
        assert!(matches!(
            inst_expr(
                &module,
                &Inst::Cast {
                    op: CastOp::Trunc,
                    src_ty: Ty::U64,
                    dst_ty: Ty::Char,
                    operand: ValueId::new(0),
                },
                "unchecked Char cast",
            ),
            Err(LiteralRefinementError::Unsupported { construct, .. })
                if construct.contains("Unicode-scalar range proof")
        ));
    }
}
