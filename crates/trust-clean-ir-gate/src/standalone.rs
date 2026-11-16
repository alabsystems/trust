// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Bounded carrier faithfulness for standalone, accepted Lean source batches.
//!
//! No Rust definition index or mixed-link path is invented here. The source
//! context owns the exact accepted bytes and immutable kernel environment; a
//! separate domain binds those roots, the structural declaration identity, its
//! exact kernel payload, and the actual emitted/relocated Trust-IR function.
//! These private tokens are in-memory permissions, not serializable kernel
//! certificates or authority for linking or a complete program. Object emission
//! additionally requires exact typed codegen custody and the unchanged strict
//! machine-output gate; a token or stored stamp alone never licenses bytes.

use std::collections::{HashMap, HashSet};

use clean_kernel::{BinderInfo, Expr, Name};
use trust_certify::lean_source_batch::AcceptedLeanSourceContext;
use trust_clean_carrier::CarrierSignature;
use trust_clean_origin::emit::{
    StandaloneScalarPlan, StandaloneScalarShape, plan_clean_origin_body_for_name,
    plan_standalone_clean_origin_body_for_name, plan_standalone_scalar_body_for_name,
};
use trust_clean_origin::gate::check_faithful_for_name;
use trust_clean_origin::{CleanOriginShape, Faithful, FaithfulnessMethod};
use trust_ir::node::InstrNode;
use trust_ir::proof::ProofDigest;
use trust_ir::ty::FuncTy;
use trust_ir::value::ValueId;
use trust_ir::{BinOp, Block, CallingConv, Constant, Function, ICmpOp, Inst, Module, Producer, Ty};
use trust_types::digest::{canonical_json_sha256, is_stable_sha256_hex};

use crate::{GateRefusal, UIntCarrier, check_wrapping_binop, reflect_wrapping_binop};

const SUBJECT_MODULE_NAME: &str =
    "@trust-internal::clean-standalone-wrapping-binop-gate-subject-v1";
const PROJECTION_SUBJECT_MODULE_NAME: &str =
    "@trust-internal::clean-standalone-projection-gate-subject-v1";
const CONSTANT_SUBJECT_MODULE_NAME: &str =
    "@trust-internal::clean-standalone-constant-uint-gate-subject-v1";
const EXPRESSION_SUBJECT_MODULE_NAME: &str =
    "@trust-internal::clean-standalone-wrapping-expression-gate-subject-v1";
const COMPARISON_SUBJECT_MODULE_NAME: &str =
    "@trust-internal::clean-standalone-comparison-gate-subject-v1";
const SELECT_SUBJECT_MODULE_NAME: &str = "@trust-internal::clean-standalone-select-gate-subject-v1";
const CONNECTIVE_SUBJECT_MODULE_NAME: &str =
    "@trust-internal::clean-standalone-comparison-connective-gate-subject-v1";
const BITWISE_SUBJECT_MODULE_NAME: &str =
    "@trust-internal::clean-standalone-bitwise-gate-subject-v1";
const DIVISION_SUBJECT_MODULE_NAME: &str =
    "@trust-internal::clean-standalone-total-division-gate-subject-v1";

// An independently enforced reader budget, not a planner-authored guarantee.
pub(crate) const EXPRESSION_MAX_OPS: usize = 32;

#[derive(Clone, Copy, Debug)]
enum StandaloneShape {
    WrappingBinOp,
    Projection,
    ConstantUint,
    WrappingExpression,
    /// Trust (WS5.20): one unsigned comparison of two parameters, returned as `Bool`.
    Comparison,
    /// Trust (WS5.20): `if l ⊲ r then t else e` over parameters, as `ICmp` + `Select`.
    Select,
    /// Trust (WS5.20): `c0 && c1` / `c0 || c1` over two parameter comparisons.
    ComparisonConnective,
    /// Trust (WS5.20): a `&&&`/`|||` tree over parameters and in-range numerals.
    Bitwise,
    /// Trust (WS5.20): Lean's total `x / y`, emitted with an explicit zero guard.
    TotalDivision,
}

impl StandaloneShape {
    fn reflect_carrier(
        self,
        signature: &FuncTy,
        function: &Function,
    ) -> Result<StandaloneCarrier, GateRefusal> {
        match self {
            Self::WrappingBinOp => {
                Ok(StandaloneCarrier::UInt(reflect_wrapping_binop(signature, function)?.carrier))
            }
            Self::Projection => {
                Ok(StandaloneCarrier::UInt(reflect_projection(signature, function)?.result))
            }
            Self::ConstantUint => {
                Ok(StandaloneCarrier::UInt(reflect_constant(signature, function)?.result))
            }
            Self::WrappingExpression => {
                Ok(StandaloneCarrier::UInt(reflect_expression(signature, function)?.result))
            }
            Self::Comparison => Ok(reflect_comparison(signature, function)?.result),
            Self::Select => Ok(reflect_select(signature, function)?.result),
            Self::ComparisonConnective => {
                reflect_comparison_connective(signature, function)?;
                Ok(StandaloneCarrier::Bool)
            }
            Self::Bitwise => {
                Ok(StandaloneCarrier::UInt(reflect_bitwise(signature, function)?.result))
            }
            Self::TotalDivision => {
                Ok(StandaloneCarrier::UInt(reflect_total_division(signature, function)?.result))
            }
        }
    }
}

/// Trust (WS5.20): the exact result carrier a standalone token is admitted at —
/// an unsigned machine integer, or (the comparison shape) `Bool` (`Ty::Bool` ↔
/// Lean `Bool`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum StandaloneCarrier {
    UInt(UIntCarrier),
    Bool,
}

impl StandaloneCarrier {
    fn rust_ty(self) -> trust_types::Ty {
        match self {
            Self::UInt(carrier) => carrier.rust_ty(),
            Self::Bool => trust_types::Ty::Bool,
        }
    }

    fn clean_name(self) -> &'static str {
        match self {
            Self::UInt(carrier) => carrier.clean_name(),
            Self::Bool => "Bool",
        }
    }

    fn from_clean(clean: trust_clean_carrier::CleanType) -> Option<Self> {
        match clean {
            trust_clean_carrier::CleanType::Bool => Some(Self::Bool),
            other => UIntCarrier::from_clean(other).map(Self::UInt),
        }
    }
}

/// Source identity computed from an accepted context, not an admission token.
/// No public constructor or deserializer can assert accepted source authority.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StandaloneLeanIdentity {
    declaration: Name,
    source_closure_sha256: String,
    owned_declarations_sha256: String,
    kernel_payload_sha256: String,
}

impl StandaloneLeanIdentity {
    #[must_use]
    pub fn declaration(&self) -> &Name {
        &self.declaration
    }

    /// Ordered logical module/path labels and exact accepted source bytes.
    #[must_use]
    pub fn source_closure_sha256(&self) -> &str {
        &self.source_closure_sha256
    }

    /// Name-sorted full payload roster added by the accepted source batch.
    #[must_use]
    pub fn owned_declarations_sha256(&self) -> &str {
        &self.owned_declarations_sha256
    }

    /// Exact selected constant and primitive-extension payload, not Display.
    #[must_use]
    pub fn kernel_payload_sha256(&self) -> &str {
        &self.kernel_payload_sha256
    }
}

/// Affine, kernel-minted permission for one placeholder standalone function.
///
/// Its public disclosure accessor is usable without manufacturing authority:
///
/// ```
/// use trust_clean_ir_gate::standalone::StandaloneTrustIrFaithful;
/// use trust_ir::proof::ProofDigest;
/// fn disclose(token: &StandaloneTrustIrFaithful) -> ProofDigest {
///     token.subject_digest()
/// }
/// ```
///
/// ```compile_fail
/// use trust_clean_ir_gate::standalone::StandaloneTrustIrFaithful;
/// fn copy_token(token: &StandaloneTrustIrFaithful) {
///     let _: StandaloneTrustIrFaithful = token.clone();
/// }
/// ```
#[derive(Debug)]
pub struct StandaloneTrustIrFaithful {
    faithful: Faithful,
    identity: StandaloneLeanIdentity,
    subject_digest: ProofDigest,
    carrier: StandaloneCarrier,
    shape: StandaloneShape,
}

/// Exact post-relocation function identity, still an in-memory bounded verdict.
#[derive(Debug)]
pub struct PublishedStandaloneTrustIrFaithful {
    // Exact custody retained at the existing kernel mint, never reconstructed from a receipt.
    signature: FuncTy,
    function: Function,
    identity: StandaloneLeanIdentity,
    subject_digest: ProofDigest,
    carrier: StandaloneCarrier,
}

impl StandaloneTrustIrFaithful {
    /// Recompute accepted source identity and the exact placeholder subject.
    pub fn authenticate(
        &self,
        context: &AcceptedLeanSourceContext<'_>,
        declaration: &Name,
        signature: &FuncTy,
        function: &Function,
    ) -> Result<(), GateRefusal> {
        require_neutral_metadata(function)?;
        let identity = capture_identity(context, declaration)?;
        if identity != self.identity {
            return Err(GateRefusal::new(
                "standalone-source-identity",
                "accepted source/module closure, declaration, or kernel payload changed",
            ));
        }
        if self.faithful.declaration() != declaration
            || self.faithful.method() != FaithfulnessMethod::DefinitionalEquality
            || self.faithful.admitted_at() != &self.carrier.rust_ty()
        {
            return Err(GateRefusal::new(
                "standalone-kernel-token",
                "kernel permission does not bind the exact declaration/method/carrier",
            ));
        }
        if self.shape.reflect_carrier(signature, function)? != self.carrier {
            return Err(GateRefusal::new(
                "standalone-carrier",
                "emitted function carrier differs from the kernel permission",
            ));
        }
        if subject_digest(self.shape, &identity, signature, function)? != self.subject_digest {
            return Err(GateRefusal::new(
                "standalone-subject-digest",
                "exact standalone signature/function changed after kernel admission",
            ));
        }
        Ok(())
    }

    /// Permit only id/type placement and the Clean producer stamp to change.
    pub fn authenticate_published(
        &self,
        context: &AcceptedLeanSourceContext<'_>,
        declaration: &Name,
        signature: &FuncTy,
        original: &Function,
        published: &Function,
    ) -> Result<PublishedStandaloneTrustIrFaithful, GateRefusal> {
        self.authenticate(context, declaration, signature, original)?;
        if published.producer.as_ref() != Some(&Producer::Clean) {
            return Err(GateRefusal::new("published-producer", "published producer must be Clean"));
        }
        let mut permitted = original.clone();
        permitted.id = published.id;
        permitted.ty = published.ty;
        permitted.producer = Some(Producer::Clean);
        if &permitted != published {
            return Err(GateRefusal::new(
                "published-relocation",
                "publication changed a Function field other than id, ty, or producer",
            ));
        }
        if self.shape.reflect_carrier(signature, published)? != self.carrier {
            return Err(GateRefusal::new("published-carrier", "published carrier changed"));
        }
        Ok(PublishedStandaloneTrustIrFaithful {
            signature: signature.clone(),
            function: published.clone(),
            identity: self.identity.clone(),
            subject_digest: subject_digest(self.shape, &self.identity, signature, published)?,
            carrier: self.carrier,
        })
    }

    #[must_use]
    pub fn identity(&self) -> &StandaloneLeanIdentity {
        &self.identity
    }

    /// Placeholder digest. Publication must disclose the final token's digest.
    #[must_use]
    pub fn subject_digest(&self) -> ProofDigest {
        self.subject_digest
    }

    #[must_use]
    pub fn carrier_tag(&self) -> &'static str {
        self.carrier.clean_name()
    }

    #[must_use]
    pub fn method_tag(&self) -> &'static str {
        "definitional-equality"
    }
}

impl PublishedStandaloneTrustIrFaithful {
    /// Reconcile this retained publication with the actual accepted source batch.
    /// This reuses the existing exact source identity, not a caller digest.
    pub fn authenticate_context(
        &self,
        context: &AcceptedLeanSourceContext<'_>,
    ) -> Result<(), GateRefusal> {
        if capture_identity(context, &self.identity.declaration)? != self.identity {
            return Err(GateRefusal::new(
                "standalone-codegen-context",
                "standalone publication belongs to a different accepted source/kernel context",
            ));
        }
        Ok(())
    }

    /// Authenticate exact retained subjects and identity-only codegen placement.
    /// This transports an existing kernel verdict; it reads no new instructions
    /// or source semantics and grants no caller, linker or executable authority.
    pub fn authenticate_codegen(
        &self,
        source_signature: &FuncTy,
        source_function: &Function,
        codegen_signature: &FuncTy,
        codegen_function: &Function,
        relocation: crate::CodegenRelocation,
    ) -> Result<(), GateRefusal> {
        if source_signature != &self.signature || source_function != &self.function {
            return Err(GateRefusal::new(
                "standalone-retained-subject",
                "standalone publication does not retain this exact signature/function",
            ));
        }
        if source_signature != codegen_signature {
            return Err(GateRefusal::new(
                "standalone-codegen-signature",
                "standalone object emission requires exact identity ABI; no signature legalization",
            ));
        }
        let mut expected = self.function.clone();
        expected.id = relocation.function_id;
        expected.linkage = relocation.linkage;
        expected.visibility = relocation.visibility;
        expected.body_gate = Some(standalone_codegen_gate_stamp());
        if &expected != codegen_function {
            return Err(GateRefusal::new(
                "standalone-codegen-function",
                "standalone codegen changed a field beyond explicit id/linkage/visibility and inert gate metadata",
            ));
        }
        Ok(())
    }

    #[must_use]
    pub fn identity(&self) -> &StandaloneLeanIdentity {
        &self.identity
    }

    #[must_use]
    pub fn subject_digest(&self) -> ProofDigest {
        self.subject_digest
    }

    #[must_use]
    pub fn carrier_tag(&self) -> &'static str {
        self.carrier.clean_name()
    }

    #[must_use]
    pub fn method_tag(&self) -> &'static str {
        "definitional-equality"
    }
}

/// Kernel-check actual SSA against a declaration owned by this accepted batch.
/// No refusal may be demoted to structural, Nat-only, or ungated evidence.
/// Only the emitter's neutral metadata shell is admitted: arbitrary attached
/// proof/contract/provenance claims cannot gain authority through a fresh mint.
pub fn admit_standalone_wrapping_binop(
    context: &AcceptedLeanSourceContext<'_>,
    declaration: &Name,
    signature: &FuncTy,
    function: &Function,
) -> Result<StandaloneTrustIrFaithful, GateRefusal> {
    admit_standalone(context, declaration, signature, function, false)
}

/// Admit an actual fixed-width unsigned wrapping operation, ordinary parameter
/// projection, or in-range literal return. Literal parameters may use distinct
/// exact UInt8/16/32/64 carriers. Inductive projections, erased hypotheses,
/// and other body shapes remain refused. Homogeneous wrapping expression trees
/// with 2..=32 Add/Sub/Mul nodes are also admitted, with parameter/in-range
/// numeral leaves and no calls or effects. Each shape reconstructs actual SSA and requires a
/// whole-term kernel definitional-equality judgment at the exact carrier.
pub fn admit_standalone_scalar(
    context: &AcceptedLeanSourceContext<'_>,
    declaration: &Name,
    signature: &FuncTy,
    function: &Function,
) -> Result<StandaloneTrustIrFaithful, GateRefusal> {
    admit_standalone(context, declaration, signature, function, true)
}

fn admit_standalone(
    context: &AcceptedLeanSourceContext<'_>,
    declaration: &Name,
    signature: &FuncTy,
    function: &Function,
    allow_scalar: bool,
) -> Result<StandaloneTrustIrFaithful, GateRefusal> {
    require_neutral_metadata(function)?;
    let identity = capture_identity(context, declaration)?;
    // Derive independently from this accepted environment. A sealed plan from
    // the emitter may have been minted for another source context.
    let (faithful, carrier, shape) = if !allow_scalar {
        let plan = plan_clean_origin_body_for_name(context.environment(), declaration)
            .map_err(|error| GateRefusal::new("standalone-source-plan", format!("{error:?}")))?;
        let (faithful, carrier) =
            check_wrapping_binop(context.environment(), &plan, signature, function)?;
        (faithful, StandaloneCarrier::UInt(carrier), StandaloneShape::WrappingBinOp)
    } else {
        let plan =
            match plan_standalone_clean_origin_body_for_name(context.environment(), declaration) {
                Ok(plan) => plan,
                // Trust (WS5.20): the standalone SCALAR vocabulary is consulted only
                // when the shared planner declines, and ITS refusal is what is
                // reported when both decline, so no existing refusal moves.
                Err(error) => {
                    let Ok(scalar) =
                        plan_standalone_scalar_body_for_name(context.environment(), declaration)
                    else {
                        return Err(GateRefusal::new(
                            "standalone-source-plan",
                            format!("{error:?}"),
                        ));
                    };
                    let (faithful, carrier, shape) =
                        check_scalar_body(context, &scalar, signature, function)?;
                    return finish_standalone(
                        context,
                        declaration,
                        identity,
                        signature,
                        function,
                        faithful,
                        carrier,
                        shape,
                    );
                }
            };
        let simple = |reflect: fn(&FuncTy, &Function) -> Result<ReflectedScalar, GateRefusal>,
                      shape: StandaloneShape| {
            check_simple_body(
                context,
                plan.declaration(),
                plan.signature(),
                signature,
                function,
                reflect,
            )
            .map(|(faithful, carrier)| (faithful, StandaloneCarrier::UInt(carrier), shape))
        };
        match plan.shape() {
            CleanOriginShape::WrappingBinOp { .. } => {
                let legacy = plan.legacy_plan().ok_or_else(|| {
                    GateRefusal::new(
                        "standalone-source-plan",
                        "wrapping operation has no legacy source plan",
                    )
                })?;
                let (faithful, carrier) =
                    check_wrapping_binop(context.environment(), legacy, signature, function)?;
                (faithful, StandaloneCarrier::UInt(carrier), StandaloneShape::WrappingBinOp)
            }
            CleanOriginShape::Projection { .. } => {
                simple(reflect_projection, StandaloneShape::Projection)?
            }
            CleanOriginShape::ConstantUint { .. } => {
                simple(reflect_constant, StandaloneShape::ConstantUint)?
            }
            CleanOriginShape::Composed { .. } => {
                simple(reflect_expression, StandaloneShape::WrappingExpression)?
            }
            // Trust (WS5.20): the scalar decision family. The plan only selects
            // WHICH reader runs; the reader derives the comparison, its
            // operands and the arms from the actual SSA, and the kernel decides
            // whole-term definitional equality at the exact result carrier.
            CleanOriginShape::DecideComparison { .. } => {
                let (faithful, carrier) = check_decision_body(
                    context,
                    plan.declaration(),
                    plan.signature(),
                    signature,
                    function,
                    DecisionShape::Comparison,
                )?;
                (faithful, carrier, StandaloneShape::Comparison)
            }
            CleanOriginShape::Select { .. } => {
                let (faithful, carrier) = check_decision_body(
                    context,
                    plan.declaration(),
                    plan.signature(),
                    signature,
                    function,
                    DecisionShape::Select,
                )?;
                (faithful, carrier, StandaloneShape::Select)
            }
            _ => {
                return Err(GateRefusal::new(
                    "target-shape",
                    "only wrapping binops, bounded homogeneous wrapping expression trees, ordinary UInt parameter projections or literal returns, parameter comparisons returned as Bool, and parameter selects are admitted; inductive projections are excluded",
                ));
            }
        }
    };
    finish_standalone(context, declaration, identity, signature, function, faithful, carrier, shape)
}

/// The identity re-capture and token mint every standalone admission ends with.
#[allow(clippy::too_many_arguments)]
fn finish_standalone(
    context: &AcceptedLeanSourceContext<'_>,
    declaration: &Name,
    identity: StandaloneLeanIdentity,
    signature: &FuncTy,
    function: &Function,
    faithful: Faithful,
    carrier: StandaloneCarrier,
    shape: StandaloneShape,
) -> Result<StandaloneTrustIrFaithful, GateRefusal> {
    if capture_identity(context, declaration)? != identity {
        return Err(GateRefusal::new(
            "standalone-source-identity",
            "kernel declaration identity changed during admission",
        ));
    }
    Ok(StandaloneTrustIrFaithful {
        faithful,
        subject_digest: subject_digest(shape, &identity, signature, function)?,
        identity,
        carrier,
        shape,
    })
}

pub(crate) struct ReflectedScalar {
    pub(crate) term: Expr,
    parameters: Vec<UIntCarrier>,
    pub(crate) result: UIntCarrier,
}

fn reflect_projection(
    signature: &FuncTy,
    function: &Function,
) -> Result<ReflectedScalar, GateRefusal> {
    if signature.is_vararg || signature.returns.len() != 1 || signature.params.is_empty() {
        return Err(GateRefusal::new(
            "signature",
            "projection requires non-vararg parameters and exactly one return value",
        ));
    }
    let result = UIntCarrier::from_ir(&signature.returns[0]).ok_or_else(|| {
        GateRefusal::new("ir-carrier", "projection result must be exact UInt8/16/32/64")
    })?;
    let parameters: Vec<_> = signature
        .params
        .iter()
        .map(|ty| {
            UIntCarrier::from_ir(ty).ok_or_else(|| {
                GateRefusal::new(
                    "ir-carrier",
                    "every projection parameter must be exact UInt8/16/32/64",
                )
            })
        })
        .collect::<Result<_, _>>()?;
    let [block] = function.blocks.as_slice() else {
        return Err(GateRefusal::new("control-flow", "projection requires exactly one block"));
    };
    if block.id != function.entry || block.params.len() != parameters.len() {
        return Err(GateRefusal::new(
            "entry-parameters",
            "projection entry or parameter count disagrees with signature",
        ));
    }
    let mut definitions = HashSet::new();
    for ((id, ty), expected) in block.params.iter().zip(&signature.params) {
        if ty != expected {
            return Err(GateRefusal::new(
                "entry-parameters",
                "projection parameter type disagrees with signature",
            ));
        }
        if !definitions.insert(*id) {
            return Err(GateRefusal::new("ssa", "projection entry defines a value twice"));
        }
    }
    let [node] = block.body.as_slice() else {
        return Err(GateRefusal::new(
            "projection-body",
            "projection must contain only one Return instruction",
        ));
    };
    let Inst::Return { values } = &node.inst else {
        return Err(GateRefusal::new("projection-body", "projection instruction must be Return"));
    };
    let [returned] = values.as_slice() else {
        return Err(GateRefusal::new("return", "projection must return exactly one value"));
    };
    if !node.results.is_empty() {
        return Err(GateRefusal::new("return", "Return must not define SSA values"));
    }
    let projected = block.params.iter().position(|(id, _)| id == returned).ok_or_else(|| {
        GateRefusal::new("ssa", "projection returns an undefined entry parameter")
    })?;
    if parameters[projected] != result {
        return Err(GateRefusal::new("return", "returned parameter carrier differs from result"));
    }
    // The source planner's projected index is deliberately not consulted.
    // Reflect the actual returned SSA identity into the source-order telescope.
    let index = u32::try_from(parameters.len() - 1 - projected)
        .map_err(|_| GateRefusal::new("resource-bound", "projection arity exceeds u32"))?;
    let mut term = Expr::bvar(index);
    for carrier in parameters.iter().rev() {
        term = Expr::lam(BinderInfo::Default, carrier.ty_expr(), term);
    }
    Ok(ReflectedScalar { term, parameters, result })
}

fn reflect_constant(
    signature: &FuncTy,
    function: &Function,
) -> Result<ReflectedScalar, GateRefusal> {
    if signature.is_vararg || signature.returns.len() != 1 {
        return Err(GateRefusal::new(
            "signature",
            "literal return requires a non-vararg signature and exactly one result",
        ));
    }
    let result = UIntCarrier::from_ir(&signature.returns[0]).ok_or_else(|| {
        GateRefusal::new("ir-carrier", "literal result must be exact UInt8/16/32/64")
    })?;
    let parameters: Vec<_> = signature
        .params
        .iter()
        .map(|ty| {
            UIntCarrier::from_ir(ty).ok_or_else(|| {
                GateRefusal::new(
                    "ir-carrier",
                    "every literal parameter must be exact UInt8/16/32/64",
                )
            })
        })
        .collect::<Result<_, _>>()?;
    let [block] = function.blocks.as_slice() else {
        return Err(GateRefusal::new("control-flow", "literal return requires exactly one block"));
    };
    if block.id != function.entry || block.params.len() != parameters.len() {
        return Err(GateRefusal::new(
            "entry-parameters",
            "literal entry or parameter count disagrees with signature",
        ));
    }
    let mut definitions = HashSet::new();
    for ((id, ty), expected) in block.params.iter().zip(&signature.params) {
        if ty != expected {
            return Err(GateRefusal::new(
                "entry-parameters",
                "literal parameter type disagrees with signature",
            ));
        }
        if !definitions.insert(*id) {
            return Err(GateRefusal::new("ssa", "literal entry defines a value twice"));
        }
    }
    let [constant, returned] = block.body.as_slice() else {
        return Err(GateRefusal::new(
            "constant-body",
            "literal body must contain exactly Const then Return",
        ));
    };
    let Inst::Const { ty, value } = &constant.inst else {
        return Err(GateRefusal::new("constant-body", "literal body must begin with Const"));
    };
    if ty != &signature.returns[0] {
        return Err(GateRefusal::new("constant", "literal type differs from result carrier"));
    }
    let [id] = constant.results.as_slice() else {
        return Err(GateRefusal::new("ssa", "Const must define exactly one SSA value"));
    };
    if !definitions.insert(*id) {
        return Err(GateRefusal::new("ssa", "Const redefines an entry parameter"));
    }
    // Every supported UInt value fits in i128, so Int is its only canonical
    // constant spelling. Never truncate, wrap an out-of-range value, or read
    // the numeral from the source planner instead of the emitted instruction.
    let Constant::Int(value) = value else {
        return Err(GateRefusal::new(
            "constant",
            "literal requires canonical non-negative Constant::Int",
        ));
    };
    if *value < 0 || (*value as u128) >= result.modulus() {
        return Err(GateRefusal::new("constant", "literal is outside its exact unsigned carrier"));
    }
    let literal = u64::try_from(*value)
        .map_err(|_| GateRefusal::new("constant", "literal does not fit u64"))?;
    let Inst::Return { values } = &returned.inst else {
        return Err(GateRefusal::new("constant-body", "literal body must end with Return"));
    };
    if values.as_slice() != [*id] || !returned.results.is_empty() {
        return Err(GateRefusal::new(
            "return",
            "Return must consume exactly the Const result and define no values",
        ));
    }
    let mut term = Expr::app(result.member("ofNat"), Expr::nat_lit(literal));
    for carrier in parameters.iter().rev() {
        term = Expr::lam(BinderInfo::Default, carrier.ty_expr(), term);
    }
    Ok(ReflectedScalar { term, parameters, result })
}

/// Read the actual SSA expression, never the source planner's operator tree.
/// Every computed value must have exactly one use on the path to Return;
/// parameters may be reused. This deliberately accepts trees, not shared DAGs,
/// and rejects dead instructions even when their removal would preserve defeq.
pub(crate) fn reflect_expression(
    signature: &FuncTy,
    function: &Function,
) -> Result<ReflectedScalar, GateRefusal> {
    if signature.is_vararg || signature.returns.len() != 1 {
        return Err(GateRefusal::new("signature", "expression requires one non-vararg result"));
    }
    let result = UIntCarrier::from_ir(&signature.returns[0]).ok_or_else(|| {
        GateRefusal::new("ir-carrier", "expression result must be exact UInt8/16/32/64")
    })?;
    if signature.params.iter().any(|ty| UIntCarrier::from_ir(ty) != Some(result)) {
        return Err(GateRefusal::new(
            "ir-carrier",
            "every expression parameter, used or not, must share the exact result carrier",
        ));
    }
    let arity = signature.params.len();
    let [block] = function.blocks.as_slice() else {
        return Err(GateRefusal::new("control-flow", "expression requires exactly one block"));
    };
    if block.id != function.entry || block.params.len() != arity {
        return Err(GateRefusal::new("entry-parameters", "expression entry/signature mismatch"));
    }
    // A binary tree has at most ops+1 constant leaves, plus its final Return.
    if block.body.len() > 2 * EXPRESSION_MAX_OPS + 2 {
        return Err(GateRefusal::new("expression-bound", "expression instruction budget exceeded"));
    }
    let mut values: HashMap<ValueId, Expr> = HashMap::new();
    let mut computed_uses: HashMap<ValueId, usize> = HashMap::new();
    for (index, ((id, ty), expected)) in block.params.iter().zip(&signature.params).enumerate() {
        if ty != expected {
            return Err(GateRefusal::new("entry-parameters", "expression parameter type mismatch"));
        }
        let index = u32::try_from(arity - 1 - index)
            .map_err(|_| GateRefusal::new("expression-bound", "expression arity exceeds u32"))?;
        if values.insert(*id, Expr::bvar(index)).is_some() {
            return Err(GateRefusal::new("ssa", "expression defines an entry parameter twice"));
        }
    }
    let mut operations = 0;
    let mut returned = None;
    for (position, node) in block.body.iter().enumerate() {
        let term = match &node.inst {
            Inst::Const { ty, value } => {
                if UIntCarrier::from_ir(ty) != Some(result) {
                    return Err(GateRefusal::new(
                        "ir-carrier",
                        "expression Const carrier mismatch",
                    ));
                }
                let Constant::Int(value) = value else {
                    return Err(GateRefusal::new(
                        "constant",
                        "expression requires canonical Constant::Int",
                    ));
                };
                if *value < 0 || (*value as u128) >= result.modulus() {
                    return Err(GateRefusal::new("constant", "expression literal is out of range"));
                }
                let value = u64::try_from(*value)
                    .map_err(|_| GateRefusal::new("constant", "expression literal exceeds u64"))?;
                Expr::app(result.member("ofNat"), Expr::nat_lit(value))
            }
            Inst::BinOp { op, ty, lhs, rhs } => {
                if UIntCarrier::from_ir(ty) != Some(result) {
                    return Err(GateRefusal::new(
                        "ir-carrier",
                        "expression BinOp carrier mismatch",
                    ));
                }
                operations += 1;
                if operations > EXPRESSION_MAX_OPS {
                    return Err(GateRefusal::new(
                        "expression-bound",
                        "expression exceeds 32 operations",
                    ));
                }
                // Independent map of actual Trust-IR wrapping operations to
                // exact Clean UInt primitives; no producer table or algebra.
                let primitive = match op {
                    BinOp::Add => "add",
                    BinOp::Sub => "sub",
                    BinOp::Mul => "mul",
                    _ => {
                        return Err(GateRefusal::new(
                            "instruction",
                            "expression admits only wrapping Add/Sub/Mul",
                        ));
                    }
                };
                let left = expression_use(*lhs, &values, &mut computed_uses)?;
                let right = expression_use(*rhs, &values, &mut computed_uses)?;
                Expr::apps(result.member(primitive), [left, right])
            }
            Inst::Return { values: returned_values } => {
                if position + 1 != block.body.len() || !node.results.is_empty() {
                    return Err(GateRefusal::new(
                        "return",
                        "expression Return must be last and define no values",
                    ));
                }
                let [id] = returned_values.as_slice() else {
                    return Err(GateRefusal::new(
                        "return",
                        "expression must return exactly one value",
                    ));
                };
                returned = Some(expression_use(*id, &values, &mut computed_uses)?);
                continue;
            }
            _ => {
                return Err(GateRefusal::new(
                    "instruction",
                    "expression contains an unsupported instruction or effect",
                ));
            }
        };
        let [id] = node.results.as_slice() else {
            return Err(GateRefusal::new(
                "ssa",
                "expression Const/BinOp must define exactly one value",
            ));
        };
        if values.insert(*id, term).is_some() {
            return Err(GateRefusal::new("ssa", "expression redefines an SSA value"));
        }
        computed_uses.insert(*id, 0);
    }
    if !(2..=EXPRESSION_MAX_OPS).contains(&operations) {
        return Err(GateRefusal::new(
            "expression-bound",
            "expression requires 2..=32 wrapping operations",
        ));
    }
    let mut term =
        returned.ok_or_else(|| GateRefusal::new("return", "expression has no final Return"))?;
    if computed_uses.values().any(|count| *count != 1) {
        return Err(GateRefusal::new(
            "expression-tree",
            "every computed value must feed the returned tree exactly once; dead values and shared computed nodes are refused",
        ));
    }
    for _ in 0..arity {
        term = Expr::lam(BinderInfo::Default, result.ty_expr(), term);
    }
    Ok(ReflectedScalar { term, parameters: vec![result; arity], result })
}

fn expression_use(
    id: ValueId,
    values: &HashMap<ValueId, Expr>,
    computed_uses: &mut HashMap<ValueId, usize>,
) -> Result<Expr, GateRefusal> {
    let term = values.get(&id).cloned().ok_or_else(|| {
        GateRefusal::new("ssa", "expression uses an undefined or forward SSA value")
    })?;
    if let Some(uses) = computed_uses.get_mut(&id) {
        *uses += 1;
        if *uses > 1 {
            return Err(GateRefusal::new(
                "expression-tree",
                "computed expression nodes may not be shared",
            ));
        }
    }
    Ok(term)
}

/// Trust (WS5.20): which decision reader [`check_decision_body`] runs.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum DecisionShape {
    Comparison,
    Select,
}

/// A comparison read off actual SSA, in the frozen producers' vocabulary: `<`,
/// `<=` or `==` between two 0-based source parameters.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct ReadComparison {
    cmp: trust_spec_elab::SelectCmp,
    left: usize,
    right: usize,
}

/// A decision body reflected into the frozen producers' INPUT (never an
/// `Expr`): the per-parameter domains, the comparison, and — for a select —
/// the two returned parameters.
struct ReflectedDecision {
    parameters: Vec<UIntCarrier>,
    comparison: ReadComparison,
    arms: Option<(usize, usize)>,
    result: StandaloneCarrier,
}

/// Map one actual `ICmp` over two entry parameters to the producers' `<`/`<=`/
/// `==` vocabulary. `>`/`>=` are the same relation read with the operands
/// swapped (`a > b` IS `b < a`), which is what the Lean elaborator itself does;
/// `!=` and every signed predicate have no producer and are refused.
fn read_comparison(op: ICmpOp, lhs: usize, rhs: usize) -> Result<ReadComparison, GateRefusal> {
    use trust_spec_elab::SelectCmp;
    let (cmp, left, right) = match op {
        ICmpOp::Ult => (SelectCmp::Lt, lhs, rhs),
        ICmpOp::Ule => (SelectCmp::Le, lhs, rhs),
        ICmpOp::Eq => (SelectCmp::Eq, lhs, rhs),
        ICmpOp::Ugt => (SelectCmp::Lt, rhs, lhs),
        ICmpOp::Uge => (SelectCmp::Le, rhs, lhs),
        _ => {
            return Err(GateRefusal::new(
                "instruction",
                "a standalone decision admits only unsigned <, <=, >, >= and == comparisons",
            ));
        }
    };
    Ok(ReadComparison { cmp, left, right })
}

/// [`entry_parameters`]' reading: the entry block, each parameter's carrier, and each
/// parameter value's 0-based source position.
type EntryParameters<'f> = (&'f Block, Vec<UIntCarrier>, HashMap<ValueId, usize>);

/// The entry block of a one-block standalone body, its parameters checked
/// against `signature` and mapped to their 0-based source positions.
fn entry_parameters<'f>(
    signature: &FuncTy,
    function: &'f Function,
) -> Result<EntryParameters<'f>, GateRefusal> {
    if signature.is_vararg || signature.returns.len() != 1 || signature.params.is_empty() {
        return Err(GateRefusal::new(
            "signature",
            "a decision requires non-vararg parameters and exactly one result",
        ));
    }
    let parameters: Vec<_> = signature
        .params
        .iter()
        .map(|ty| {
            UIntCarrier::from_ir(ty).ok_or_else(|| {
                GateRefusal::new(
                    "ir-carrier",
                    "every decision parameter must be exact UInt8/16/32/64",
                )
            })
        })
        .collect::<Result<_, _>>()?;
    let [block] = function.blocks.as_slice() else {
        return Err(GateRefusal::new("control-flow", "a decision requires exactly one block"));
    };
    if block.id != function.entry || block.params.len() != parameters.len() {
        return Err(GateRefusal::new(
            "entry-parameters",
            "decision entry or parameter count disagrees with signature",
        ));
    }
    let mut positions = HashMap::new();
    for (index, ((id, ty), expected)) in block.params.iter().zip(&signature.params).enumerate() {
        if ty != expected {
            return Err(GateRefusal::new(
                "entry-parameters",
                "decision parameter type disagrees with signature",
            ));
        }
        if positions.insert(*id, index).is_some() {
            return Err(GateRefusal::new("ssa", "decision entry defines a value twice"));
        }
    }
    Ok((block, parameters, positions))
}

/// Read an `ICmp` whose operands are both entry parameters of ONE carrier,
/// defining exactly one fresh value.
fn read_icmp(
    node: &InstrNode,
    parameters: &[UIntCarrier],
    positions: &HashMap<ValueId, usize>,
) -> Result<(ReadComparison, ValueId), GateRefusal> {
    let Inst::ICmp { op, ty, lhs, rhs } = &node.inst else {
        return Err(GateRefusal::new("decision-body", "a decision must begin with ICmp"));
    };
    let (Some(&left), Some(&right)) = (positions.get(lhs), positions.get(rhs)) else {
        return Err(GateRefusal::new(
            "decision-operand",
            "both comparison operands must be entry parameters",
        ));
    };
    let carrier = UIntCarrier::from_ir(ty).ok_or_else(|| {
        GateRefusal::new("ir-carrier", "comparison operand carrier must be exact UInt8/16/32/64")
    })?;
    if parameters[left] != carrier || parameters[right] != carrier {
        return Err(GateRefusal::new(
            "ir-carrier",
            "comparison type differs from its operands' parameter carriers",
        ));
    }
    let [id] = node.results.as_slice() else {
        return Err(GateRefusal::new("ssa", "ICmp must define exactly one value"));
    };
    if positions.contains_key(id) {
        return Err(GateRefusal::new("ssa", "ICmp redefines an entry parameter"));
    }
    Ok((read_comparison(*op, left, right)?, *id))
}

/// `%c = icmp ⊲ %l %r ; return %c` at `(UIntN, UIntN, …) -> Bool`.
fn reflect_comparison(
    signature: &FuncTy,
    function: &Function,
) -> Result<ReflectedDecision, GateRefusal> {
    let (block, parameters, positions) = entry_parameters(signature, function)?;
    if signature.returns[0] != Ty::Bool {
        return Err(GateRefusal::new("ir-carrier", "a comparison returns exactly Bool"));
    }
    let [compare, returned] = block.body.as_slice() else {
        return Err(GateRefusal::new(
            "decision-body",
            "a comparison body is exactly ICmp then Return",
        ));
    };
    let (comparison, id) = read_icmp(compare, &parameters, &positions)?;
    let Inst::Return { values } = &returned.inst else {
        return Err(GateRefusal::new("decision-body", "a comparison body must end with Return"));
    };
    if values.as_slice() != [id] || !returned.results.is_empty() {
        return Err(GateRefusal::new(
            "return",
            "Return must consume exactly the ICmp result and define no values",
        ));
    }
    Ok(ReflectedDecision { parameters, comparison, arms: None, result: StandaloneCarrier::Bool })
}

/// `%c = icmp ⊲ %l %r ; %s = select R %c %t %e ; return %s`, with both arms
/// entry parameters of the result carrier.
fn reflect_select(
    signature: &FuncTy,
    function: &Function,
) -> Result<ReflectedDecision, GateRefusal> {
    let (block, parameters, positions) = entry_parameters(signature, function)?;
    let result = UIntCarrier::from_ir(&signature.returns[0]).ok_or_else(|| {
        GateRefusal::new("ir-carrier", "a select result must be exact UInt8/16/32/64")
    })?;
    let [compare, select, returned] = block.body.as_slice() else {
        return Err(GateRefusal::new(
            "decision-body",
            "a select body is exactly ICmp, Select, then Return",
        ));
    };
    let (comparison, cond) = read_icmp(compare, &parameters, &positions)?;
    let Inst::Select { ty, cond: selected_on, then_val, else_val } = &select.inst else {
        return Err(GateRefusal::new(
            "decision-body",
            "a select body's second node must be Select",
        ));
    };
    if *selected_on != cond {
        return Err(GateRefusal::new("ssa", "Select must branch on the ICmp result"));
    }
    if UIntCarrier::from_ir(ty) != Some(result) {
        return Err(GateRefusal::new("ir-carrier", "Select type differs from the result carrier"));
    }
    let (Some(&then_param), Some(&else_param)) = (positions.get(then_val), positions.get(else_val))
    else {
        return Err(GateRefusal::new(
            "decision-operand",
            "both select arms must be entry parameters",
        ));
    };
    if parameters[then_param] != result || parameters[else_param] != result {
        return Err(GateRefusal::new(
            "ir-carrier",
            "a select arm's parameter carrier differs from the result carrier",
        ));
    }
    let [id] = select.results.as_slice() else {
        return Err(GateRefusal::new("ssa", "Select must define exactly one value"));
    };
    if positions.contains_key(id) || *id == cond {
        return Err(GateRefusal::new("ssa", "Select redefines an earlier value"));
    }
    let Inst::Return { values } = &returned.inst else {
        return Err(GateRefusal::new("decision-body", "a select body must end with Return"));
    };
    if values.as_slice() != [*id] || !returned.results.is_empty() {
        return Err(GateRefusal::new(
            "return",
            "Return must consume exactly the Select result and define no values",
        ));
    }
    Ok(ReflectedDecision {
        parameters,
        comparison,
        arms: Some((then_param, else_param)),
        result: StandaloneCarrier::UInt(result),
    })
}

fn machine_domain(carrier: UIntCarrier) -> trust_spec_elab::Domain {
    use trust_spec_elab::MachineUIntWidth;
    trust_spec_elab::Domain::Machine(match carrier {
        UIntCarrier::U8 => MachineUIntWidth::U8,
        UIntCarrier::U16 => MachineUIntWidth::U16,
        UIntCarrier::U32 => MachineUIntWidth::U32,
        UIntCarrier::U64 => MachineUIntWidth::U64,
    })
}

/// Trust (WS5.20): the decision family's kernel check. The actual SSA is read
/// by [`reflect_comparison`] / [`reflect_select`] (never the plan's operands),
/// its reading is handed to the SAME frozen `trust_spec_elab` producer the MIR
/// lane's side B uses (`admit_comparison_function` / `admit_select_function`),
/// minted into a scratch clone of the accepted environment, and the minted
/// term must be whole-term definitionally equal to the untouched declaration
/// at the exact result carrier. The producer, not this reader, owns the term
/// vocabulary; this crate shares nothing with the emitter.
fn check_decision_body(
    context: &AcceptedLeanSourceContext<'_>,
    declaration: &Name,
    source: &CarrierSignature,
    signature: &FuncTy,
    function: &Function,
    shape: DecisionShape,
) -> Result<(Faithful, StandaloneCarrier), GateRefusal> {
    if function.id.index() != 0 || function.ty.index() != 0 {
        return Err(GateRefusal::new(
            "subject-identity",
            "scalar body requires placeholder FuncId(0)/FuncTyId(0)",
        ));
    }
    if function.name != trust_clean_origin::symbol::declaration_symbol(declaration) {
        return Err(GateRefusal::new(
            "subject-name",
            "scalar function name differs from owned source declaration",
        ));
    }
    if !source.hypotheses().is_empty() || !source.preconditions().is_empty() {
        return Err(GateRefusal::new(
            "source-preconditions",
            "scalar body does not admit erased hypotheses or preconditions",
        ));
    }
    let reflected = match shape {
        DecisionShape::Comparison => reflect_comparison(signature, function)?,
        DecisionShape::Select => reflect_select(signature, function)?,
    };
    if source.arguments().len() != reflected.parameters.len() {
        return Err(GateRefusal::new(
            "source-ir-arity",
            "source and decision SSA parameter counts differ",
        ));
    }
    for (argument, actual) in source.arguments().iter().zip(&reflected.parameters) {
        if UIntCarrier::from_clean(argument.clean()) != Some(*actual)
            || argument.rust() != &actual.rust_ty()
        {
            return Err(GateRefusal::new(
                "source-ir-carrier",
                "source and decision parameter carriers differ",
            ));
        }
    }
    let carrier = reflected.result;
    if StandaloneCarrier::from_clean(source.result().clean()) != Some(carrier)
        || source.result().rust() != &carrier.rust_ty()
    {
        return Err(GateRefusal::new(
            "source-ir-carrier",
            "source and decision result carriers differ",
        ));
    }
    let domains: Vec<trust_spec_elab::Domain> =
        reflected.parameters.iter().map(|carrier| machine_domain(*carrier)).collect();
    let reflected_name = format!("{declaration}_trust_standalone_reflection");
    let reflected_kernel_name = Name::from_string(&reflected_name);
    let mut scratch = context.environment().clone();
    if scratch.get_const(&reflected_kernel_name).is_some() {
        return Err(GateRefusal::new(
            "reflection-name",
            "the reflection constant's name is already taken in the accepted environment",
        ));
    }
    let ReadComparison { cmp, left, right } = reflected.comparison;
    let minted = match (shape, reflected.arms) {
        (DecisionShape::Comparison, None) => trust_spec_elab::admit_comparison_function(
            &mut scratch,
            &reflected_name,
            &domains,
            cmp,
            trust_spec_elab::CmpOperand::Param(left),
            trust_spec_elab::CmpOperand::Param(right),
        ),
        (DecisionShape::Select, Some((then_param, else_param))) => {
            trust_spec_elab::admit_select_function(
                &mut scratch,
                &reflected_name,
                &domains,
                cmp,
                left,
                right,
                then_param,
                else_param,
            )
        }
        _ => {
            return Err(GateRefusal::new(
                "decision-body",
                "INTERNAL: decision reader and shape disagree; please report it",
            ));
        }
    };
    minted.map_err(|detail| GateRefusal::new("reflection-rejected", detail))?;
    let Some(term) = scratch.get_const(&reflected_kernel_name).and_then(|c| c.value.clone()) else {
        return Err(GateRefusal::new(
            "reflection-rejected",
            "the reflected defining equation was accepted but carries no value",
        ));
    };
    let faithful =
        check_faithful_for_name(context.environment(), declaration, &term, source.result())
            .map_err(|refusal| GateRefusal::new("kernel-disagreement", refusal.note()))?;
    if faithful.method() != FaithfulnessMethod::DefinitionalEquality {
        return Err(GateRefusal::new(
            "kernel-method",
            "a standalone decision requires whole-term definitional equality",
        ));
    }
    if faithful.admitted_at() != &carrier.rust_ty() {
        return Err(GateRefusal::new(
            "kernel-carrier",
            "decision permission has a different exact carrier",
        ));
    }
    Ok((faithful, carrier))
}

/// Trust (WS5.20): `%c0 = icmp; %c1 = icmp; %r = and|or bool %c0 %c1; ret %r`
/// read off the actual SSA: the two comparisons (each over two entry
/// parameters of one UInt carrier) and the connective, in operand order.
struct ReflectedConnective {
    parameters: Vec<UIntCarrier>,
    op: trust_spec_elab::BoolBinOp,
    left: ReadComparison,
    right: ReadComparison,
}

fn reflect_comparison_connective(
    signature: &FuncTy,
    function: &Function,
) -> Result<ReflectedConnective, GateRefusal> {
    let (block, parameters, positions) = entry_parameters(signature, function)?;
    if signature.returns[0] != Ty::Bool {
        return Err(GateRefusal::new("ir-carrier", "a comparison connective returns exactly Bool"));
    }
    if parameters.iter().any(|carrier| *carrier != parameters[0]) {
        return Err(GateRefusal::new(
            "ir-carrier",
            "every connective parameter must share one exact UInt carrier",
        ));
    }
    let [first, second, join, returned] = block.body.as_slice() else {
        return Err(GateRefusal::new(
            "decision-body",
            "a comparison connective is exactly ICmp, ICmp, And/Or, then Return",
        ));
    };
    let (c0, id0) = read_icmp(first, &parameters, &positions)?;
    let (c1, id1) = read_icmp(second, &parameters, &positions)?;
    if id0 == id1 {
        return Err(GateRefusal::new("ssa", "the two comparisons define one value"));
    }
    let Inst::BinOp { op, ty, lhs, rhs } = &join.inst else {
        return Err(GateRefusal::new("decision-body", "the connective must be a BinOp"));
    };
    if *ty != Ty::Bool {
        return Err(GateRefusal::new("ir-carrier", "the connective must be computed at Bool"));
    }
    let op = match op {
        BinOp::And => trust_spec_elab::BoolBinOp::And,
        BinOp::Or => trust_spec_elab::BoolBinOp::Or,
        _ => {
            return Err(GateRefusal::new(
                "instruction",
                "a comparison connective admits only And/Or at Bool",
            ));
        }
    };
    // Each comparison feeds the connective exactly once, in operand order.
    let (left, right) = if (*lhs, *rhs) == (id0, id1) {
        (c0, c1)
    } else if (*lhs, *rhs) == (id1, id0) {
        (c1, c0)
    } else {
        return Err(GateRefusal::new(
            "ssa",
            "the connective must combine exactly the two comparison results",
        ));
    };
    let [id] = join.results.as_slice() else {
        return Err(GateRefusal::new("ssa", "the connective must define exactly one value"));
    };
    if positions.contains_key(id) || *id == id0 || *id == id1 {
        return Err(GateRefusal::new("ssa", "the connective redefines an earlier value"));
    }
    let Inst::Return { values } = &returned.inst else {
        return Err(GateRefusal::new("decision-body", "a connective body must end with Return"));
    };
    if values.as_slice() != [*id] || !returned.results.is_empty() {
        return Err(GateRefusal::new(
            "return",
            "Return must consume exactly the connective result and define no values",
        ));
    }
    Ok(ReflectedConnective { parameters, op, left, right })
}

/// Trust (WS5.20): a `&&&`/`|||` tree read off the actual SSA, rendered in the
/// frozen elaborator's surface syntax over `p0 … p{n-1}` (never the planner's
/// tree).
struct ReflectedBitwise {
    rendering: String,
    arity: usize,
    result: UIntCarrier,
}

/// Every computed value has exactly one use on the path to Return (a tree, as
/// [`reflect_expression`]); parameters may be reused; only `BinOp::And`/`Or`,
/// canonical in-range `Const::Int`, and one final `Return` are read.
fn reflect_bitwise(
    signature: &FuncTy,
    function: &Function,
) -> Result<ReflectedBitwise, GateRefusal> {
    if signature.is_vararg || signature.returns.len() != 1 {
        return Err(GateRefusal::new("signature", "a bitwise tree requires one non-vararg result"));
    }
    let result = UIntCarrier::from_ir(&signature.returns[0]).ok_or_else(|| {
        GateRefusal::new("ir-carrier", "a bitwise result must be exact UInt8/16/32/64")
    })?;
    if signature.params.iter().any(|ty| UIntCarrier::from_ir(ty) != Some(result)) {
        return Err(GateRefusal::new(
            "ir-carrier",
            "every bitwise parameter, used or not, must share the exact result carrier",
        ));
    }
    let arity = signature.params.len();
    let [block] = function.blocks.as_slice() else {
        return Err(GateRefusal::new("control-flow", "a bitwise tree requires exactly one block"));
    };
    if block.id != function.entry || block.params.len() != arity {
        return Err(GateRefusal::new("entry-parameters", "bitwise entry/signature mismatch"));
    }
    if block.body.len() > 2 * EXPRESSION_MAX_OPS + 2 {
        return Err(GateRefusal::new("expression-bound", "bitwise instruction budget exceeded"));
    }
    let mut values: HashMap<ValueId, String> = HashMap::new();
    let mut computed_uses: HashMap<ValueId, usize> = HashMap::new();
    for (index, ((id, ty), expected)) in block.params.iter().zip(&signature.params).enumerate() {
        if ty != expected {
            return Err(GateRefusal::new("entry-parameters", "bitwise parameter type mismatch"));
        }
        if values.insert(*id, format!("p{index}")).is_some() {
            return Err(GateRefusal::new("ssa", "bitwise entry defines a parameter twice"));
        }
    }
    let use_value = |id: ValueId,
                     values: &HashMap<ValueId, String>,
                     computed_uses: &mut HashMap<ValueId, usize>|
     -> Result<String, GateRefusal> {
        let rendered = values.get(&id).cloned().ok_or_else(|| {
            GateRefusal::new("ssa", "bitwise tree uses an undefined or forward SSA value")
        })?;
        if let Some(uses) = computed_uses.get_mut(&id) {
            *uses += 1;
            if *uses > 1 {
                return Err(GateRefusal::new(
                    "expression-tree",
                    "computed bitwise nodes may not be shared",
                ));
            }
        }
        Ok(rendered)
    };
    let mut operations = 0;
    let mut returned = None;
    for (position, node) in block.body.iter().enumerate() {
        let rendered = match &node.inst {
            Inst::Const { ty, value } => {
                if UIntCarrier::from_ir(ty) != Some(result) {
                    return Err(GateRefusal::new("ir-carrier", "bitwise Const carrier mismatch"));
                }
                let Constant::Int(value) = value else {
                    return Err(GateRefusal::new(
                        "constant",
                        "a bitwise tree requires canonical Constant::Int",
                    ));
                };
                if *value < 0 || (*value as u128) >= result.modulus() {
                    return Err(GateRefusal::new("constant", "bitwise literal is out of range"));
                }
                value.to_string()
            }
            Inst::BinOp { op, ty, lhs, rhs } => {
                if UIntCarrier::from_ir(ty) != Some(result) {
                    return Err(GateRefusal::new("ir-carrier", "bitwise BinOp carrier mismatch"));
                }
                let token = match op {
                    BinOp::And => "&",
                    BinOp::Or => "|",
                    _ => {
                        return Err(GateRefusal::new(
                            "instruction",
                            "a bitwise tree admits only And/Or",
                        ));
                    }
                };
                operations += 1;
                if operations > EXPRESSION_MAX_OPS {
                    return Err(GateRefusal::new(
                        "expression-bound",
                        "bitwise tree exceeds 32 operations",
                    ));
                }
                let left = use_value(*lhs, &values, &mut computed_uses)?;
                let right = use_value(*rhs, &values, &mut computed_uses)?;
                format!("({left} {token} {right})")
            }
            Inst::Return { values: returned_values } => {
                if position + 1 != block.body.len() || !node.results.is_empty() {
                    return Err(GateRefusal::new(
                        "return",
                        "bitwise Return must be last and define no values",
                    ));
                }
                let [id] = returned_values.as_slice() else {
                    return Err(GateRefusal::new("return", "a bitwise tree returns one value"));
                };
                returned = Some(use_value(*id, &values, &mut computed_uses)?);
                continue;
            }
            _ => {
                return Err(GateRefusal::new(
                    "instruction",
                    "a bitwise tree contains an unsupported instruction or effect",
                ));
            }
        };
        let [id] = node.results.as_slice() else {
            return Err(GateRefusal::new("ssa", "bitwise Const/BinOp must define one value"));
        };
        if values.insert(*id, rendered).is_some() {
            return Err(GateRefusal::new("ssa", "bitwise tree redefines an SSA value"));
        }
        computed_uses.insert(*id, 0);
    }
    if !(1..=EXPRESSION_MAX_OPS).contains(&operations) {
        return Err(GateRefusal::new(
            "expression-bound",
            "a bitwise tree requires 1..=32 operations",
        ));
    }
    let rendering =
        returned.ok_or_else(|| GateRefusal::new("return", "bitwise tree has no final Return"))?;
    if computed_uses.values().any(|count| *count != 1) {
        return Err(GateRefusal::new(
            "expression-tree",
            "every computed value must feed the returned tree exactly once",
        ));
    }
    Ok(ReflectedBitwise { rendering, arity, result })
}

/// Trust (WS5.20): the guarded total division, read EXACTLY as
/// `z = const 0; one = const 1; isz = icmp eq y z; d = select isz one y;
/// q = udiv x d; r = select isz z q; ret r` over entry parameters `x`, `y`.
/// That idiom IS Lean's total `UIntN.div x y` (`x / 0 = 0`; `UDiv` never sees
/// a zero divisor), and it is the reader's one trusted mapping here: any other
/// guard, a dropped guard, swapped arms or a different constant is refused by
/// the reader or disagrees in the kernel.
struct ReflectedDivision {
    arity: usize,
    dividend: usize,
    divisor: usize,
    result: UIntCarrier,
}

fn reflect_total_division(
    signature: &FuncTy,
    function: &Function,
) -> Result<ReflectedDivision, GateRefusal> {
    let (block, parameters, positions) = entry_parameters(signature, function)?;
    let result = UIntCarrier::from_ir(&signature.returns[0]).ok_or_else(|| {
        GateRefusal::new("ir-carrier", "a division result must be exact UInt8/16/32/64")
    })?;
    if parameters.iter().any(|carrier| *carrier != result) {
        return Err(GateRefusal::new(
            "ir-carrier",
            "every division parameter must share the exact result carrier",
        ));
    }
    let carrier_ty = result.ir_ty();
    let [zero, one, is_zero, safe, quotient, selected, returned] = block.body.as_slice() else {
        return Err(GateRefusal::new(
            "division-body",
            "a total division is exactly the seven-node guarded idiom",
        ));
    };
    let mut defined = HashSet::<ValueId>::with_capacity(6);
    let mut fresh = |node: &InstrNode| -> Result<ValueId, GateRefusal> {
        let [id] = node.results.as_slice() else {
            return Err(GateRefusal::new("ssa", "a division node must define exactly one value"));
        };
        if positions.contains_key(id) || !defined.insert(*id) {
            return Err(GateRefusal::new("ssa", "a division node redefines an earlier value"));
        }
        Ok(*id)
    };
    let constant = |node: &InstrNode, expected: i128| -> bool {
        matches!(&node.inst, Inst::Const { ty, value: Constant::Int(v) }
            if *ty == carrier_ty && *v == expected)
    };
    if !constant(zero, 0) {
        return Err(GateRefusal::new("division-body", "the guard must begin with Const 0"));
    }
    let z = fresh(zero)?;
    if !constant(one, 1) {
        return Err(GateRefusal::new("division-body", "the guard's safe divisor must be Const 1"));
    }
    let o = fresh(one)?;
    let Inst::ICmp { op: ICmpOp::Eq, ty, lhs: y, rhs } = &is_zero.inst else {
        return Err(GateRefusal::new("division-body", "the zero test must be icmp eq"));
    };
    let Some(&divisor) = positions.get(y) else {
        return Err(GateRefusal::new(
            "division-body",
            "the zero test must read the divisor parameter",
        ));
    };
    if *ty != carrier_ty || *rhs != z {
        return Err(GateRefusal::new(
            "division-body",
            "the zero test must compare the divisor with 0",
        ));
    }
    let c = fresh(is_zero)?;
    if !matches!(&safe.inst, Inst::Select { ty, cond, then_val, else_val }
        if *ty == carrier_ty && *cond == c && *then_val == o && else_val == y)
    {
        return Err(GateRefusal::new(
            "division-body",
            "the safe divisor must be select(y == 0, 1, y)",
        ));
    }
    let d = fresh(safe)?;
    let Inst::BinOp { op: BinOp::UDiv, ty, lhs: x, rhs: divided_by } = &quotient.inst else {
        return Err(GateRefusal::new("division-body", "the quotient must be an unsigned UDiv"));
    };
    let Some(&dividend) = positions.get(x) else {
        return Err(GateRefusal::new("division-body", "the dividend must be an entry parameter"));
    };
    if *ty != carrier_ty || *divided_by != d {
        return Err(GateRefusal::new(
            "division-body",
            "the quotient must divide by the safe divisor",
        ));
    }
    let q = fresh(quotient)?;
    if !matches!(&selected.inst, Inst::Select { ty, cond, then_val, else_val }
        if *ty == carrier_ty && *cond == c && *then_val == z && *else_val == q)
    {
        return Err(GateRefusal::new(
            "division-body",
            "the result must be select(y == 0, 0, quotient)",
        ));
    }
    let r = fresh(selected)?;
    let Inst::Return { values } = &returned.inst else {
        return Err(GateRefusal::new("division-body", "a division body must end with Return"));
    };
    if values.as_slice() != [r] || !returned.results.is_empty() {
        return Err(GateRefusal::new(
            "return",
            "Return must consume exactly the guarded result and define no values",
        ));
    }
    Ok(ReflectedDivision { arity: parameters.len(), dividend, divisor, result })
}

/// Mint `mint`'s reflection into a scratch clone of the accepted environment
/// and return its value — the MIR lane's side-B discipline (the real
/// environment never acquires a constant as a side effect of a check).
fn mint_in_scratch(
    context: &AcceptedLeanSourceContext<'_>,
    declaration: &Name,
    mint: impl FnOnce(
        &mut clean_kernel::env::Environment,
        &str,
    ) -> Result<trust_spec_elab::Admission, String>,
) -> Result<Expr, GateRefusal> {
    let reflected_name = format!("{declaration}_trust_standalone_reflection");
    let reflected_kernel_name = Name::from_string(&reflected_name);
    let mut scratch = context.environment().clone();
    if scratch.get_const(&reflected_kernel_name).is_some() {
        return Err(GateRefusal::new(
            "reflection-name",
            "the reflection constant's name is already taken in the accepted environment",
        ));
    }
    mint(&mut scratch, &reflected_name)
        .map_err(|detail| GateRefusal::new("reflection-rejected", detail))?;
    scratch.get_const(&reflected_kernel_name).and_then(|c| c.value.clone()).ok_or_else(|| {
        GateRefusal::new(
            "reflection-rejected",
            "the reflected defining equation was accepted but carries no value",
        )
    })
}

/// Trust (WS5.20): the standalone SCALAR vocabulary's kernel check. The plan
/// only selects WHICH reader runs; the reader derives everything from the
/// actual SSA, the frozen producers (or, for the guarded division, the
/// carrier's own `div`) mint the term, and the kernel must decide whole-term
/// definitional equality with the untouched declaration at the exact result
/// carrier.
fn check_scalar_body(
    context: &AcceptedLeanSourceContext<'_>,
    plan: &StandaloneScalarPlan,
    signature: &FuncTy,
    function: &Function,
) -> Result<(Faithful, StandaloneCarrier, StandaloneShape), GateRefusal> {
    let declaration = plan.declaration();
    let source = plan.signature();
    if function.id.index() != 0 || function.ty.index() != 0 {
        return Err(GateRefusal::new(
            "subject-identity",
            "scalar body requires placeholder FuncId(0)/FuncTyId(0)",
        ));
    }
    if function.name != trust_clean_origin::symbol::declaration_symbol(declaration) {
        return Err(GateRefusal::new(
            "subject-name",
            "scalar function name differs from owned source declaration",
        ));
    }
    if !source.hypotheses().is_empty() || !source.preconditions().is_empty() {
        return Err(GateRefusal::new(
            "source-preconditions",
            "scalar body does not admit erased hypotheses or preconditions",
        ));
    }
    let (term, parameters, carrier, shape) = match plan.shape() {
        StandaloneScalarShape::ComparisonConnective { .. } => {
            let read = reflect_comparison_connective(signature, function)?;
            let domains: Vec<_> = read.parameters.iter().map(|c| machine_domain(*c)).collect();
            let term = mint_in_scratch(context, declaration, |env, name| {
                trust_spec_elab::admit_bool_binary_function(
                    env,
                    name,
                    &domains,
                    read.op,
                    read.left.cmp,
                    trust_spec_elab::CmpOperand::Param(read.left.left),
                    trust_spec_elab::CmpOperand::Param(read.left.right),
                    read.right.cmp,
                    trust_spec_elab::CmpOperand::Param(read.right.left),
                    trust_spec_elab::CmpOperand::Param(read.right.right),
                )
            })?;
            (term, read.parameters, StandaloneCarrier::Bool, StandaloneShape::ComparisonConnective)
        }
        StandaloneScalarShape::Bitwise { .. } => {
            let read = reflect_bitwise(signature, function)?;
            let names: Vec<String> = (0..read.arity).map(|i| format!("p{i}")).collect();
            let name_refs: Vec<&str> = names.iter().map(String::as_str).collect();
            let domain = machine_domain(read.result);
            let term = mint_in_scratch(context, declaration, |env, name| {
                trust_spec_elab::admit_expr_function(
                    env,
                    name,
                    &read.rendering,
                    &name_refs,
                    &domain,
                )
            })?;
            (
                term,
                vec![read.result; read.arity],
                StandaloneCarrier::UInt(read.result),
                StandaloneShape::Bitwise,
            )
        }
        StandaloneScalarShape::TotalDivision { .. } => {
            let read = reflect_total_division(signature, function)?;
            let index = |position: usize| {
                u32::try_from(read.arity - 1 - position)
                    .map_err(|_| GateRefusal::new("resource-bound", "division arity exceeds u32"))
            };
            let mut term = Expr::apps(
                read.result.member("div"),
                [Expr::bvar(index(read.dividend)?), Expr::bvar(index(read.divisor)?)],
            );
            for _ in 0..read.arity {
                term = Expr::lam(BinderInfo::Default, read.result.ty_expr(), term);
            }
            (
                term,
                vec![read.result; read.arity],
                StandaloneCarrier::UInt(read.result),
                StandaloneShape::TotalDivision,
            )
        }
    };
    if source.arguments().len() != parameters.len() {
        return Err(GateRefusal::new(
            "source-ir-arity",
            "source and scalar SSA parameter counts differ",
        ));
    }
    for (argument, actual) in source.arguments().iter().zip(&parameters) {
        if UIntCarrier::from_clean(argument.clean()) != Some(*actual)
            || argument.rust() != &actual.rust_ty()
        {
            return Err(GateRefusal::new(
                "source-ir-carrier",
                "source and scalar parameter carriers differ",
            ));
        }
    }
    if StandaloneCarrier::from_clean(source.result().clean()) != Some(carrier)
        || source.result().rust() != &carrier.rust_ty()
    {
        return Err(GateRefusal::new(
            "source-ir-carrier",
            "source and scalar result carriers differ",
        ));
    }
    let faithful =
        check_faithful_for_name(context.environment(), declaration, &term, source.result())
            .map_err(|refusal| GateRefusal::new("kernel-disagreement", refusal.note()))?;
    if faithful.method() != FaithfulnessMethod::DefinitionalEquality {
        return Err(GateRefusal::new(
            "kernel-method",
            "a standalone scalar body requires whole-term definitional equality",
        ));
    }
    if faithful.admitted_at() != &carrier.rust_ty() {
        return Err(GateRefusal::new(
            "kernel-carrier",
            "scalar permission has a different exact carrier",
        ));
    }
    Ok((faithful, carrier, shape))
}

fn check_simple_body(
    context: &AcceptedLeanSourceContext<'_>,
    declaration: &Name,
    source: &CarrierSignature,
    signature: &FuncTy,
    function: &Function,
    reflect: fn(&FuncTy, &Function) -> Result<ReflectedScalar, GateRefusal>,
) -> Result<(Faithful, UIntCarrier), GateRefusal> {
    if function.id.index() != 0 || function.ty.index() != 0 {
        return Err(GateRefusal::new(
            "subject-identity",
            "scalar body requires placeholder FuncId(0)/FuncTyId(0)",
        ));
    }
    if function.name != trust_clean_origin::symbol::declaration_symbol(declaration) {
        return Err(GateRefusal::new(
            "subject-name",
            "scalar function name differs from owned source declaration",
        ));
    }
    if !source.hypotheses().is_empty() || !source.preconditions().is_empty() {
        return Err(GateRefusal::new(
            "source-preconditions",
            "scalar body does not admit erased hypotheses or preconditions",
        ));
    }
    let reflected = reflect(signature, function)?;
    if source.arguments().len() != reflected.parameters.len() {
        return Err(GateRefusal::new(
            "source-ir-arity",
            "source and scalar SSA parameter counts differ",
        ));
    }
    for (argument, actual) in source.arguments().iter().zip(&reflected.parameters) {
        if UIntCarrier::from_clean(argument.clean()) != Some(*actual)
            || argument.rust() != &actual.rust_ty()
        {
            return Err(GateRefusal::new(
                "source-ir-carrier",
                "source and scalar parameter carriers differ",
            ));
        }
    }
    let carrier = reflected.result;
    if UIntCarrier::from_clean(source.result().clean()) != Some(carrier)
        || source.result().rust() != &carrier.rust_ty()
    {
        return Err(GateRefusal::new(
            "source-ir-carrier",
            "source and scalar result carriers differ",
        ));
    }
    let faithful = check_faithful_for_name(
        context.environment(),
        declaration,
        &reflected.term,
        source.result(),
    )
    .map_err(|refusal| GateRefusal::new("kernel-disagreement", refusal.note()))?;
    if faithful.method() != FaithfulnessMethod::DefinitionalEquality {
        return Err(GateRefusal::new(
            "kernel-method",
            "ordinary scalar body requires whole-term definitional equality",
        ));
    }
    if faithful.admitted_at() != &carrier.rust_ty() {
        return Err(GateRefusal::new(
            "kernel-carrier",
            "scalar permission has a different exact carrier",
        ));
    }
    Ok((faithful, carrier))
}

fn require_neutral_metadata(function: &Function) -> Result<(), GateRefusal> {
    // Reflection checks computational SSA, not unrelated proof/contract claims.
    // A fresh decoder remint must not launder arbitrary claims by recomputing
    // their digests. Rebuild a closed neutral shell so future metadata fields
    // also default to refused, rather than maintaining an open-ended denylist.
    let mut neutral =
        Function::new(function.id, function.name.clone(), function.ty, function.entry);
    // The current fixed-width Clean emitter explicitly uses Rust, not C.
    // This pins its bounded IR convention; it is not cross-language ABI proof.
    neutral.calling_conv = CallingConv::Rust;
    neutral.producer = function.producer.clone();
    neutral.blocks = function
        .blocks
        .iter()
        .map(|block| {
            let mut clean = Block::new(block.id);
            clean.params = block.params.clone();
            clean.body = block
                .body
                .iter()
                .map(|node| InstrNode::new(node.inst.clone()).with_results(node.results.clone()))
                .collect();
            clean
        })
        .collect();
    if &neutral != function {
        return Err(GateRefusal::new(
            "standalone-metadata",
            "bounded standalone admission requires Rust ABI, default linkage, and no extra function/instruction proof, contract, attribute, provenance, or debug metadata",
        ));
    }
    Ok(())
}

fn capture_identity(
    context: &AcceptedLeanSourceContext<'_>,
    declaration: &Name,
) -> Result<StandaloneLeanIdentity, GateRefusal> {
    if !context.owns_declaration(declaration) {
        return Err(GateRefusal::new(
            "standalone-source-owner",
            "declaration is not an added eager identity of the accepted source batch",
        ));
    }
    // Planning, kernel lookup, and the sealed faithfulness token all retain
    // this exact Name. Display text is only the IR function's diagnostic label.
    let env = context.environment();
    let info = env.get_const(declaration).ok_or_else(|| {
        GateRefusal::new("standalone-kernel-payload", "owned declaration has no kernel constant")
    })?;
    let kernel_payload_sha256 = canonical_json_sha256(&(
        info,
        env.get_inductive(declaration),
        env.get_constructor(declaration),
        env.get_recursor(declaration),
        env.quotients().find(|val| &val.name == declaration),
    ))
    .map_err(|error| GateRefusal::new("standalone-kernel-payload", error.to_string()))?;
    let source_closure_sha256 = context.source_closure_sha256();
    let owned_declarations_sha256 = context.owned_declarations_sha256();
    if !is_stable_sha256_hex(source_closure_sha256)
        || !is_stable_sha256_hex(owned_declarations_sha256)
    {
        return Err(GateRefusal::new(
            "standalone-source-identity",
            "accepted context has a noncanonical closure digest",
        ));
    }
    Ok(StandaloneLeanIdentity {
        declaration: declaration.clone(),
        source_closure_sha256: source_closure_sha256.to_owned(),
        owned_declarations_sha256: owned_declarations_sha256.to_owned(),
        kernel_payload_sha256,
    })
}

fn subject_digest(
    shape: StandaloneShape,
    identity: &StandaloneLeanIdentity,
    signature: &FuncTy,
    function: &Function,
) -> Result<ProofDigest, GateRefusal> {
    // Canonical JSON frames only the source identity. The existing canonical
    // binary module codec binds ALL function fields, including exact constants.
    let identity_sha256 = canonical_json_sha256(&(
        "trust.clean.standalone-source-identity.v1",
        &identity.source_closure_sha256,
        &identity.owned_declarations_sha256,
        &identity.declaration,
        &identity.kernel_payload_sha256,
    ))
    .map_err(|error| GateRefusal::new("standalone-source-identity", error.to_string()))?;
    let domain = match shape {
        StandaloneShape::WrappingBinOp => SUBJECT_MODULE_NAME,
        StandaloneShape::Projection => PROJECTION_SUBJECT_MODULE_NAME,
        StandaloneShape::ConstantUint => CONSTANT_SUBJECT_MODULE_NAME,
        StandaloneShape::WrappingExpression => EXPRESSION_SUBJECT_MODULE_NAME,
        StandaloneShape::Comparison => COMPARISON_SUBJECT_MODULE_NAME,
        StandaloneShape::Select => SELECT_SUBJECT_MODULE_NAME,
        StandaloneShape::ComparisonConnective => CONNECTIVE_SUBJECT_MODULE_NAME,
        StandaloneShape::Bitwise => BITWISE_SUBJECT_MODULE_NAME,
        StandaloneShape::TotalDivision => DIVISION_SUBJECT_MODULE_NAME,
    };
    let mut module = Module::new(format!("{domain}::lean-identity-sha256={identity_sha256}"));
    module.func_types.push(signature.clone());
    module.functions.push(function.clone());
    Ok(module.stable_digest())
}

/// Distinct standalone custody domain; a freely writable stamp alone is never admission.
pub const STANDALONE_CODEGEN_AUTHORITY: &str = "clean-standalone-kernel-gate";

/// Disclosure metadata only. The F1 boundary additionally requires the original
/// private in-memory publication and exact retained signature/function.
#[must_use]
pub fn standalone_codegen_gate_stamp() -> trust_ir::BodyGate {
    trust_ir::BodyGate::Gated { authority: STANDALONE_CODEGEN_AUTHORITY.to_owned(), evidence: None }
}
