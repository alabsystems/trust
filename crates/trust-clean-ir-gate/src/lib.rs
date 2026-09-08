// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Independent TrustIR -> Clean carrier-faithfulness gate.
//!
//! This first production slice is intentionally tiny: one straight-line
//! [`trust_ir::BinOp`] (`Add`, `Sub`, or `Mul`) over one exact `UInt8`,
//! `UInt16`, `UInt32`, or `UInt64` carrier, followed by `Return`. The gate
//! reads the *actual emitted* [`trust_ir::Function`], reflects that SSA body
//! into a closed Clean term, and asks `clean_kernel` (through
//! [`trust_clean_origin::check_faithful`]) whether it is definitionally equal
//! to the kernel-checked declaration.
//!
//! There is deliberately no production dependency on `trust-clean-ir`, the
//! emitter. This crate owns its type map, instruction reader, Clean primitive
//! map, value environment, and subject digest. The emitter is a dev-dependency
//! only so tests can supply realistic adversarial inputs.
//!
//! A successful check returns [`TrustIrFaithful`], whose fields and constructor
//! are private. The token binds the kernel verdict to the exact function and
//! signature, source definition index, and Rust-side mixed-link key through
//! `Module::stable_digest`; [`TrustIrFaithful::authenticate`] recomputes that
//! placeholder digest at the append seam, and
//! [`TrustIrFaithful::authenticate_published`] permits only the explicit
//! id/type/provenance relocation before minting the final disclosed digest.
//! Reflecting alone is never proof authority.

use std::collections::{HashMap, HashSet};

use clean_kernel::env::Environment;
use clean_kernel::expr::{BinderInfo, Expr};
use clean_kernel::name::Name;
use trust_clean_carrier::{CarrierSignature, CleanType};
use trust_clean_origin::{
    CleanOriginPlan, CleanOriginShape, Faithful, FaithfulnessMethod, check_faithful,
};
use trust_ir::proof::ProofDigest;
use trust_ir::ty::{FuncTy, Ty};
use trust_ir::value::ValueId;
use trust_ir::{BinOp, Constant, Function, Inst, Module, Producer};
use trust_types::Ty as RustTy;

const SUBJECT_MODULE_NAME: &str = "@trust-internal::clean-wrapping-binop-gate-subject-v1";

/// A fail-closed refusal from the wrapping-binop carrier gate.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GateRefusal {
    stage: &'static str,
    detail: String,
}

impl GateRefusal {
    fn new(stage: &'static str, detail: impl Into<String>) -> Self {
        Self { stage, detail: detail.into() }
    }

    /// Stable short class for machine-readable tests and diagnostics.
    #[must_use]
    pub fn stage(&self) -> &'static str {
        self.stage
    }

    /// Operator-facing detail. A refusal never authorizes a lower tier.
    #[must_use]
    pub fn note(&self) -> String {
        format!("{}: {}", self.stage, self.detail)
    }
}

impl std::fmt::Display for GateRefusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.note())
    }
}

impl std::error::Error for GateRefusal {}

/// The exact unsigned Clean/TrustIR carrier admitted by this increment.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum UIntCarrier {
    U8,
    U16,
    U32,
    U64,
}

impl UIntCarrier {
    fn from_clean(clean: CleanType) -> Option<Self> {
        match clean {
            CleanType::UInt(8) => Some(Self::U8),
            CleanType::UInt(16) => Some(Self::U16),
            CleanType::UInt(32) => Some(Self::U32),
            CleanType::UInt(64) => Some(Self::U64),
            _ => None,
        }
    }

    fn from_ir(ty: &Ty) -> Option<Self> {
        match ty {
            Ty::U8 => Some(Self::U8),
            Ty::U16 => Some(Self::U16),
            Ty::U32 => Some(Self::U32),
            Ty::U64 => Some(Self::U64),
            _ => None,
        }
    }

    fn ir_ty(self) -> Ty {
        match self {
            Self::U8 => Ty::U8,
            Self::U16 => Ty::U16,
            Self::U32 => Ty::U32,
            Self::U64 => Ty::U64,
        }
    }

    fn clean_name(self) -> &'static str {
        match self {
            Self::U8 => "UInt8",
            Self::U16 => "UInt16",
            Self::U32 => "UInt32",
            Self::U64 => "UInt64",
        }
    }

    fn bits(self) -> u32 {
        match self {
            Self::U8 => 8,
            Self::U16 => 16,
            Self::U32 => 32,
            Self::U64 => 64,
        }
    }

    fn modulus(self) -> u128 {
        1u128 << self.bits()
    }

    fn rust_ty(self) -> RustTy {
        RustTy::Int { width: self.bits(), signed: false }
    }

    fn ty_expr(self) -> Expr {
        constant(self.clean_name())
    }

    fn member(self, suffix: &str) -> Expr {
        constant(&format!("{}.{suffix}", self.clean_name()))
    }
}

/// Private, digest-bound permission to publish one carrier-faithful body.
///
/// There is no public constructor, every field is private, and the token is
/// intentionally affine (`Clone` is not implemented). Authentication
/// recomputes the SHA-256 whole-module digest over the supplied source index,
/// mixed-link key, signature, and function.
///
/// ```compile_fail
/// use trust_clean_ir_gate::TrustIrFaithful;
/// # fn forge(
/// #     faithful: trust_clean_origin::Faithful,
/// #     subject_digest: trust_ir::proof::ProofDigest,
/// # ) {
/// let _ = TrustIrFaithful {
///     faithful,
///     subject_digest,
///     carrier: unreachable!(),
/// };
/// # }
/// ```
///
/// ```compile_fail
/// use trust_clean_ir_gate::TrustIrFaithful;
/// # fn replay(token: &TrustIrFaithful) {
/// let _: TrustIrFaithful = token.clone();
/// # }
/// ```
#[derive(Debug)]
pub struct TrustIrFaithful {
    faithful: Faithful,
    subject_digest: ProofDigest,
    carrier: UIntCarrier,
}

/// Authentication of the exact Function as it will occur in the published
/// module.
///
/// This is deliberately a second sealed value rather than an accessor on
/// [`TrustIrFaithful`]. The mint-time token covers the collector's placeholder
/// IDs and provenance. Only [`TrustIrFaithful::authenticate_published`] can
/// prove that the publisher changed exactly `id`, `ty`, and `producer`, reflect
/// the relocated body again, and bind the resulting final subject digest.
#[derive(Debug)]
pub struct PublishedTrustIrFaithful {
    subject_digest: ProofDigest,
    carrier: UIntCarrier,
}

impl TrustIrFaithful {
    /// Re-authenticate this permission against the exact append-seam subject,
    /// including the Rust `def_path` used for mixed-language edge linking.
    ///
    /// The structural reflection is repeated as defense in depth; the digest
    /// then binds every remaining function field, including metadata which has
    /// no computational reading in the reflector.
    pub fn authenticate(
        &self,
        clean_name: &str,
        source_def_index: u32,
        rust_def_path: &str,
        signature: &FuncTy,
        function: &Function,
    ) -> Result<(), GateRefusal> {
        if self.faithful.name() != clean_name {
            return Err(GateRefusal::new(
                "token-name",
                format!(
                    "permission names `{}` but append subject names `{clean_name}`",
                    self.faithful.name()
                ),
            ));
        }
        if self.faithful.method() != FaithfulnessMethod::DefinitionalEquality {
            return Err(GateRefusal::new(
                "token-method",
                "wrapping-binop permission is not a whole-term definitional-equality verdict",
            ));
        }
        let expected_rust = self.carrier.rust_ty();
        if self.faithful.admitted_at() != &expected_rust {
            return Err(GateRefusal::new(
                "token-admitted-carrier",
                format!(
                    "kernel permission was admitted at {:?}, expected independently derived {:?}",
                    self.faithful.admitted_at(),
                    expected_rust
                ),
            ));
        }
        let reflected = reflect_wrapping_binop(signature, function)?;
        if reflected.carrier != self.carrier {
            return Err(GateRefusal::new(
                "token-carrier",
                format!(
                    "permission is for {} but append subject reflects at {}",
                    self.carrier.clean_name(),
                    reflected.carrier.clean_name()
                ),
            ));
        }
        let actual = subject_digest(source_def_index, rust_def_path, signature, function);
        if actual != self.subject_digest {
            return Err(GateRefusal::new(
                "token-digest",
                format!(
                    "body/signature digest changed after the kernel verdict (minted {}, actual {})",
                    self.subject_digest, actual
                ),
            ));
        }
        Ok(())
    }

    /// Rebind an authenticated placeholder subject to its exact published
    /// identity and return a digest for that final subject.
    ///
    /// This method first authenticates `original` against the kernel-minted
    /// token. It then proves by whole-`Function` equality that publication
    /// changed only the three explicitly non-computational placement fields:
    /// `id`, `ty`, and `producer`; the final producer must be `Clean`. Finally
    /// it independently reflects `published` again. No caller can construct
    /// the returned sealed value directly.
    pub fn authenticate_published(
        &self,
        clean_name: &str,
        source_def_index: u32,
        rust_def_path: &str,
        signature: &FuncTy,
        original: &Function,
        published: &Function,
    ) -> Result<PublishedTrustIrFaithful, GateRefusal> {
        self.authenticate(clean_name, source_def_index, rust_def_path, signature, original)?;

        if published.producer.as_ref() != Some(&Producer::Clean) {
            return Err(GateRefusal::new(
                "published-producer",
                format!(
                    "published wrapping-binop producer is {:?}, expected Clean",
                    published.producer
                ),
            ));
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

        let reflected = reflect_wrapping_binop(signature, published)?;
        if reflected.carrier != self.carrier {
            return Err(GateRefusal::new(
                "published-carrier",
                format!(
                    "published subject reflects at {}, permission is for {}",
                    reflected.carrier.clean_name(),
                    self.carrier.clean_name()
                ),
            ));
        }
        Ok(PublishedTrustIrFaithful {
            subject_digest: subject_digest(source_def_index, rust_def_path, signature, published),
            carrier: self.carrier,
        })
    }

    /// Digest of the exact placeholder signature/function authenticated at
    /// mint time. Publishers must disclose the distinct final digest returned
    /// by [`Self::authenticate_published`], never this pre-publication value.
    #[must_use]
    pub fn subject_digest(&self) -> ProofDigest {
        self.subject_digest
    }

    /// Exact carrier tag, for honest disclosure only.
    #[must_use]
    pub fn carrier_tag(&self) -> &'static str {
        self.carrier.clean_name()
    }

    /// Kernel judgment used by this bounded gate.
    #[must_use]
    pub fn method_tag(&self) -> &'static str {
        "definitional-equality"
    }
}

impl PublishedTrustIrFaithful {
    /// Digest of the exact final signature, Function fields, and Rust mixed-link
    /// key authenticated immediately before publication.
    #[must_use]
    pub fn subject_digest(&self) -> ProofDigest {
        self.subject_digest
    }

    /// Exact carrier tag, for honest disclosure only.
    #[must_use]
    pub fn carrier_tag(&self) -> &'static str {
        self.carrier.clean_name()
    }

    /// Kernel judgment inherited from the authenticated mint-time token.
    #[must_use]
    pub fn method_tag(&self) -> &'static str {
        "definitional-equality"
    }
}

/// Inspect, reflect, and kernel-check an actual emitted wrapping-binop body.
///
/// Only `CleanOriginShape::WrappingBinOp` over exact `UInt8/16/32/64` is in
/// scope. Any refusal is terminal for a targeted body; callers must not demote
/// it to structural or kernel-TV evidence.
pub fn admit_wrapping_binop(
    env: &Environment,
    plan: &CleanOriginPlan,
    source_def_index: u32,
    rust_def_path: &str,
    signature: &FuncTy,
    function: &Function,
) -> Result<TrustIrFaithful, GateRefusal> {
    if !matches!(plan.shape(), CleanOriginShape::WrappingBinOp { .. }) {
        return Err(GateRefusal::new(
            "target-shape",
            "only CleanOriginShape::WrappingBinOp is admitted by this gate",
        ));
    }
    if function.id.index() != 0 || function.ty.index() != 0 {
        return Err(GateRefusal::new(
            "subject-identity",
            format!(
                "collector must present placeholder FuncId(0)/FuncTyId(0), got {}/{}",
                function.id.index(),
                function.ty.index()
            ),
        ));
    }
    if function.name != plan.name() {
        return Err(GateRefusal::new(
            "subject-name",
            format!("function is named `{}` but sealed plan is `{}`", function.name, plan.name()),
        ));
    }

    let expected_carrier = source_signature_carrier(plan.signature())?;
    if plan.signature().arguments().len() != signature.params.len() {
        return Err(GateRefusal::new(
            "source-ir-arity",
            format!(
                "sealed source has {} carried arguments but TrustIR signature has {} parameters",
                plan.signature().arguments().len(),
                signature.params.len()
            ),
        ));
    }
    let reflected = reflect_wrapping_binop(signature, function)?;
    if reflected.carrier != expected_carrier {
        return Err(GateRefusal::new(
            "source-ir-carrier",
            format!(
                "sealed source uses {} but TrustIR subject uses {}",
                expected_carrier.clean_name(),
                reflected.carrier.clean_name()
            ),
        ));
    }

    let faithful = check_faithful(env, plan.name(), &reflected.term, plan.result_carrier())
        .map_err(|refusal| GateRefusal::new("kernel-disagreement", refusal.note()))?;
    if faithful.method() != FaithfulnessMethod::DefinitionalEquality {
        return Err(GateRefusal::new(
            "kernel-method",
            "the bounded wrapping-binop gate requires whole-term definitional equality",
        ));
    }
    let expected_rust = expected_carrier.rust_ty();
    if faithful.admitted_at() != &expected_rust {
        return Err(GateRefusal::new(
            "kernel-carrier",
            format!(
                "kernel verdict was admitted at {:?}, independently derived carrier is {:?}",
                faithful.admitted_at(),
                expected_rust
            ),
        ));
    }

    Ok(TrustIrFaithful {
        faithful,
        subject_digest: subject_digest(source_def_index, rust_def_path, signature, function),
        carrier: reflected.carrier,
    })
}

/// Reflect the exact bounded TrustIR fragment into a closed Clean term.
///
/// This function has **zero authority by itself**. It is public for independent
/// negative controls; only [`admit_wrapping_binop`] can mint the private token.
pub fn reflect_wrapping_binop(
    signature: &FuncTy,
    function: &Function,
) -> Result<ReflectedFunction, GateRefusal> {
    let carrier = ir_signature_carrier(signature)?;
    if function.blocks.len() != 1 {
        return Err(GateRefusal::new(
            "control-flow",
            format!("expected exactly one block, got {}", function.blocks.len()),
        ));
    }
    let block = function
        .blocks
        .iter()
        .find(|block| block.id == function.entry)
        .ok_or_else(|| GateRefusal::new("control-flow", "entry block is missing"))?;
    if block.params.len() != signature.params.len() {
        return Err(GateRefusal::new(
            "entry-parameters",
            format!(
                "entry has {} parameters but signature has {}",
                block.params.len(),
                signature.params.len()
            ),
        ));
    }

    let mut values = HashMap::<ValueId, Expr>::new();
    let mut constant_values = HashSet::<ValueId>::new();
    let mut used_constants = HashSet::<ValueId>::new();
    let arity = block.params.len();
    for (index, ((id, actual_ty), expected_ty)) in
        block.params.iter().zip(&signature.params).enumerate()
    {
        if actual_ty != expected_ty || UIntCarrier::from_ir(actual_ty) != Some(carrier) {
            return Err(GateRefusal::new(
                "entry-parameters",
                format!("parameter {index} has type {actual_ty:?}, expected {:?}", carrier.ir_ty()),
            ));
        }
        let bvar = u32::try_from(arity - 1 - index)
            .map_err(|_| GateRefusal::new("resource-bound", "parameter count exceeds u32"))?;
        define_value(&mut values, *id, Expr::bvar(bvar))?;
    }

    let mut binop_output = None;
    let mut returned = false;
    for (position, node) in block.body.iter().enumerate() {
        if returned {
            return Err(GateRefusal::new(
                "control-flow",
                format!("instruction {position} follows Return"),
            ));
        }
        match &node.inst {
            Inst::Const { ty, value } if binop_output.is_none() => {
                require_single_result("Const", &node.results)?;
                require_carrier_ty(carrier, ty, "Const")?;
                let Constant::Int(value) = value else {
                    return Err(GateRefusal::new(
                        "constant",
                        "only canonical non-negative Constant::Int is in scope",
                    ));
                };
                if *value < 0 || (*value as u128) >= carrier.modulus() {
                    return Err(GateRefusal::new(
                        "constant",
                        format!("value {value} is outside {}", carrier.clean_name()),
                    ));
                }
                let literal = u64::try_from(*value)
                    .map_err(|_| GateRefusal::new("constant", "literal does not fit u64"))?;
                let id = node.results[0];
                define_value(
                    &mut values,
                    id,
                    Expr::app(carrier.member("ofNat"), Expr::nat_lit(literal)),
                )?;
                constant_values.insert(id);
            }
            Inst::BinOp { op, ty, lhs, rhs } if binop_output.is_none() => {
                require_single_result("BinOp", &node.results)?;
                require_carrier_ty(carrier, ty, "BinOp")?;
                let suffix = match op {
                    BinOp::Add => "add",
                    BinOp::Sub => "sub",
                    BinOp::Mul => "mul",
                    _ => {
                        return Err(GateRefusal::new(
                            "binop",
                            format!("unsupported operation {op:?}; only Add/Sub/Mul are admitted"),
                        ));
                    }
                };
                let left = values.get(lhs).cloned().ok_or_else(|| {
                    GateRefusal::new("ssa", format!("left operand {lhs:?} is undefined"))
                })?;
                let right = values.get(rhs).cloned().ok_or_else(|| {
                    GateRefusal::new("ssa", format!("right operand {rhs:?} is undefined"))
                })?;
                if constant_values.contains(lhs) {
                    used_constants.insert(*lhs);
                }
                if constant_values.contains(rhs) {
                    used_constants.insert(*rhs);
                }
                let id = node.results[0];
                define_value(&mut values, id, Expr::apps(carrier.member(suffix), [left, right]))?;
                binop_output = Some(id);
            }
            Inst::Return { values: returned_values } => {
                if !node.results.is_empty() {
                    return Err(GateRefusal::new(
                        "return",
                        format!("Return unexpectedly defines {} values", node.results.len()),
                    ));
                }
                let [returned_value] = returned_values.as_slice() else {
                    return Err(GateRefusal::new(
                        "return",
                        format!("expected one return value, got {}", returned_values.len()),
                    ));
                };
                if Some(*returned_value) != binop_output {
                    return Err(GateRefusal::new(
                        "return",
                        "Return does not return the sole BinOp result",
                    ));
                }
                returned = true;
            }
            Inst::BinOp { .. } => {
                return Err(GateRefusal::new(
                    "shape",
                    "more than one BinOp is outside WrappingBinOp scope",
                ));
            }
            Inst::Const { .. } => {
                return Err(GateRefusal::new("shape", "a Const appears after the BinOp"));
            }
            other => {
                return Err(GateRefusal::new(
                    "instruction",
                    format!("unsupported instruction {other:?}"),
                ));
            }
        }
    }
    if !returned {
        return Err(GateRefusal::new("control-flow", "block has no final Return"));
    }
    if constant_values != used_constants {
        return Err(GateRefusal::new(
            "shape",
            "one or more Const instructions do not feed the sole BinOp",
        ));
    }
    let result_id =
        binop_output.ok_or_else(|| GateRefusal::new("shape", "block has no Add/Sub/Mul BinOp"))?;
    let mut term = values
        .get(&result_id)
        .cloned()
        .ok_or_else(|| GateRefusal::new("ssa", "BinOp result disappeared"))?;
    for _ in (0..arity).rev() {
        term = Expr::lam(BinderInfo::Default, carrier.ty_expr(), term);
    }
    Ok(ReflectedFunction { term, carrier })
}

/// A reflection result, not an authority token.
#[derive(Clone, Debug)]
pub struct ReflectedFunction {
    term: Expr,
    carrier: UIntCarrier,
}

impl ReflectedFunction {
    /// The independently reconstructed closed Clean term.
    #[must_use]
    pub fn term(&self) -> &Expr {
        &self.term
    }

    /// Exact carrier tag observed from the TrustIR signature/body.
    #[must_use]
    pub fn carrier_tag(&self) -> &'static str {
        self.carrier.clean_name()
    }
}

fn source_signature_carrier(signature: &CarrierSignature) -> Result<UIntCarrier, GateRefusal> {
    let hypotheses = signature.hypotheses();
    let preconditions = signature.preconditions();
    if !hypotheses.is_empty() || !preconditions.is_empty() {
        return Err(GateRefusal::new(
            "source-preconditions",
            format!(
                "bounded wrapping-binop gate requires zero erased hypotheses/preconditions, got {}/{}",
                hypotheses.len(),
                preconditions.len()
            ),
        ));
    }
    let carrier = UIntCarrier::from_clean(signature.result().clean()).ok_or_else(|| {
        GateRefusal::new(
            "source-carrier",
            format!(
                "result is {}, expected exact UInt8/16/32/64 (BitVec is not this slice)",
                signature.result().clean().name()
            ),
        )
    })?;
    for (index, argument) in signature.arguments().iter().enumerate() {
        if UIntCarrier::from_clean(argument.clean()) != Some(carrier) {
            return Err(GateRefusal::new(
                "source-carrier",
                format!(
                    "argument {index} is {}, expected {}",
                    argument.clean().name(),
                    carrier.clean_name()
                ),
            ));
        }
        if argument.rust() != &carrier.rust_ty() {
            return Err(GateRefusal::new(
                "source-rust-carrier",
                format!(
                    "sealed argument {index} Rust carrier is {:?}, independently derived carrier is {:?}",
                    argument.rust(),
                    carrier.rust_ty()
                ),
            ));
        }
    }
    if signature.result().rust() != &carrier.rust_ty() {
        return Err(GateRefusal::new(
            "source-rust-carrier",
            format!(
                "sealed result Rust carrier is {:?}, independently derived carrier is {:?}",
                signature.result().rust(),
                carrier.rust_ty()
            ),
        ));
    }
    Ok(carrier)
}

fn ir_signature_carrier(signature: &FuncTy) -> Result<UIntCarrier, GateRefusal> {
    if signature.is_vararg || signature.returns.len() != 1 {
        return Err(GateRefusal::new(
            "signature",
            format!(
                "expected non-vararg signature with one result, got vararg={} results={}",
                signature.is_vararg,
                signature.returns.len()
            ),
        ));
    }
    let carrier = UIntCarrier::from_ir(&signature.returns[0]).ok_or_else(|| {
        GateRefusal::new(
            "ir-carrier",
            format!("unsupported TrustIR result type {:?}", signature.returns[0]),
        )
    })?;
    for (index, parameter) in signature.params.iter().enumerate() {
        if UIntCarrier::from_ir(parameter) != Some(carrier) {
            return Err(GateRefusal::new(
                "ir-carrier",
                format!("parameter {index} is {parameter:?}, expected {:?}", carrier.ir_ty()),
            ));
        }
    }
    Ok(carrier)
}

fn require_carrier_ty(
    carrier: UIntCarrier,
    actual: &Ty,
    instruction: &'static str,
) -> Result<(), GateRefusal> {
    if UIntCarrier::from_ir(actual) == Some(carrier) {
        return Ok(());
    }
    Err(GateRefusal::new(
        "instruction-type",
        format!("{instruction} has type {actual:?}, expected {:?}", carrier.ir_ty()),
    ))
}

fn require_single_result(
    instruction: &'static str,
    results: &[ValueId],
) -> Result<(), GateRefusal> {
    if results.len() == 1 {
        return Ok(());
    }
    Err(GateRefusal::new(
        "result-arity",
        format!("{instruction} defines {} values, expected one", results.len()),
    ))
}

fn define_value(
    values: &mut HashMap<ValueId, Expr>,
    id: ValueId,
    term: Expr,
) -> Result<(), GateRefusal> {
    if values.insert(id, term).is_some() {
        return Err(GateRefusal::new("ssa", format!("value {id:?} is defined twice")));
    }
    Ok(())
}

fn constant(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn subject_digest(
    source_def_index: u32,
    rust_def_path: &str,
    signature: &FuncTy,
    function: &Function,
) -> ProofDigest {
    // Module names are length-framed by the canonical binary codec, so this
    // binds the Rust-side mixed-link key without an ad hoc concatenation hash.
    let mut module = Module::new(format!(
        "{SUBJECT_MODULE_NAME}::def-index={source_def_index}::def-path={rust_def_path}"
    ));
    module.func_types.push(signature.clone());
    module.functions.push(function.clone());
    module.stable_digest()
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::{BinderInfo, Level};
    use trust_clean_carrier::carrier_signature_with_hypotheses_for;

    fn c(name: &str) -> Expr {
        Expr::const_(Name::from_string(name), vec![])
    }

    fn pi(domain: Expr, body: Expr) -> Expr {
        Expr::pi(BinderInfo::Default, domain, body)
    }

    #[test]
    fn hypothesis_and_precondition_bearing_source_signature_is_explicitly_refused() {
        let uint8 = c("UInt8");
        let zero = Expr::app(c("UInt8.ofNat"), Expr::nat_lit(0));
        let nonzero = Expr::apps(
            Expr::const_(Name::from_string("Ne"), vec![Level::succ(Level::zero())]),
            [uint8.clone(), Expr::bvar(0), zero],
        );
        let ty = pi(uint8.clone(), pi(nonzero, uint8));
        let signature = carrier_signature_with_hypotheses_for(&ty)
            .expect("control fixture has one carried precondition");
        assert_eq!(signature.hypotheses().len(), 1);
        assert_eq!(signature.preconditions().len(), 1);
        let refusal = source_signature_carrier(&signature)
            .expect_err("W2 must never erase a source precondition");
        assert_eq!(refusal.stage(), "source-preconditions", "{}", refusal.note());
    }

    #[test]
    fn bitvec_is_distinct_from_uint_even_at_a_supported_machine_width() {
        assert_eq!(UIntCarrier::from_clean(CleanType::BitVec(64)), None);
        assert_eq!(UIntCarrier::from_clean(CleanType::UInt(64)), Some(UIntCarrier::U64));
    }
}
