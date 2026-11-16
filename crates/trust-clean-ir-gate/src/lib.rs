// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Independent TrustIR -> Clean carrier-faithfulness gate.
//!
//! This production slice is deliberately small and closed: four straight-line
//! body shapes over one exact `UInt8`, `UInt16`, `UInt32`, or `UInt64` carrier
//! — a `Return` of an entry parameter (`projection`), a lone `Const` returned
//! (`constant-uint`), one [`trust_ir::BinOp`] (`Add`, `Sub`, or `Mul`)
//! returned (`wrapping-binop`), or a tree of 2..=32 of those ops over
//! parameters and single-use constants (`composed`); see [`GatedShape`] and
//! [`gate_targets`]. The gate reads the *actual emitted* [`trust_ir::Function`],
//! reflects that SSA body into a closed Clean term WITHOUT consulting the
//! sealed plan's operands (the body decides its own shape; the plan is then
//! required to agree), and asks `clean_kernel` (through
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
use trust_clean_origin::{CleanOriginPlan, CleanOriginShape, Faithful, FaithfulnessMethod};
use trust_ir::proof::ProofDigest;
use trust_ir::ty::{FuncTy, Ty};
use trust_ir::value::ValueId;
use trust_ir::{BinOp, Constant, Function, Inst, Module, Producer};
use trust_types::Ty as RustTy;
use trust_types::admissible_body::ArithExpr;

const WRAPPING_SUBJECT_MODULE_NAME: &str = "@trust-internal::clean-wrapping-binop-gate-subject-v1";
const SUBJECT_MODULE_NAME: &str = "@trust-internal::clean-carrier-gate-subject-v2";
// A distinct domain for the composed family, so adding it moves no existing
// subject digest (the 419cd81db6 precedent).
const COMPOSED_SUBJECT_MODULE_NAME: &str =
    "@trust-internal::clean-carrier-gate-composed-subject-v1";
// Plan step 3.1: one domain per new family, so adding them moves no existing subject digest.
const SELECT_SUBJECT_MODULE_NAME: &str = "@trust-internal::clean-carrier-gate-select-subject-v1";
const COMPARISON_SUBJECT_MODULE_NAME: &str =
    "@trust-internal::clean-carrier-gate-comparison-value-subject-v1";
const BOOL_VALUE_SUBJECT_MODULE_NAME: &str =
    "@trust-internal::clean-carrier-gate-bool-value-subject-v1";

/// In-memory standalone Lean admission from an accepted, retained source batch.
pub mod standalone;

/// Reauthenticate a published carrier subject after identity-ABI codegen relocation.
/// This reader does not change any backend's admission policy.
pub mod codegen;
/// Independent, non-authorizing reflection of actual direct-call SSA bodies.
pub mod rust_calls;
pub use codegen::{CodegenRelocation, authenticate_codegen};

/// Plan step 3.1: the select, comparison-value and Bool-value families (coverage; not join
/// targets — see the module docs).
pub mod family;
pub use family::{
    BoolSpelling, BranchSpelling, FAMILY_SHAPE_TAGS, FamilyReading, Leaf, gate_reflects_family,
    read_family,
};

/// A fail-closed refusal from the wrapping-binop carrier gate.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GateRefusal {
    stage: &'static str,
    detail: String,
}

impl GateRefusal {
    pub(crate) fn new(stage: &'static str, detail: impl Into<String>) -> Self {
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

/// Plan step 3.4 (docs/design/2026-10-02-step3-lean-through-trust-ir.md §4.1, D36):
/// the codegen authority a carrier-gated Clean-origin Function carries in its
/// `trust_ir::Function::body_gate`.
///
/// The stamp alone proves nothing: trust-ir's `BodyGate` is free-form and never interpreted by
/// the format, so anyone can write the string. It is honored only beside a session ledger entry
/// whose [`PublishedTrustIrFaithful`] authenticates the exact stamped Function
/// ([`PublishedTrustIrFaithful::authenticate_function`]) in the compilation that minted it. It is
/// a CODEGEN LICENSE, never a proof grade (design §4.5): no obligation, certificate or summary
/// enters the module, and no reader may treat it as `Certified` or `Trusted` evidence about the
/// declaration.
pub const CLEAN_CARRIER_GATE_AUTHORITY: &str = "clean-carrier-gate";

/// The `body_gate` value [`CLEAN_CARRIER_GATE_AUTHORITY`] stamps.
#[must_use]
pub fn clean_carrier_gate_stamp() -> trust_ir::BodyGate {
    trust_ir::BodyGate::Gated { authority: CLEAN_CARRIER_GATE_AUTHORITY.to_string(), evidence: None }
}

fn has_clean_carrier_gate_stamp(body_gate: Option<&trust_ir::BodyGate>) -> bool {
    matches!(
        body_gate,
        Some(trust_ir::BodyGate::Gated { authority, evidence: None })
            if authority == CLEAN_CARRIER_GATE_AUTHORITY
    )
}

/// Plan step 3.4 (design §4.2): the kernel context a carrier-gate verdict was decided in — I7's
/// verdict-digest fields (08-04 §7). The island batch's dependency-closure environment digest of
/// the declaration (`trust_clean_origin::admission::environment_digest_for_name`, mode
/// `ENVIRONMENT_DIGEST_MODE_DEPENDENCY_CLOSURE`) and the Clean kernel version.
///
/// Computed only from a live environment ([`Self::of`]); there is no parser and no other
/// constructor, so a value of this type always names an environment some code in this process
/// actually digested. It is READABLE (disclosure), and it is not authority by itself: a
/// [`TrustIrFaithful`] binds the one it was minted in, and authentication compares it, so a token
/// can never be read against another environment (increment 6 inherits the comparison).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GateEnvironment {
    environment_digest: String,
    kernel_version: &'static str,
}

impl GateEnvironment {
    /// Digest `declaration`'s dependency closure in `env`, and record this kernel's version.
    /// A missing declaration, an encoding failure or a resource bound is a refusal, never a
    /// digest over part of the closure.
    pub fn of(env: &Environment, declaration: &Name) -> Result<Self, GateRefusal> {
        let digest = trust_clean_origin::admission::environment_digest_for_name(env, declaration)
            .map_err(|refusal| GateRefusal::new("environment-digest", refusal.note()))?;
        Ok(Self {
            environment_digest: digest.as_hex().to_owned(),
            kernel_version: trust_clean_origin::local_kernel_version(),
        })
    }

    /// The canonical lowercase-hex SHA-256 of the declaration's dependency closure.
    #[must_use]
    pub fn environment_digest(&self) -> &str {
        &self.environment_digest
    }

    /// The Clean kernel version (`clean_kernel::VERSION`) that decided the verdict.
    #[must_use]
    pub fn kernel_version(&self) -> &'static str {
        self.kernel_version
    }
}

/// The exact unsigned Clean/TrustIR carrier admitted by this increment. Public only as a
/// field of the zero-authority [`FamilyReading`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UIntCarrier {
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

/// The carrier a token was minted at: an exact UInt (the four original shapes, the select
/// family) or `Bool` (plan step 3.1: the comparison-value and Bool-value families' result).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum TokenCarrier {
    UInt(UIntCarrier),
    Bool,
}

impl TokenCarrier {
    pub(crate) fn rust_ty(self) -> RustTy {
        match self {
            Self::UInt(carrier) => carrier.rust_ty(),
            Self::Bool => RustTy::Bool,
        }
    }

    pub(crate) fn clean_name(self) -> &'static str {
        match self {
            Self::UInt(carrier) => carrier.clean_name(),
            Self::Bool => "Bool",
        }
    }
}

/// Plan step 3.1: the select family's body form, read from the body alone.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum SelectForm {
    /// The comparison's right operand and both arms are parameters.
    Params,
    /// The comparison's right operand is a literal; both arms are parameters.
    Literal,
    /// At least one arm is a literal.
    Operands,
}

/// The body shape the reflector READ from an emitted Function. Decided from
/// the SSA body alone; [`admit_clean_origin`] then requires the sealed plan to
/// agree, so plan operands never steer the reflection.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum GatedShape {
    /// `Return` of entry parameter `projected` (0-based source position).
    Projection { projected: usize },
    /// One in-range `Const` returned verbatim.
    ConstantUint { value: u64 },
    /// One `Add`/`Sub`/`Mul` over parameters and/or in-range constants.
    WrappingBinOp,
    /// A tree of `ops` (2..=32) `Add`/`Sub`/`Mul` nodes over parameters and
    /// in-range constants: every computed value feeds the returned tree
    /// exactly once, parameters may be reused.
    Composed { ops: usize },
    /// Plan step 3.1: `if <ult|ule|eq> then <arm> else <arm>` at one UInt carrier, spelled as
    /// `icmp` + `select` or as an `icmp` + `condbr` diamond ([`family`]).
    Select { spelling: BranchSpelling, form: SelectForm },
    /// Plan step 3.1: a comparison of two UInt parameters returned as `Bool`.
    ComparisonValue,
    /// Plan step 3.1: `not b` over a `Bool` parameter.
    BoolNot { spelling: BoolSpelling },
    /// Plan step 3.1: `a && b` / `a || b` over `Bool` parameters.
    BoolConnective { spelling: BoolSpelling },
}

impl GatedShape {
    /// The coverage-row tag this shape publishes under (matches the
    /// compiler's `shape_tag` rendering of the sealed plan).
    #[must_use]
    pub fn tag(self) -> &'static str {
        match self {
            Self::Projection { .. } => "projection",
            Self::ConstantUint { .. } => "constant-uint",
            Self::WrappingBinOp => "wrapping-binop",
            Self::Composed { .. } => "composed",
            Self::Select { form: SelectForm::Params, .. } => "select",
            Self::Select { form: SelectForm::Literal, .. } => "select-literal",
            Self::Select { form: SelectForm::Operands, .. } => "select-operands",
            Self::ComparisonValue => "comparison-value",
            Self::BoolNot { .. } => "bool-not",
            Self::BoolConnective { .. } => "bool-connective",
        }
    }

    /// Plan step 3.1: is this one of the [`family`] shapes?
    #[must_use]
    pub fn is_family(self) -> bool {
        matches!(
            self,
            Self::Select { .. }
                | Self::ComparisonValue
                | Self::BoolNot { .. }
                | Self::BoolConnective { .. }
        )
    }

    /// The family shape a body-only [`FamilyReading`] is. The `=`-versus-`==` spelling of an
    /// `icmp eq` select is the plan's choice (see [`family`]) and is not part of the shape.
    #[must_use]
    pub fn of_family_reading(reading: &FamilyReading) -> Self {
        match reading {
            FamilyReading::Select { spelling, rhs, then_arm, else_arm, .. } => {
                let form = match (rhs, then_arm, else_arm) {
                    (_, Leaf::Literal(_), _) | (_, _, Leaf::Literal(_)) => SelectForm::Operands,
                    (Leaf::Literal(_), _, _) => SelectForm::Literal,
                    _ => SelectForm::Params,
                };
                Self::Select { spelling: *spelling, form }
            }
            FamilyReading::Comparison { .. } => Self::ComparisonValue,
            FamilyReading::BoolValue { spelling, kind } => match kind {
                trust_spec_elab::BoolValueKind::Not(_) => Self::BoolNot { spelling: *spelling },
                _ => Self::BoolConnective { spelling: *spelling },
            },
        }
    }
}

/// Coverage-row shape tags this gate can target. The join seam consults it as
/// a belt: a gate token on any other tag is a semantic-finalization error.
pub const GATED_SHAPE_TAGS: &[&str] =
    &["wrapping-binop", "projection", "constant-uint", "composed"];

/// True iff `tag` is a shape this gate reflects.
#[must_use]
pub fn gates_shape(tag: &str) -> bool {
    GATED_SHAPE_TAGS.contains(&tag)
}

/// Does the carrier gate TARGET this sealed plan? A targeted plan MUST mint a
/// [`TrustIrFaithful`] or the compile is fatal; it is never demoted.
///
/// Every targeted shape is targeted only when the source carrier belt admits
/// the plan — exactly the belt [`admit_clean_origin`] re-runs first — AND
/// only when the declaration's own value is already the plan's body
/// ([`CleanOriginPlan::source_is_direct`]): the op or tree of a
/// `WrappingBinOp` / `Composed`, the returned parameter of a `Projection`,
/// the numeral of a `ConstantUint`. `Composed` is additionally targeted only
/// while its node count is inside the SSA reader's own budget (2..=32,
/// `standalone`'s `EXPRESSION_MAX_OPS`). `Projection` and `ConstantUint`
/// legitimately exist at carriers this gate has no reflector for (`Bool`,
/// `Nat`, `BitVec`, erased hypotheses); the belt keeps those off it.
///
/// The direct-source condition exists because a targeted row whose kernel-TV
/// companion is missing is fatal at the join, and the companion
/// (`clean_reflect::denote_source_in_environment`) denotes the ORIGINAL value
/// with no `MData` arm and without unfolding a Lean helper: the only names it
/// resolves in the checked source environment are named class dictionaries
/// (`instHAddUInt64`), read from their stored fields. The planner may reach its shape through a Lean helper
/// (`chain a b := helperAdd a b`, `pathPick a b := pick a b`,
/// `useK a := kFive a`), a prelude definition (`id (a - b)`), an elaborator
/// annotation, or a dead `let` whose value the companion cannot read. While a
/// shape was targeted on the belt alone every such row was fatal — the
/// wrapping helper case measured at stage1 with verification on
/// (docs/audits/2026-09-28-true-state-trust-ir-to-codegen.md M2d), the
/// projection and constant helper cases measured the same way on 2026-09-29
/// ("carrier-gated … `pathPick`/`useK`: the expected kernel-TV companion is
/// missing"); the others reach the same missing companion, measured at crate
/// level (`tests/composed_gate.rs`). Each is now left untargeted, at the tier
/// the companion alone decides, rather than made fatal. A dead `let` the
/// companion DOES read (its `UIntW.{blt,ble,beq}` conditional arm) stays
/// direct, so no row that minted a companion before loses its target.
///
/// The belt is implied by the direct-source condition (every binder `UIntW`
/// at the result width, exactly `arity` of them, so no erased hypothesis) and
/// is kept as the uniform first test: a plan that fails it would be refused
/// by [`admit_clean_origin`] and so be fatal, never admitted.
/// `InductiveProjection` is never targeted: its verdict is a
/// structural-induction proof, not the whole-term definitional equality this
/// gate requires.
#[must_use]
pub fn gate_targets(plan: &CleanOriginPlan) -> bool {
    let within_budget = match plan.shape() {
        CleanOriginShape::WrappingBinOp { .. }
        | CleanOriginShape::Projection { .. }
        | CleanOriginShape::ConstantUint { .. } => true,
        CleanOriginShape::Composed { expr } => {
            (2..=standalone::EXPRESSION_MAX_OPS).contains(&arith_ops(expr))
        }
        _ => return false,
    };
    within_budget
        && source_signature_carrier(plan.signature()).is_ok()
        && plan.source_is_direct()
}

/// Wrapping-op NODES in a composed tree (leaves count zero).
fn arith_ops(expr: &ArithExpr) -> usize {
    match expr {
        ArithExpr::Operand(_) => 0,
        ArithExpr::Bin { left, right, .. } => 1 + arith_ops(left) + arith_ops(right),
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
    carrier: TokenCarrier,
    shape: GatedShape,
    /// Plan step 3.4 (design §4.2): the environment the kernel decided in.
    environment: GateEnvironment,
}

/// Authentication of the exact Function as it will occur in the published
/// module.
///
/// This is deliberately a second sealed value rather than an accessor on
/// [`TrustIrFaithful`]. The mint-time token covers the collector's placeholder
/// IDs and provenance. Only [`TrustIrFaithful::authenticate_published`] can
/// prove that the publisher changed exactly `id`, `ty`, `producer` and (plan
/// step 3.4) the [`CLEAN_CARRIER_GATE_AUTHORITY`] stamp, reflect the relocated
/// body again, and bind the resulting final subject digest.
///
/// Plan step 3.4 (design §4.1 part 2): this is the value a session ledger
/// holds. It keeps the source identity it was authenticated for and the
/// [`GateEnvironment`] of the verdict, and its [`Self::ledger_digest`] binds the
/// final subject digest to I7's verdict fields (environment digest, kernel
/// version, carrier decision, gate method) and the reflected shape. It is not
/// `Clone`, has no public constructor and no serializer: a ledger entry exists
/// only in the compilation whose join authenticated it, and is never cached or
/// read from an artifact (design §4.3).
#[derive(Debug)]
pub struct PublishedTrustIrFaithful {
    subject_digest: ProofDigest,
    carrier: TokenCarrier,
    shape: GatedShape,
    environment: GateEnvironment,
    source_def_index: u32,
    rust_def_path: String,
    ledger_digest: ProofDigest,
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
        // The append subject is the registry's SOURCE spelling (`«A.b»` is one
        // component). Read it with the parser the compiler used to derive the
        // plan's declaration from that same string, and compare kernel names
        // exactly; `Name::from_string` is a dotted-display reader and would
        // split or keep the guillemets, so it named a different constant.
        let subject = trust_certify::clean_island::island_source_name(clean_name)
            .map_err(|reason| GateRefusal::new("token-name", reason))?;
        if self.faithful.declaration() != &subject {
            let permission = self.faithful.declaration();
            return Err(GateRefusal::new(
                "token-name",
                format!(
                    "permission names `{}` but append subject names `{clean_name}`",
                    trust_certify::clean_island::island_source_spelling(permission)
                        .unwrap_or_else(|| format!("{permission:?}"))
                ),
            ));
        }
        if self.faithful.method() != FaithfulnessMethod::DefinitionalEquality {
            return Err(GateRefusal::new(
                "token-method",
                "carrier-gate permission is not a whole-term definitional-equality verdict",
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
        let (shape, carrier) = reflect_shape_and_carrier(self.shape, signature, function)?;
        if shape != self.shape {
            return Err(GateRefusal::new(
                "token-shape",
                format!(
                    "permission is for {:?} but append subject reflects as {:?}",
                    self.shape, shape
                ),
            ));
        }
        if carrier != self.carrier {
            return Err(GateRefusal::new(
                "token-carrier",
                format!(
                    "permission is for {} but append subject reflects at {}",
                    self.carrier.clean_name(),
                    carrier.clean_name()
                ),
            ));
        }
        let actual =
            subject_digest(self.shape, source_def_index, rust_def_path, signature, function);
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

    /// Plan step 3.4 (design §4.2): refuse unless `environment` is the environment this token's
    /// kernel verdict was decided in. The append seam calls it with the environment the
    /// collector says the row comes from; increment 6 calls it with the consuming
    /// compilation's own digest of the transported sources.
    pub fn authenticate_environment(
        &self,
        environment: &GateEnvironment,
    ) -> Result<(), GateRefusal> {
        if environment != &self.environment {
            return Err(GateRefusal::new(
                "token-environment",
                format!(
                    "permission was decided in environment {} (Clean kernel {}), but the subject \
                     is presented from environment {} (Clean kernel {}); a carrier-gate verdict \
                     is never read against another environment",
                    self.environment.environment_digest,
                    self.environment.kernel_version,
                    environment.environment_digest,
                    environment.kernel_version
                ),
            ));
        }
        Ok(())
    }

    /// The environment this token's kernel verdict was decided in (disclosure).
    #[must_use]
    pub fn environment(&self) -> &GateEnvironment {
        &self.environment
    }

    /// Rebind an authenticated placeholder subject to its exact published
    /// identity and return a digest for that final subject.
    ///
    /// This method first authenticates `original` against the kernel-minted
    /// token. It then proves by whole-`Function` equality that publication
    /// changed only the explicitly non-computational placement fields: `id`,
    /// `ty`, and `producer` (the final producer must be `Clean`), plus — plan
    /// step 3.4 — `body_gate`, which may become exactly
    /// [`clean_carrier_gate_stamp`] and nothing else. Finally it independently
    /// reflects `published` again. No caller can construct the returned sealed
    /// value directly.
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
                    "published Clean-origin producer is {:?}, expected Clean",
                    published.producer
                ),
            ));
        }
        let mut permitted = original.clone();
        permitted.id = published.id;
        permitted.ty = published.ty;
        permitted.producer = Some(Producer::Clean);
        // Plan step 3.4 (design §4.1 part 1): the ONE licensing claim publication may add is
        // the carrier stamp, spelled exactly. Any other `body_gate` (another authority,
        // `Ungated`, a blank authority) is a field change and refused below.
        if has_clean_carrier_gate_stamp(published.body_gate.as_ref()) {
            permitted.body_gate = published.body_gate.clone();
        }
        if &permitted != published {
            return Err(GateRefusal::new(
                "published-relocation",
                "publication changed a Function field other than id, ty, producer, or the \
                 clean-carrier-gate stamp",
            ));
        }

        let (shape, carrier) = reflect_shape_and_carrier(self.shape, signature, published)?;
        if shape != self.shape {
            return Err(GateRefusal::new(
                "published-shape",
                format!(
                    "published subject reflects as {:?}, permission is for {:?}",
                    shape, self.shape
                ),
            ));
        }
        if carrier != self.carrier {
            return Err(GateRefusal::new(
                "published-carrier",
                format!(
                    "published subject reflects at {}, permission is for {}",
                    carrier.clean_name(),
                    self.carrier.clean_name()
                ),
            ));
        }
        let final_digest =
            subject_digest(self.shape, source_def_index, rust_def_path, signature, published);
        Ok(PublishedTrustIrFaithful {
            subject_digest: final_digest,
            carrier: self.carrier,
            shape: self.shape,
            environment: self.environment.clone(),
            source_def_index,
            rust_def_path: rust_def_path.to_owned(),
            ledger_digest: ledger_digest(final_digest, &self.environment, self.carrier, self.shape),
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

    /// The body shape the reflector read at mint time.
    #[must_use]
    pub fn shape(&self) -> GatedShape {
        self.shape
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

    /// The body shape inherited from the authenticated mint-time token.
    #[must_use]
    pub fn shape(&self) -> GatedShape {
        self.shape
    }

    /// Plan step 3.4: the environment the verdict was decided in (disclosure; bound into
    /// [`Self::ledger_digest`]).
    #[must_use]
    pub fn environment(&self) -> &GateEnvironment {
        &self.environment
    }

    /// The source `DefIndex` this entry was authenticated for.
    #[must_use]
    pub fn source_def_index(&self) -> u32 {
        self.source_def_index
    }

    /// The Rust-side `def_path` (the mixed-link key) this entry was authenticated for.
    #[must_use]
    pub fn rust_def_path(&self) -> &str {
        &self.rust_def_path
    }

    /// Plan step 3.4 (design §4.2): SHA-256 over the final subject digest, the environment
    /// digest, the Clean kernel version, the carrier decision, the gate method and the reflected
    /// shape. Disclosed beside the subject digest; it is what an importer re-earning the verdict
    /// at increment 6 compares, so its fields are I7's.
    #[must_use]
    pub fn ledger_digest(&self) -> ProofDigest {
        self.ledger_digest
    }

    /// Plan step 3.4 (design §4.1, §4.4): authenticate the ledger entry against the Function a
    /// consumer is about to honor, in the module it was published into (same `FuncId`s, same
    /// `FuncTyId`s). Refused unless the Function is `Producer::Clean`, carries exactly
    /// [`clean_carrier_gate_stamp`], reflects again at the entry's shape and carrier, and its
    /// subject digest (and so its ledger digest) is the one the join authenticated: a body
    /// edited after the gate (an `Add` turned into a `Sub`), a moved signature, another source
    /// identity or a missing or foreign stamp all refuse. Relocation into another module (F1's
    /// rename and `FuncId` remap) is NOT accepted here; that is the third rebind,
    /// `authenticate_codegen`, plan step 3.6.
    pub fn authenticate_function(
        &self,
        signature: &FuncTy,
        function: &Function,
    ) -> Result<(), GateRefusal> {
        if function.producer.as_ref() != Some(&Producer::Clean) {
            return Err(GateRefusal::new(
                "ledger-producer",
                format!("the Function's producer is {:?}, expected Clean", function.producer),
            ));
        }
        if !has_clean_carrier_gate_stamp(function.body_gate.as_ref()) {
            return Err(GateRefusal::new(
                "ledger-stamp",
                format!(
                    "the Function carries body_gate {:?}, not the `{CLEAN_CARRIER_GATE_AUTHORITY}` \
                     stamp its ledger entry was authenticated with",
                    function.body_gate
                ),
            ));
        }
        let (shape, carrier) = reflect_shape_and_carrier(self.shape, signature, function)?;
        if shape != self.shape || carrier != self.carrier {
            return Err(GateRefusal::new(
                "ledger-shape",
                format!(
                    "the Function reflects as {shape:?} at {}, its ledger entry is for {:?} at {}",
                    carrier.clean_name(),
                    self.shape,
                    self.carrier.clean_name()
                ),
            ));
        }
        let actual = subject_digest(
            self.shape,
            self.source_def_index,
            &self.rust_def_path,
            signature,
            function,
        );
        if actual != self.subject_digest
            || ledger_digest(actual, &self.environment, self.carrier, self.shape)
                != self.ledger_digest
        {
            return Err(GateRefusal::new(
                "ledger-digest",
                format!(
                    "the Function changed after the gate: its ledger entry binds subject {}, the \
                     Function digests to {actual}",
                    self.subject_digest
                ),
            ));
        }
        Ok(())
    }
}

/// Plan step 3.4: the domain of [`PublishedTrustIrFaithful::ledger_digest`]. Its own domain,
/// so no subject digest (pinned byte for byte by `tests/standalone_gate.rs`) moves.
const LEDGER_SUBJECT_MODULE_NAME: &str = "@trust-internal::clean-carrier-gate-ledger-v1";

fn ledger_digest(
    subject: ProofDigest,
    environment: &GateEnvironment,
    carrier: TokenCarrier,
    shape: GatedShape,
) -> ProofDigest {
    // Module names are length-framed by the canonical binary codec; no field can carry `::`
    // (a `sha256:` digest, a hex digest, a semver version, fixed tags).
    Module::new(format!(
        "{LEDGER_SUBJECT_MODULE_NAME}::subject={subject}::environment={}::kernel={}::\
         carrier={}::method=definitional-equality::shape={}",
        environment.environment_digest,
        environment.kernel_version,
        carrier.clean_name(),
        shape.tag()
    ))
    .stable_digest()
}

/// Inspect, reflect, and kernel-check an actual emitted Clean-origin body at
/// one of the gated shapes ([`GatedShape`]).
///
/// Only plans for which [`gate_targets`] holds are in scope. Any refusal is
/// terminal for a targeted body; callers must not demote it to structural or
/// kernel-TV evidence. The reflector reads the Function alone and DECIDES the
/// shape; the sealed plan is then required to agree with what was read
/// (stage `plan-shape`), so a plan can never steer the reflection.
pub fn admit_clean_origin(
    env: &Environment,
    plan: &CleanOriginPlan,
    source_def_index: u32,
    rust_def_path: &str,
    signature: &FuncTy,
    function: &Function,
) -> Result<TrustIrFaithful, GateRefusal> {
    let (faithful, carrier, shape) =
        check_clean_origin(env, plan, signature, function, SubjectNaming::RustLinkSymbol)?;
    // Plan step 3.4 (design §4.2): the environment the verdict was decided in. Refused, never
    // omitted, when the closure cannot be digested.
    let environment = GateEnvironment::of(env, plan.declaration())?;
    Ok(TrustIrFaithful {
        faithful,
        subject_digest: subject_digest(shape, source_def_index, rust_def_path, signature, function),
        carrier: TokenCarrier::UInt(carrier),
        shape,
        environment,
    })
}

/// Plan step 3.1: inspect, read and kernel-check an actual emitted Clean-origin body of the
/// SELECT, COMPARISON-VALUE or BOOL-VALUE family ([`family`]), in the sealed-plan emitter's
/// spelling or in Clean's compiler's (`icmp` + `condbr` diamond, `select` for the Bool
/// operations, `icmp eq` for `==`).
///
/// The same discipline as [`admit_clean_origin`]: placeholder subject identity, the source
/// carrier belt (no erased hypothesis), the body decides family, comparison and operands, the
/// plan must agree, the kernel decides whole-term definitional equality at the result carrier,
/// and the token is private, affine and digest-bound (its own subject domain per family). It is
/// NOT the join's targeting: [`gate_targets`] is unchanged, so no collector mints these tokens
/// for the mixed-link join, which would refuse one (a token on a non-target row is fatal there).
pub fn admit_clean_origin_family(
    env: &Environment,
    plan: &CleanOriginPlan,
    source_def_index: u32,
    rust_def_path: &str,
    signature: &FuncTy,
    function: &Function,
) -> Result<TrustIrFaithful, GateRefusal> {
    check_subject_identity(plan, function, SubjectNaming::LeanDeclaration)?;
    let (faithful, carrier, shape) = family::check_family(env, plan, signature, function)?;
    let environment = GateEnvironment::of(env, plan.declaration())?;
    Ok(TrustIrFaithful {
        faithful,
        subject_digest: subject_digest(shape, source_def_index, rust_def_path, signature, function),
        carrier,
        shape,
        environment,
    })
}

/// The collector's placeholder identity: `FuncId(0)`/`FuncTyId(0)`, and the subject bound to the
/// sealed plan under `naming` (see [`SubjectNaming`]). The family entry
/// ([`admit_clean_origin_family`]) is not wired into the crate lane's join, and its subjects are
/// still Lean-declaration-named, so it passes [`SubjectNaming::LeanDeclaration`] — exactly as
/// strict as before WS5.2; wiring it into the crate lane means passing
/// [`SubjectNaming::RustLinkSymbol`], which refuses a Lean-named subject there.
fn check_subject_identity(
    plan: &CleanOriginPlan,
    function: &Function,
    naming: SubjectNaming,
) -> Result<(), GateRefusal> {
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
    // Trust (WS5.2): the subject is NAMED by the minted Rust item's link-time symbol and the
    // plan's Lean spelling is its DISPLAY PATH (`trust_thir_lower::link_symbol::
    // bind_clean_origin_link_symbol`, applied by the collector before this call). The plan
    // binding is exactly as strict as before — it moved from `name` to `display_path` — and a
    // subject still carrying the Lean spelling as its name was never bound to a symbol, so it
    // is refused rather than minted a token that authenticates a non-symbol name. The symbol
    // itself is bound into the token's subject digest with the rest of the Function.
    let lean = trust_clean_origin::symbol::declaration_symbol(plan.declaration());
    match naming {
        SubjectNaming::RustLinkSymbol => {
            if function.display_path.as_deref() != Some(lean.as_str())
                || function.name.is_empty()
                || function.name == lean
            {
                return Err(GateRefusal::new(
                    "subject-name",
                    format!(
                        "function is named `{}` with display path {:?}, but the sealed plan \
                         `{}` requires display path `{lean}` and a bound Rust link-time symbol \
                         as the name",
                        function.name,
                        function.display_path,
                        plan.name()
                    ),
                ));
            }
        }
        // WS5.2 moved the crate lane's binding from `name` to `display_path`; the
        // standalone lane has no Rust item, so its binding stays on `name`, exactly as
        // strict as before (and `require_neutral_metadata` refuses any display path).
        SubjectNaming::LeanDeclaration => {
            if function.name != lean {
                return Err(GateRefusal::new(
                    "subject-name",
                    format!(
                        "function is named `{}` but sealed plan is `{}`",
                        function.name,
                        plan.name()
                    ),
                ));
            }
        }
    }
    Ok(())
}

/// Re-reflect a subject for authentication, with the reader that minted `expected`: the
/// original bounded reflector for the four original shapes, the family reader for the plan
/// step 3.1 families. A family token never authenticates through the original reader, nor the
/// reverse, because the readers' grammars are disjoint and the shape must match exactly.
fn reflect_shape_and_carrier(
    expected: GatedShape,
    signature: &FuncTy,
    function: &Function,
) -> Result<(GatedShape, TokenCarrier), GateRefusal> {
    if expected.is_family() {
        let reading = family::read_family(signature, function)?;
        let carrier = match &reading {
            FamilyReading::Select { carrier, .. } => TokenCarrier::UInt(*carrier),
            FamilyReading::Comparison { .. } | FamilyReading::BoolValue { .. } => {
                TokenCarrier::Bool
            }
        };
        Ok((GatedShape::of_family_reading(&reading), carrier))
    } else {
        let reflected = reflect_gated(signature, function)?;
        Ok((reflected.shape, TokenCarrier::UInt(reflected.carrier)))
    }
}

/// How the subject Function is NAMED — the one thing the crate lane and the
/// standalone Lean lane disagree about, so it is an explicit input of the shared
/// check rather than a rule one lane silently imposes on the other.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum SubjectNaming {
    /// The crate lane (WS5.2): `Function.name` is the minted Rust item's bound
    /// link-time symbol and the plan's Lean spelling is its `display_path`.
    RustLinkSymbol,
    /// The standalone Lean lane: no Rust item exists, so there is no link-time
    /// symbol to bind; `Function.name` is the Lean declaration symbol itself —
    /// the same rule every other standalone reader applies
    /// (`standalone::check_simple_body`).
    LeanDeclaration,
}

/// The rustc mixed-link join's check: [`gate_targets`] (its kernel-TV
/// companion must be able to read the row), then [`check_emitted_body`].
fn check_clean_origin(
    env: &Environment,
    plan: &CleanOriginPlan,
    signature: &FuncTy,
    function: &Function,
    naming: SubjectNaming,
) -> Result<(Faithful, UIntCarrier, GatedShape), GateRefusal> {
    if !gate_targets(plan) {
        return Err(GateRefusal::new(
            "target-shape",
            format!(
                "`{}` is not a carrier-gate target: only Projection / ConstantUint / \
                 WrappingBinOp / Composed (Composed at 2..=32 ops) plans whose \
                 declaration's own value is already that parameter, numeral, op or \
                 tree (no helper call unfolded) at an exact UInt8/16/32/64 carrier \
                 with no erased hypothesis are admitted by this gate",
                plan.name()
            ),
        ));
    }
    check_emitted_body(env, plan, signature, function, naming)
}

/// Shared actual-SSA/kernel check. Source identity is bound by each caller's
/// distinct token mint, never by synthesizing a Rust identity for Lean input.
///
/// The body check without the JOIN's targeting policy: the body reflects, its
/// shape agrees with the plan, and the whole term is kernel-defeq to the
/// declaration. [`check_clean_origin`] adds [`gate_targets`] in front of it
/// for the rustc mixed-link join, whose kernel-TV companion cannot read a
/// helper head; the standalone lane ([`check_wrapping_binop`]) has no companion
/// and no lower tier, and the kernel unfolds the helper itself, so a
/// transparent helper call (`call8 := helper8 a b`) is admitted there as it
/// was before the join's policy reached it (37e92f7922c).
fn check_emitted_body(
    env: &Environment,
    plan: &CleanOriginPlan,
    signature: &FuncTy,
    function: &Function,
    naming: SubjectNaming,
) -> Result<(Faithful, UIntCarrier, GatedShape), GateRefusal> {
    check_subject_identity(plan, function, naming)?;

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
    let reflected = reflect_gated(signature, function)?;
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
    // The plan must agree with what the body-only reflection read. Kernel
    // defeq below is the authority; this is the exact-set belt that stops a
    // plan operand and an emitted body from disagreeing silently.
    let agrees = match (plan.shape(), reflected.shape) {
        (CleanOriginShape::WrappingBinOp { .. }, GatedShape::WrappingBinOp) => true,
        (
            CleanOriginShape::Projection { projected },
            GatedShape::Projection { projected: read },
        ) => *projected == read,
        (CleanOriginShape::ConstantUint { value }, GatedShape::ConstantUint { value: read }) => {
            *value == u128::from(read)
        }
        (CleanOriginShape::Composed { expr }, GatedShape::Composed { ops }) => {
            arith_ops(expr) == ops
        }
        _ => false,
    };
    if !agrees {
        return Err(GateRefusal::new(
            "plan-shape",
            format!(
                "sealed plan is {:?} but the emitted body reflects as {:?}",
                plan.shape(),
                reflected.shape
            ),
        ));
    }

    let faithful = trust_clean_origin::gate::check_faithful_for_name(
        env,
        plan.declaration(),
        &reflected.term,
        plan.result_carrier(),
    )
    .map_err(|refusal| GateRefusal::new("kernel-disagreement", refusal.note()))?;
    if faithful.method() != FaithfulnessMethod::DefinitionalEquality {
        return Err(GateRefusal::new(
            "kernel-method",
            "the bounded carrier gate requires whole-term definitional equality",
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

    Ok((faithful, reflected.carrier, reflected.shape))
}

/// Standalone wrapping tokens retain their original bounded grammar. Sharing
/// the SSA/kernel check must not admit a projection under a wrapping token.
fn check_wrapping_binop(
    env: &Environment,
    plan: &CleanOriginPlan,
    signature: &FuncTy,
    function: &Function,
) -> Result<(Faithful, UIntCarrier), GateRefusal> {
    if !matches!(plan.shape(), CleanOriginShape::WrappingBinOp { .. }) {
        return Err(GateRefusal::new(
            "target-shape",
            "only CleanOriginShape::WrappingBinOp is admitted by this gate",
        ));
    }
    // Standalone lane: no kernel-TV companion and no join, so not the join's
    // targeting policy (`check_clean_origin`); the body check is the whole
    // authority, and the kernel unfolds a transparent helper itself. Only the
    // standalone Lean lane calls this (`standalone::admit_standalone*`), so the
    // subject is named by its Lean declaration symbol (WS5.2).
    let (faithful, carrier, _) =
        check_emitted_body(env, plan, signature, function, SubjectNaming::LeanDeclaration)?;
    Ok((faithful, carrier))
}

/// The original bounded entry point: [`admit_clean_origin`] restricted to
/// `CleanOriginShape::WrappingBinOp` plans. Kept so the wrapping-binop
/// controls keep their exact refusal stages.
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
    admit_clean_origin(env, plan, source_def_index, rust_def_path, signature, function)
}

/// Reflect the exact bounded TrustIR fragment into a closed Clean term and
/// report which [`GatedShape`] the body IS.
///
/// This function has **zero authority by itself**. It is public for independent
/// negative controls; only [`admit_clean_origin`] can mint the private token.
/// Grammar (one block, every instruction accounted for): entry params at the
/// carrier; zero or more `Const` (each in range); at most one `Add`/`Sub`/`Mul`
/// `BinOp`; a final `Return` of exactly one value, which decides the shape —
/// the sole BinOp result (`WrappingBinOp`, every Const must feed it), the sole
/// Const (`ConstantUint`, no BinOp), or an entry parameter (`Projection`, no
/// Const and no BinOp). A single block with TWO OR MORE `Add`/`Sub`/`Mul`
/// `BinOp`s is read by the standalone expression reader instead (`Composed`):
/// a tree whose every
/// Const/BinOp result feeds the returned value exactly once. Anything else
/// refuses.
pub fn reflect_gated(
    signature: &FuncTy,
    function: &Function,
) -> Result<ReflectedFunction, GateRefusal> {
    let carrier = ir_signature_carrier(signature)?;
    // The body, not the plan, picks the reader: the wrapping-op count is a
    // fact about the emitted SSA alone. Only Add/Sub/Mul count, so a body with
    // one of them plus another BinOp keeps the historical `binop` refusal, and
    // a body whose sole Return is not last keeps the `control-flow` refusal of
    // the loop below.
    if let [block] = function.blocks.as_slice() {
        let mut ops = 0usize;
        let mut returns = 0usize;
        for n in &block.body {
            match &n.inst {
                Inst::BinOp { op: BinOp::Add | BinOp::Sub | BinOp::Mul, .. } => ops += 1,
                Inst::Return { .. } => returns += 1,
                _ => {}
            }
        }
        let return_is_last =
            returns == 1 && matches!(block.body.last().map(|n| &n.inst), Some(Inst::Return { .. }));
        if ops >= 2 && return_is_last {
            let reflected = standalone::reflect_expression(signature, function)?;
            if reflected.result != carrier {
                return Err(GateRefusal::new(
                    "ir-carrier",
                    "expression reader and signature disagree about the carrier",
                ));
            }
            return Ok(ReflectedFunction {
                term: reflected.term,
                carrier,
                shape: GatedShape::Composed { ops },
            });
        }
    }
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
    let mut constant_literals = HashMap::<ValueId, u64>::new();
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
    let mut returned: Option<(GatedShape, ValueId)> = None;
    for (position, node) in block.body.iter().enumerate() {
        if returned.is_some() {
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
                constant_literals.insert(id, literal);
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
                let shape = if let Some(output) = binop_output {
                    if *returned_value != output {
                        return Err(GateRefusal::new(
                            "return",
                            "Return does not return the sole BinOp result",
                        ));
                    }
                    if constant_values != used_constants {
                        return Err(GateRefusal::new(
                            "shape",
                            "one or more Const instructions do not feed the sole BinOp",
                        ));
                    }
                    GatedShape::WrappingBinOp
                } else if let Some(literal) = constant_literals.get(returned_value) {
                    if constant_values.len() != 1 {
                        return Err(GateRefusal::new(
                            "shape",
                            "one or more Const instructions do not feed the Return",
                        ));
                    }
                    GatedShape::ConstantUint { value: *literal }
                } else if let Some(index) =
                    block.params.iter().position(|(p, _)| p == returned_value)
                {
                    if !constant_values.is_empty() {
                        return Err(GateRefusal::new(
                            "shape",
                            "a Const instruction does not feed the returned parameter",
                        ));
                    }
                    GatedShape::Projection { projected: index }
                } else {
                    return Err(GateRefusal::new(
                        "return",
                        "Return does not return a parameter, the sole Const, or the sole BinOp \
                         result",
                    ));
                };
                returned = Some((shape, *returned_value));
            }
            Inst::BinOp { .. } => {
                return Err(GateRefusal::new(
                    "shape",
                    "more than one BinOp is outside the gated shapes",
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
    let Some((shape, result_id)) = returned else {
        return Err(GateRefusal::new("control-flow", "block has no final Return"));
    };
    let mut term = values
        .get(&result_id)
        .cloned()
        .ok_or_else(|| GateRefusal::new("ssa", "returned value disappeared"))?;
    for _ in (0..arity).rev() {
        term = Expr::lam(BinderInfo::Default, carrier.ty_expr(), term);
    }
    Ok(ReflectedFunction { term, carrier, shape })
}

/// The original bounded reflector: [`reflect_gated`] restricted to the
/// `WrappingBinOp` shape, keeping the historical `shape` refusal for a body
/// with no BinOp. Zero authority, like the function it wraps.
pub fn reflect_wrapping_binop(
    signature: &FuncTy,
    function: &Function,
) -> Result<ReflectedFunction, GateRefusal> {
    let reflected = reflect_gated(signature, function)?;
    if reflected.shape != GatedShape::WrappingBinOp {
        return Err(GateRefusal::new("shape", "block is not exactly one Add/Sub/Mul BinOp"));
    }
    Ok(reflected)
}

/// A reflection result, not an authority token.
#[derive(Clone, Debug)]
pub struct ReflectedFunction {
    term: Expr,
    carrier: UIntCarrier,
    shape: GatedShape,
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

    /// The shape the body-only reflection read.
    #[must_use]
    pub fn shape(&self) -> GatedShape {
        self.shape
    }
}

fn source_signature_carrier(signature: &CarrierSignature) -> Result<UIntCarrier, GateRefusal> {
    let hypotheses = signature.hypotheses();
    let preconditions = signature.preconditions();
    if !hypotheses.is_empty() || !preconditions.is_empty() {
        return Err(GateRefusal::new(
            "source-preconditions",
            format!(
                "bounded carrier gate requires zero erased hypotheses/preconditions, got {}/{}",
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
    shape: GatedShape,
    source_def_index: u32,
    rust_def_path: &str,
    signature: &FuncTy,
    function: &Function,
) -> ProofDigest {
    // Extending the admitted family must not rewrite the original wrapping
    // subject bytes. The private token retains the independently reflected
    // shape, rechecked at both authentication seams; callers cannot select a
    // digest domain or relabel a new shape as the legacy wrapping family.
    let domain = match shape {
        GatedShape::WrappingBinOp => WRAPPING_SUBJECT_MODULE_NAME,
        GatedShape::Projection { .. } | GatedShape::ConstantUint { .. } => SUBJECT_MODULE_NAME,
        GatedShape::Composed { .. } => COMPOSED_SUBJECT_MODULE_NAME,
        GatedShape::Select { .. } => SELECT_SUBJECT_MODULE_NAME,
        GatedShape::ComparisonValue => COMPARISON_SUBJECT_MODULE_NAME,
        GatedShape::BoolNot { .. } | GatedShape::BoolConnective { .. } => {
            BOOL_VALUE_SUBJECT_MODULE_NAME
        }
    };
    // Module names are length-framed by the canonical binary codec, so this
    // binds the Rust-side mixed-link key without an ad hoc concatenation hash.
    let mut module =
        Module::new(format!("{domain}::def-index={source_def_index}::def-path={rust_def_path}"));
    module.func_types.push(signature.clone());
    module.functions.push(function.clone());
    module.stable_digest()
}

#[cfg(test)]
mod tests {
    use clean_kernel::{BinderInfo, Level};
    use trust_clean_carrier::carrier_signature_with_hypotheses_for;

    use super::*;

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
    fn composed_targeting_budget_is_the_planner_cap_exactly() {
        // A planner cap above the reader's budget would leave the deeper trees
        // untargeted (fail-safe, not fatal) — but silently. Raising either
        // side must be a decision that also moves this pin.
        assert_eq!(standalone::EXPRESSION_MAX_OPS, trust_clean_origin::COMPOSED_MAX_OPS);
    }

    #[test]
    fn bitvec_is_distinct_from_uint_even_at_a_supported_machine_width() {
        assert_eq!(UIntCarrier::from_clean(CleanType::BitVec(64)), None);
        assert_eq!(UIntCarrier::from_clean(CleanType::UInt(64)), Some(UIntCarrier::U64));
    }
}
