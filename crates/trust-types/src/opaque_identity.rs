// trust-types: occurrence/value identity for every operand carrier whose value no
// lane models (OPAQUE-SCALAR-ID-1, 2026-10-07; OPAQUE-REF-ID-1, 2026-10-07).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

//! Identity for the operand carriers that have NO modeled value.
//!
//! THE DEFECT CLASS THIS CLOSES. The extractor hands the verifier several
//! carriers that stand for "some value we do not model":
//!
//! * [`ConstValue::OpaqueScalar`] — an integer it does not model: a runtime value
//!   (`ptr as usize`, `f32 -> u32` / `f64 -> u64`, `[u8; N] -> uN`,
//!   `MaybeUninit<uN> -> uN`, transparent repr-int enum transmutes) or a constant
//!   it cannot evaluate in a generic body (`size_of::<T>()`, `align_of::<T>()`,
//!   associated consts, `const { .. }` blocks);
//! * the opaque REFERENCE carriers [`ConstValue::OpaqueConst`],
//!   [`ConstValue::UnitVariantRef`], [`ConstValue::EmptyClosureRef`] and
//!   [`ConstValue::StructScalarFieldsRef`] — a
//!   pointer or reference it does not model: a runtime value (`usize as *const T`,
//!   `Box<T> -> Box<dyn Trait>`, an unknown-length `[x; N]`) or a reference constant
//!   (a promoted `&[..]` table, a static, `&None`, `&Struct(..)`);
//! * [`Operand::Unsupported`] — an operand the extractor refused to model.
//!
//! None of them carried an identity, and every solver-facing renderer interned
//! them by a name that is not a value: `__trust_opaque_scalar_u64` (by width),
//! `__unknown_const` (one symbol for EVERY reference carrier) and
//! `__trust_unsupported_operand_{kind}_{detail}` (by diagnostic text). Two
//! different values were one solver term. With one symbol per width,
//! `if a as *const u8 as usize != b as *const u8 as usize { panic!() }` rendered
//! `x == S ∧ y == S ∧ x != y`, UNSAT, so the panic row was PROVED and
//! kernel-certified (OPAQUE-SCALAR-ID-1). With one `__unknown_const`,
//! `let p = x as *const u8; let q = y as *const u8; if p != q { panic!() }` was
//! PROVED and certified the same way, and because that carrier brings no
//! `UnsupportedMir` row, `t[if p == q { 0 } else { 9 }]` and
//! `100 / if p == q { 1 } else { 0 }` were accepted under
//! `-Ztrust-policy=strict` and panic when run (OPAQUE-REF-ID-1).
//!
//! THE MODEL. Every such carrier holds an [`OpaqueOrigin`], and its symbol is
//! spelled from that origin alone (plus a family prefix):
//!
//! * [`OpaqueOrigin::Site`] — the operand's MIR location `(block, stmt)`
//!   (`stmt == stmts.len()` is the terminator) and its position `slot` in that
//!   location's operand walk. Two different sites never share a symbol. A site
//!   symbol is the value its statement produced on its most recent execution:
//!   exactly what the destination's single-definition SSA name denotes, so it
//!   adds no tie that name does not already carry. Lanes that instantiate one
//!   block more than once per formula (CHC transition relations, BMC unrolling,
//!   termination steps) refuse these carriers outright and keep refusing them.
//! * [`OpaqueOrigin::Const`] — an unevaluated constant the extractor keyed by its
//!   item and normalized generic arguments. Equal keys are the same constant of
//!   the same function instance, so they MAY share one symbol; different keys
//!   never do. Only [`ConstValue::OpaqueScalar`] is ever keyed (and serializes
//!   its key); the other carriers are positional only.
//! * [`OpaqueOrigin::Unplaced`] — a carrier no body has placed yet (an in-code
//!   construction). Every production producer places: the extractor at the end
//!   of body extraction, every deserialization of a [`VerifiableBody`], and
//!   trust-vcgen's generation entry for bodies built in code.
//!
//! Positional origins are a pure function of the body's shape, so they are
//! re-derived rather than trusted: [`VerifiableBody::place_opaque_values`]
//! overwrites every positional origin with the operand's CURRENT location, which
//! makes it idempotent and keeps it correct for a body that a pass edited after
//! an earlier placement. They are never serialized, so every legacy JSON dump
//! re-serializes byte-identically (`"OpaqueConst"` stays a bare unit string).
//!
//! THE WIRE (OPAQUE-SCALAR-WIRE-1, 2026-10-07). Two formats carry these types:
//! self-describing JSON (the dumps) and positional bincode (trust-certify's
//! identity bytes, the constant-image round trip). A bincode decoder reads every
//! field of a struct unconditionally, so a field written only sometimes
//! (`skip_serializing_if`) desynchronizes it: it reads the NEXT value's bytes in
//! its place. The positional origins are `#[serde(skip)]` (never written in any
//! format). The one origin a reader cannot recompute, an opaque scalar's constant
//! key, is written by [`serialize_opaque_scalar`]: in JSON only when present (so
//! legacy dumps stay byte-identical), in every non-human-readable format as an
//! ALWAYS-present `key: Option<String>` field. The bincode encoding therefore
//! differs from the pre-2026-10-07 one by that one field; it is self-delimiting,
//! and a keyed and a keyless occurrence are never prefixes of each other.

use std::borrow::Cow;

use serde::{Deserialize, Serialize};

use crate::model::{
    BasicBlock, ConstValue, DatatypeDefs, LocalDecl, Operand, Rvalue, Statement, Terminator, Ty,
    VerifiableBody, VerifiableFunction,
};

/// Where an unmodeled carrier's identity comes from.
///
/// See the module documentation for the semantics of each origin.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Default, Serialize, Deserialize)]
#[non_exhaustive]
pub enum OpaqueOrigin {
    /// Not yet placed in a body. Renders to a family-only symbol, which aliases
    /// every other unplaced occurrence of the family; production bodies never
    /// reach a renderer in this state (see the module documentation).
    #[default]
    Unplaced,
    /// The operand at MIR location `(block, stmt)` (`stmt == stmts.len()` is the
    /// block's terminator), position `slot` in the location's operand walk.
    Site { block: u32, stmt: u32, slot: u32 },
    /// An unevaluated compile-time constant, keyed by the extractor from its
    /// item, its normalized generic arguments and its promoted index. Equal keys
    /// denote the same constant; different keys are never conflated.
    Const { key: String },
}

impl OpaqueOrigin {
    /// Whether this origin is a function of the operand's position alone (and so
    /// is re-derived on load instead of being serialized).
    #[must_use]
    pub fn is_positional(&self) -> bool {
        matches!(self, OpaqueOrigin::Unplaced | OpaqueOrigin::Site { .. })
    }

    /// The origin's injective symbol tag: `unplaced`, `b{block}_s{stmt}_o{slot}`,
    /// or `k` followed by the key's bytes in lowercase hex (never a hash). The
    /// three shapes start with distinct letters and the site shape is fixed-arity,
    /// so a tag followed by `_` and any suffix still decodes to one origin.
    #[must_use]
    pub fn symbol_tag(&self) -> String {
        let mut tag = String::new();
        self.push_symbol_tag(&mut tag);
        tag
    }

    fn push_symbol_tag(&self, out: &mut String) {
        match self {
            OpaqueOrigin::Unplaced => out.push_str("unplaced"),
            OpaqueOrigin::Site { block, stmt, slot } => {
                use std::fmt::Write as _;
                let _ = write!(out, "b{block}_s{stmt}_o{slot}");
            }
            OpaqueOrigin::Const { key } => {
                out.reserve(1 + key.len() * 2);
                out.push('k');
                for byte in key.bytes() {
                    out.push(HEX_LOWER[usize::from(byte >> 4)]);
                    out.push(HEX_LOWER[usize::from(byte & 0xf)]);
                }
            }
        }
    }
}

/// Serializer of [`ConstValue::OpaqueScalar`] (its variant-level
/// `serialize_with`; see the module documentation, "THE WIRE").
///
/// A human-readable format gets the legacy JSON shape: `width`, `signed`, and
/// `origin` only for a keyed ([`OpaqueOrigin::Const`]) occurrence. Any other
/// format gets a FIXED field sequence `width`, `signed`, `key: Option<String>`,
/// so a positional decoder never reads past the variant.
///
/// # Errors
/// Whatever the serializer reports.
#[allow(clippy::trivially_copy_pass_by_ref)] // serde fixes the `&FIELD` signature
pub(crate) fn serialize_opaque_scalar<S: serde::Serializer>(
    width: &u32,
    signed: &bool,
    origin: &OpaqueOrigin,
    serializer: S,
) -> Result<S::Ok, S::Error> {
    use serde::ser::SerializeStruct as _;
    if serializer.is_human_readable() {
        let keyed = !origin.is_positional();
        let mut fields = serializer.serialize_struct("OpaqueScalar", 2 + usize::from(keyed))?;
        fields.serialize_field("width", width)?;
        fields.serialize_field("signed", signed)?;
        if keyed {
            fields.serialize_field("origin", origin)?;
        } else {
            fields.skip_field("origin")?;
        }
        fields.end()
    } else {
        let key = match origin {
            OpaqueOrigin::Const { key } => Some(key.as_str()),
            OpaqueOrigin::Unplaced | OpaqueOrigin::Site { .. } => None,
        };
        let mut fields = serializer.serialize_struct("OpaqueScalar", 3)?;
        fields.serialize_field("width", width)?;
        fields.serialize_field("signed", signed)?;
        fields.serialize_field("key", &key)?;
        fields.end()
    }
}

/// Deserializer of [`ConstValue::OpaqueScalar`] (its variant-level
/// `deserialize_with`), the exact inverse of [`serialize_opaque_scalar`] per
/// format. A positional origin comes back [`OpaqueOrigin::Unplaced`];
/// [`VerifiableBody`]'s deserialization places it.
///
/// # Errors
/// Whatever the deserializer reports for a malformed variant.
pub(crate) fn deserialize_opaque_scalar<'de, D: serde::Deserializer<'de>>(
    deserializer: D,
) -> Result<(u32, bool, OpaqueOrigin), D::Error> {
    #[derive(Deserialize)]
    #[serde(rename = "OpaqueScalar")]
    struct TextWire {
        width: u32,
        signed: bool,
        #[serde(default)]
        origin: OpaqueOrigin,
    }
    #[derive(Deserialize)]
    #[serde(rename = "OpaqueScalar")]
    struct BinaryWire {
        width: u32,
        signed: bool,
        key: Option<String>,
    }
    if deserializer.is_human_readable() {
        let TextWire { width, signed, origin } = TextWire::deserialize(deserializer)?;
        Ok((width, signed, origin))
    } else {
        let BinaryWire { width, signed, key } = BinaryWire::deserialize(deserializer)?;
        Ok((width, signed, key.map_or(OpaqueOrigin::Unplaced, |key| OpaqueOrigin::Const { key })))
    }
}

const HEX_LOWER: [char; 16] =
    ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c', 'd', 'e', 'f'];

/// Prefix shared by every opaque-scalar symbol, whatever its origin. Consumers
/// that must treat the whole family alike (the σ-path per-occurrence freshening,
/// diagnostics) match on this prefix.
pub const OPAQUE_SCALAR_SYMBOL_PREFIX: &str = "__trust_opaque_scalar_";

/// Prefix shared by every opaque-REFERENCE symbol ([`ConstValue::OpaqueConst`],
/// [`ConstValue::UnitVariantRef`], [`ConstValue::EmptyClosureRef`],
/// [`ConstValue::StructScalarFieldsRef`]),
/// whatever its origin. Before OPAQUE-REF-ID-1 the whole family was the one
/// symbol `__unknown_const`.
pub const OPAQUE_REF_SYMBOL_PREFIX: &str = "__trust_opaque_ref_";

/// Prefix shared by every [`Operand::Unsupported`] symbol. The origin tag follows
/// it directly, so the name is injective in the origin whatever diagnostic text
/// the renderer appends.
pub const UNSUPPORTED_OPERAND_SYMBOL_PREFIX: &str = "__trust_unsupported_operand_";

impl ConstValue {
    /// A not-yet-placed [`ConstValue::OpaqueScalar`] of the given integer type.
    ///
    /// A body that contains it must be placed ([`VerifiableBody::place_opaque_values`])
    /// before any renderer names it; every deserialization does that.
    #[must_use]
    pub fn opaque_scalar(width: u32, signed: bool) -> Self {
        ConstValue::OpaqueScalar { width, signed, origin: OpaqueOrigin::Unplaced }
    }

    /// An unevaluated-constant [`ConstValue::OpaqueScalar`] keyed by `key`
    /// (item + normalized generic arguments + promoted index, as minted by the
    /// extractor). Placement never rewrites a keyed origin.
    #[must_use]
    pub fn opaque_scalar_const(width: u32, signed: bool, key: String) -> Self {
        ConstValue::OpaqueScalar { width, signed, origin: OpaqueOrigin::Const { key } }
    }

    /// A not-yet-placed [`ConstValue::OpaqueConst`] (an unmodeled pointer,
    /// reference or aggregate value). Placement gives it its site.
    #[must_use]
    pub fn opaque_const() -> Self {
        ConstValue::OpaqueConst(OpaqueOrigin::Unplaced)
    }

    /// A not-yet-placed [`ConstValue::UnitVariantRef`].
    #[must_use]
    pub fn unit_variant_ref(enum_name: impl Into<String>, variant: usize) -> Self {
        ConstValue::UnitVariantRef {
            enum_name: enum_name.into(),
            variant,
            origin: OpaqueOrigin::Unplaced,
        }
    }

    /// A not-yet-placed [`ConstValue::EmptyClosureRef`] for the closure whose
    /// def path is `closure` (spelled as `Ty::Closure::name`).
    #[must_use]
    pub fn empty_closure_ref(closure: impl Into<String>) -> Self {
        ConstValue::EmptyClosureRef { closure: closure.into(), origin: OpaqueOrigin::Unplaced }
    }

    /// A not-yet-placed [`ConstValue::StructScalarFieldsRef`].
    #[must_use]
    pub fn struct_scalar_fields_ref(adt_name: impl Into<String>, fields: Vec<ConstValue>) -> Self {
        ConstValue::StructScalarFieldsRef {
            adt_name: adt_name.into(),
            fields,
            origin: OpaqueOrigin::Unplaced,
        }
    }

    /// The identity of a carrier with no modeled value: `Some` for
    /// [`ConstValue::OpaqueScalar`] and the four opaque-reference carriers,
    /// `None` for every constant whose value IS its identity.
    #[must_use]
    pub fn opaque_origin(&self) -> Option<&OpaqueOrigin> {
        match self {
            ConstValue::OpaqueScalar { origin, .. }
            | ConstValue::OpaqueConst(origin)
            | ConstValue::UnitVariantRef { origin, .. }
            | ConstValue::EmptyClosureRef { origin, .. }
            | ConstValue::StructScalarFieldsRef { origin, .. } => Some(origin),
            _ => None,
        }
    }

    fn opaque_origin_mut(&mut self) -> Option<&mut OpaqueOrigin> {
        match self {
            ConstValue::OpaqueScalar { origin, .. }
            | ConstValue::OpaqueConst(origin)
            | ConstValue::UnitVariantRef { origin, .. }
            | ConstValue::EmptyClosureRef { origin, .. }
            | ConstValue::StructScalarFieldsRef { origin, .. } => Some(origin),
            _ => None,
        }
    }

    /// The ONE solver symbol for an opaque scalar occurrence (OPAQUE-SCALAR-ID-1).
    ///
    /// Injective in `(width, signed, origin)`: the type prefix is followed by `_`
    /// and the origin's [`OpaqueOrigin::symbol_tag`], so two distinct origins never
    /// share a name. The output uses only `[_0-9a-z]`, which needs no further
    /// SMT-symbol or TrustFormulaV1 sanitization and replays verbatim into the
    /// native lanes.
    #[must_use]
    pub fn opaque_scalar_smt_var_name(width: u32, signed: bool, origin: &OpaqueOrigin) -> String {
        let sign = if signed { 'i' } else { 'u' };
        let mut name = format!("{OPAQUE_SCALAR_SYMBOL_PREFIX}{sign}{width}_");
        origin.push_symbol_tag(&mut name);
        name
    }

    /// The ONE solver symbol for an opaque-REFERENCE occurrence (OPAQUE-REF-ID-1):
    /// [`OPAQUE_REF_SYMBOL_PREFIX`] followed by the origin's tag. The four
    /// reference carriers share the family on purpose — one site holds one
    /// operand, so distinct carriers at distinct sites still never collide — and
    /// none of them shares a name with an opaque scalar or a place.
    #[must_use]
    pub fn opaque_reference_smt_var_name(origin: &OpaqueOrigin) -> String {
        let mut name = String::from(OPAQUE_REF_SYMBOL_PREFIX);
        origin.push_symbol_tag(&mut name);
        name
    }

    /// The solver symbol of a carrier with no modeled value, spelled from its
    /// identity: `Some` exactly when [`ConstValue::opaque_origin`] is `Some`.
    /// Every renderer that names such a carrier must name it through this, so
    /// no two lanes can disagree about which occurrences are one value.
    #[must_use]
    pub fn unmodeled_value_smt_var_name(&self) -> Option<String> {
        match self {
            ConstValue::OpaqueScalar { width, signed, origin } => {
                Some(Self::opaque_scalar_smt_var_name(*width, *signed, origin))
            }
            ConstValue::OpaqueConst(origin)
            | ConstValue::UnitVariantRef { origin, .. }
            | ConstValue::EmptyClosureRef { origin, .. }
            | ConstValue::StructScalarFieldsRef { origin, .. } => {
                Some(Self::opaque_reference_smt_var_name(origin))
            }
            _ => None,
        }
    }
}

impl Operand {
    /// A not-yet-placed [`Operand::Unsupported`]. Placement gives it its site.
    #[must_use]
    pub fn unsupported(kind: impl Into<String>, detail: impl Into<String>) -> Self {
        Operand::Unsupported {
            kind: kind.into(),
            detail: detail.into(),
            origin: OpaqueOrigin::Unplaced,
        }
    }

    /// The solver symbol of an [`Operand::Unsupported`] occurrence
    /// (OPAQUE-REF-ID-1): [`UNSUPPORTED_OPERAND_SYMBOL_PREFIX`], the origin's tag,
    /// then `_` and `decoration` (a sanitized kind, for readability only). The
    /// tag decides identity; the decoration can never make two origins collide.
    #[must_use]
    pub fn unsupported_operand_smt_var_name(origin: &OpaqueOrigin, decoration: &str) -> String {
        let mut name = String::from(UNSUPPORTED_OPERAND_SYMBOL_PREFIX);
        origin.push_symbol_tag(&mut name);
        if !decoration.is_empty() {
            name.push('_');
            name.push_str(decoration);
        }
        name
    }

    /// The identity this operand carries when its value is not modeled: the
    /// origin of an unmodeled constant ([`ConstValue::opaque_origin`]) or of an
    /// [`Operand::Unsupported`].
    #[must_use]
    pub fn opaque_origin(&self) -> Option<&OpaqueOrigin> {
        match self {
            Operand::Constant(value) => value.opaque_origin(),
            Operand::Unsupported { origin, .. } => Some(origin),
            _ => None,
        }
    }

    fn opaque_origin_mut(&mut self) -> Option<&mut OpaqueOrigin> {
        match self {
            Operand::Constant(value) => value.opaque_origin_mut(),
            Operand::Unsupported { origin, .. } => Some(origin),
            _ => None,
        }
    }
}

/// Visit every operand of a body location in the fixed walk order that defines
/// [`OpaqueOrigin::Site::slot`]. The order is the field order of each
/// variant; the match is exhaustive on purpose, so a new operand-bearing variant
/// cannot be added without deciding its slots.
macro_rules! define_operand_walk {
    ($stmt_fn:ident, $rvalue_fn:ident, $term_fn:ident, $($mutability:tt)?) => {
        fn $rvalue_fn(rvalue: & $($mutability)? Rvalue, visit: &mut impl FnMut(& $($mutability)? Operand)) {
            match rvalue {
                Rvalue::Use(op)
                | Rvalue::UnaryOp(_, op)
                | Rvalue::Cast(op, _)
                | Rvalue::Repeat(op, _) => visit(op),
                Rvalue::BinaryOp(_, lhs, rhs)
                | Rvalue::CheckedBinaryOp(_, lhs, rhs)
                | Rvalue::UncheckedBinaryOp(_, lhs, rhs) => {
                    visit(lhs);
                    visit(rhs);
                }
                Rvalue::Aggregate(_, ops) | Rvalue::Unsupported { operands: ops, .. } => {
                    for op in ops {
                        visit(op);
                    }
                }
                Rvalue::PtrOffset { ptr, count } => {
                    visit(ptr);
                    visit(count);
                }
                Rvalue::Ref { .. }
                | Rvalue::Discriminant(_)
                | Rvalue::Len(_)
                | Rvalue::AddressOf(..)
                | Rvalue::CopyForDeref(_) => {}
            }
        }

        fn $stmt_fn(stmt: & $($mutability)? Statement, visit: &mut impl FnMut(& $($mutability)? Operand)) {
            match stmt {
                Statement::Assign { rvalue, .. } => $rvalue_fn(rvalue, visit),
                Statement::Intrinsic { args, .. } => {
                    for op in args {
                        visit(op);
                    }
                }
                Statement::CopyNonOverlapping { src, dst, count, .. } => {
                    visit(src);
                    visit(dst);
                    visit(count);
                }
                Statement::Unsupported { operands, .. } => {
                    for op in operands {
                        visit(op);
                    }
                }
                Statement::StorageLive(_)
                | Statement::StorageDead(_)
                | Statement::SetDiscriminant { .. }
                | Statement::Deinit { .. }
                | Statement::Retag { .. }
                | Statement::PlaceMention(_)
                | Statement::Coverage
                | Statement::ConstEvalCounter
                | Statement::Nop => {}
            }
        }

        fn $term_fn(term: & $($mutability)? Terminator, visit: &mut impl FnMut(& $($mutability)? Operand)) {
            match term {
                Terminator::SwitchInt { discr, .. } => visit(discr),
                Terminator::Call { args, .. } | Terminator::TailCall { args, .. } => {
                    for op in args {
                        visit(op);
                    }
                }
                Terminator::Assert { cond, .. } => visit(cond),
                Terminator::Goto(_)
                | Terminator::Return
                | Terminator::Drop { .. }
                | Terminator::Opaque { .. }
                | Terminator::Unreachable
                | Terminator::Resume => {}
            }
        }
    };
}

define_operand_walk!(statement_operands_mut, rvalue_operands_mut, terminator_operands_mut, mut);
define_operand_walk!(statement_operands, rvalue_operands, terminator_operands,);

fn site(block: usize, stmt: usize, slot: u32) -> OpaqueOrigin {
    // A body with more than u32::MAX blocks or statements cannot be extracted;
    // saturating keeps the walk total without a panic path.
    OpaqueOrigin::Site {
        block: u32::try_from(block).unwrap_or(u32::MAX),
        stmt: u32::try_from(stmt).unwrap_or(u32::MAX),
        slot,
    }
}

/// Call `visit(location, operand)` for every operand of `block`, with the
/// operand's would-be [`OpaqueOrigin::Site`].
fn for_each_block_operand_mut(
    block_index: usize,
    block: &mut BasicBlock,
    visit: &mut impl FnMut(OpaqueOrigin, &mut Operand),
) {
    let terminator_index = block.stmts.len();
    for (stmt_index, stmt) in block.stmts.iter_mut().enumerate() {
        let mut slot = 0u32;
        statement_operands_mut(stmt, &mut |op| {
            visit(site(block_index, stmt_index, slot), op);
            slot = slot.saturating_add(1);
        });
    }
    let mut slot = 0u32;
    terminator_operands_mut(&mut block.terminator, &mut |op| {
        visit(site(block_index, terminator_index, slot), op);
        slot = slot.saturating_add(1);
    });
}

fn any_block_operand(
    block_index: usize,
    block: &BasicBlock,
    pred: &mut impl FnMut(OpaqueOrigin, &Operand) -> bool,
) -> bool {
    let terminator_index = block.stmts.len();
    let mut found = false;
    for (stmt_index, stmt) in block.stmts.iter().enumerate() {
        let mut slot = 0u32;
        statement_operands(stmt, &mut |op| {
            found |= pred(site(block_index, stmt_index, slot), op);
            slot = slot.saturating_add(1);
        });
        if found {
            return true;
        }
    }
    let mut slot = 0u32;
    terminator_operands(&block.terminator, &mut |op| {
        found |= pred(site(block_index, terminator_index, slot), op);
        slot = slot.saturating_add(1);
    });
    found
}

impl VerifiableBody {
    /// Give every positional unmodeled carrier (see [`Operand::opaque_origin`]) its
    /// [`OpaqueOrigin::Site`] at its CURRENT location. Keyed
    /// ([`OpaqueOrigin::Const`]) origins are left untouched. Idempotent.
    ///
    /// The location is the block's index in [`VerifiableBody::blocks`], which is
    /// the extractor's MIR block index; uniqueness only needs the index to be
    /// distinct per block, which a `Vec` position always is.
    pub fn place_opaque_values(&mut self) {
        for (block_index, block) in self.blocks.iter_mut().enumerate() {
            for_each_block_operand_mut(block_index, block, &mut |at, op| {
                if let Some(origin) = op.opaque_origin_mut()
                    && origin.is_positional()
                {
                    *origin = at;
                }
            });
        }
    }

    /// Whether [`VerifiableBody::place_opaque_values`] would change anything:
    /// some positional origin is unplaced or names a location other than its own.
    #[must_use]
    pub fn opaque_values_need_placement(&self) -> bool {
        self.blocks.iter().enumerate().any(|(block_index, block)| {
            any_block_operand(block_index, block, &mut |at, op| {
                op.opaque_origin().is_some_and(|origin| origin.is_positional() && *origin != at)
            })
        })
    }
}

impl VerifiableFunction {
    /// This function with every unmodeled carrier placed (see
    /// [`VerifiableBody::place_opaque_values`]). No clone is made when the body
    /// is already placed, which every extracted or deserialized body is.
    #[must_use]
    pub fn with_placed_opaque_values(&self) -> Cow<'_, Self> {
        if !self.body.opaque_values_need_placement() {
            return Cow::Borrowed(self);
        }
        let mut placed = self.clone();
        placed.body.place_opaque_values();
        Cow::Owned(placed)
    }
}

/// The wire shape of [`VerifiableBody`]. Deserialization goes through it so that
/// placement runs on EVERY load, whichever crate or format reads the body; the
/// serialized form is untouched (positional origins are never written).
#[derive(Deserialize)]
#[serde(rename = "VerifiableBody")]
pub(crate) struct VerifiableBodyWire {
    locals: Vec<LocalDecl>,
    blocks: Vec<BasicBlock>,
    arg_count: usize,
    return_ty: Ty,
    #[serde(default)]
    datatype_defs: DatatypeDefs,
}

impl From<VerifiableBodyWire> for VerifiableBody {
    fn from(wire: VerifiableBodyWire) -> Self {
        let mut body = VerifiableBody {
            locals: wire.locals,
            blocks: wire.blocks,
            arg_count: wire.arg_count,
            return_ty: wire.return_ty,
            datatype_defs: wire.datatype_defs,
        };
        body.place_opaque_values();
        body
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::model::{BlockId, Place, SourceSpan};

    fn opaque_assign(local: usize) -> Statement {
        Statement::Assign {
            place: Place::local(local),
            rvalue: Rvalue::Use(Operand::Constant(ConstValue::opaque_scalar(64, false))),
            span: SourceSpan::default(),
        }
    }

    fn body() -> VerifiableBody {
        VerifiableBody {
            locals: Vec::new(),
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![opaque_assign(1), opaque_assign(2)],
                    terminator: Terminator::Goto(BlockId(1)),
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::BinaryOp(
                            crate::model::BinOp::Add,
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::opaque_scalar_const(
                                64,
                                false,
                                "core::mem::SizedTypeProperties::SIZE@T".into(),
                            )),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Assert {
                        cond: Operand::Constant(ConstValue::opaque_scalar(8, false)),
                        expected: true,
                        msg: crate::model::AssertMessage::BoundsCheck,
                        target: BlockId(1),
                        span: SourceSpan::default(),
                        unwind: Default::default(),
                    },
                },
            ],
            arg_count: 0,
            return_ty: Ty::Unit,
            datatype_defs: Default::default(),
        }
    }

    fn origins(body: &VerifiableBody) -> Vec<OpaqueOrigin> {
        let mut out = Vec::new();
        for (block_index, block) in body.blocks.iter().enumerate() {
            any_block_operand(block_index, block, &mut |_, op| {
                if let Operand::Constant(ConstValue::OpaqueScalar { origin, .. }) = op {
                    out.push(origin.clone());
                }
                false
            });
        }
        out
    }

    #[test]
    fn placement_gives_each_occurrence_its_own_site_and_keeps_const_keys() {
        let mut b = body();
        assert!(b.opaque_values_need_placement());
        b.place_opaque_values();
        assert!(!b.opaque_values_need_placement(), "placement is idempotent");
        assert_eq!(
            origins(&b),
            vec![
                OpaqueOrigin::Site { block: 0, stmt: 0, slot: 0 },
                OpaqueOrigin::Site { block: 0, stmt: 1, slot: 0 },
                OpaqueOrigin::Const { key: "core::mem::SizedTypeProperties::SIZE@T".into() },
                OpaqueOrigin::Site { block: 1, stmt: 1, slot: 0 },
            ]
        );
    }

    #[test]
    fn a_moved_statement_is_replaced_at_its_new_location() {
        let mut b = body();
        b.place_opaque_values();
        b.blocks[0].stmts.insert(0, Statement::Nop);
        assert!(b.opaque_values_need_placement());
        b.place_opaque_values();
        assert_eq!(origins(&b)[0], OpaqueOrigin::Site { block: 0, stmt: 1, slot: 0 });
    }

    #[test]
    fn names_are_distinct_per_origin_and_symbol_safe() {
        let names = [
            ConstValue::opaque_scalar_smt_var_name(64, false, &OpaqueOrigin::Unplaced),
            ConstValue::opaque_scalar_smt_var_name(
                64,
                false,
                &OpaqueOrigin::Site { block: 1, stmt: 2, slot: 0 },
            ),
            ConstValue::opaque_scalar_smt_var_name(
                64,
                false,
                &OpaqueOrigin::Site { block: 12, stmt: 0, slot: 0 },
            ),
            ConstValue::opaque_scalar_smt_var_name(
                64,
                false,
                &OpaqueOrigin::Const { key: "A::V".into() },
            ),
            ConstValue::opaque_scalar_smt_var_name(
                64,
                false,
                &OpaqueOrigin::Const { key: "B::V".into() },
            ),
            ConstValue::opaque_scalar_smt_var_name(
                64,
                true,
                &OpaqueOrigin::Const { key: "A::V".into() },
            ),
        ];
        for (i, a) in names.iter().enumerate() {
            assert!(a.starts_with(OPAQUE_SCALAR_SYMBOL_PREFIX));
            assert!(a.bytes().all(|c| c == b'_' || c.is_ascii_digit() || c.is_ascii_lowercase()));
            for b in &names[i + 1..] {
                assert_ne!(a, b);
            }
        }
    }

    /// The native lanes replay a vcgen formula's variable names verbatim (the trust-mc
    /// request's typed predicate and the TrustFormulaV1 envelope both carry `{"var":
    /// name}`), so distinct origins stay distinct variables there too.
    #[test]
    fn names_replay_verbatim_into_the_native_formula_envelope() {
        use crate::{Formula, Sort};
        let a = ConstValue::opaque_scalar_smt_var_name(
            64,
            false,
            &OpaqueOrigin::Site { block: 0, stmt: 1, slot: 0 },
        );
        let b = ConstValue::opaque_scalar_smt_var_name(
            64,
            false,
            &OpaqueOrigin::Const { key: "core::mem::SizedTypeProperties::ALIGN@00ff".into() },
        );
        let formula = Formula::Not(Box::new(Formula::Eq(
            Box::new(Formula::Var(a.clone(), Sort::Int)),
            Box::new(Formula::Var(b.clone(), Sort::Int)),
        )));
        let envelope = crate::trust_formula_v1::formula_to_trust_formula_v1_envelope(&formula)
            .expect("opaque-scalar names are valid TrustFormulaV1 variables");
        assert!(envelope.contains(&a) && envelope.contains(&b), "{envelope}");
        // OPAQUE-REF-ID-1: the two recovered pointers of `q1_int_to_ptr` (and an
        // unsupported operand) reach the native lanes as two distinct variables too.
        let p = ConstValue::opaque_reference_smt_var_name(&OpaqueOrigin::Site {
            block: 0,
            stmt: 0,
            slot: 0,
        });
        let q = ConstValue::opaque_reference_smt_var_name(&OpaqueOrigin::Site {
            block: 0,
            stmt: 1,
            slot: 0,
        });
        let u = Operand::unsupported_operand_smt_var_name(
            &OpaqueOrigin::Site { block: 2, stmt: 0, slot: 1 },
            "const_f16",
        );
        let refs = Formula::And(vec![
            Formula::Not(Box::new(Formula::Eq(
                Box::new(Formula::Var(p.clone(), Sort::Int)),
                Box::new(Formula::Var(q.clone(), Sort::Int)),
            ))),
            Formula::Eq(Box::new(Formula::Var(u.clone(), Sort::Int)), Box::new(Formula::Int(0))),
        ]);
        let envelope = crate::trust_formula_v1::formula_to_trust_formula_v1_envelope(&refs)
            .expect("opaque-reference and unsupported names are valid TrustFormulaV1 variables");
        assert!(p != q && envelope.contains(&p) && envelope.contains(&q), "{envelope}");
        assert!(envelope.contains(&u), "{envelope}");
    }

    #[test]
    fn deserialization_places_and_serialization_omits_positional_origins() {
        let mut placed = body();
        placed.place_opaque_values();
        let mut unplaced = body();
        // A legacy dump has no `origin` at all.
        let legacy = serde_json::to_string(&unplaced).expect("serialize");
        assert!(!legacy.contains("Unplaced") && !legacy.contains("\"Site\""));
        assert_eq!(legacy.matches("\"origin\"").count(), 1, "only the keyed origin is written");
        let loaded: VerifiableBody = serde_json::from_str(&legacy).expect("deserialize");
        assert_eq!(origins(&loaded), origins(&placed));
        assert_eq!(serde_json::to_string(&loaded).expect("serialize"), legacy);
        unplaced.place_opaque_values();
        assert_eq!(serde_json::to_string(&unplaced).expect("serialize"), legacy);
    }

    /// Every unmodeled carrier, one per statement / terminator slot: the three
    /// opaque-reference carriers and an unsupported operand.
    fn reference_body() -> VerifiableBody {
        let assign = |local: usize, op: Operand| Statement::Assign {
            place: Place::local(local),
            rvalue: Rvalue::Use(op),
            span: SourceSpan::default(),
        };
        VerifiableBody {
            locals: Vec::new(),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    assign(1, Operand::Constant(ConstValue::opaque_const())),
                    assign(2, Operand::Constant(ConstValue::opaque_const())),
                    assign(3, Operand::Constant(ConstValue::unit_variant_ref("Option", 0))),
                    assign(
                        4,
                        Operand::Constant(ConstValue::struct_scalar_fields_ref(
                            "S",
                            vec![ConstValue::Uint(7, 8)],
                        )),
                    ),
                    assign(5, Operand::unsupported("Const::F16", "float constant width 16")),
                ],
                terminator: Terminator::Call {
                    func: "f".into(),
                    args: vec![
                        Operand::unsupported("Const::F16", "float constant width 16"),
                        Operand::Constant(ConstValue::opaque_const()),
                    ],
                    dest: Place::local(6),
                    target: None,
                    span: SourceSpan::default(),
                    atomic: None,
                    is_foreign: false,
                    is_unsafe_sig: false,
                    callee_identity: None,
                    callee_key: None,
                    unwind: Default::default(),
                },
            }],
            arg_count: 0,
            return_ty: Ty::Unit,
            datatype_defs: Default::default(),
        }
    }

    fn all_origins(body: &VerifiableBody) -> Vec<OpaqueOrigin> {
        let mut out = Vec::new();
        for (block_index, block) in body.blocks.iter().enumerate() {
            any_block_operand(block_index, block, &mut |_, op| {
                if let Some(origin) = op.opaque_origin() {
                    out.push(origin.clone());
                }
                false
            });
        }
        out
    }

    /// OPAQUE-REF-ID-1: the reference carriers and unsupported operands are placed
    /// exactly like opaque scalars, one site each.
    #[test]
    fn reference_and_unsupported_carriers_are_placed_per_site() {
        let mut b = reference_body();
        assert!(b.opaque_values_need_placement());
        b.place_opaque_values();
        assert!(!b.opaque_values_need_placement(), "placement is idempotent");
        let site = |block, stmt, slot| OpaqueOrigin::Site { block, stmt, slot };
        assert_eq!(
            all_origins(&b),
            vec![
                site(0, 0, 0),
                site(0, 1, 0),
                site(0, 2, 0),
                site(0, 3, 0),
                site(0, 4, 0),
                site(0, 5, 0),
                site(0, 5, 1),
            ]
        );
    }

    /// The renderers' names: one per site within each family, never shared across
    /// families, and the unsupported operand's diagnostic decoration cannot make two
    /// origins collide (the tag is fixed-arity and comes first).
    #[test]
    fn reference_and_unsupported_names_are_injective_in_the_origin() {
        let mut b = reference_body();
        b.place_opaque_values();
        let mut names = Vec::new();
        for (block_index, block) in b.blocks.iter().enumerate() {
            any_block_operand(block_index, block, &mut |_, op| {
                match op {
                    Operand::Constant(value) => names
                        .push(value.unmodeled_value_smt_var_name().expect("an unmodeled carrier")),
                    Operand::Unsupported { origin, .. } => {
                        names.push(Operand::unsupported_operand_smt_var_name(origin, "const_f16"))
                    }
                    _ => {}
                }
                false
            });
        }
        assert_eq!(names.len(), 7);
        for (i, a) in names.iter().enumerate() {
            assert!(a.bytes().all(|c| c == b'_' || c.is_ascii_digit() || c.is_ascii_lowercase()));
            for other in &names[i + 1..] {
                assert_ne!(a, other);
            }
        }
        assert!(names[..4].iter().all(|n| n.starts_with(OPAQUE_REF_SYMBOL_PREFIX)));
        assert!(names[4].starts_with(UNSUPPORTED_OPERAND_SYMBOL_PREFIX));
        // A decoration that spells another site's tag still names its own site.
        let a = Operand::unsupported_operand_smt_var_name(
            &OpaqueOrigin::Site { block: 1, stmt: 2, slot: 3 },
            "b4_s5_o6",
        );
        let b = Operand::unsupported_operand_smt_var_name(
            &OpaqueOrigin::Site { block: 4, stmt: 5, slot: 6 },
            "",
        );
        assert_ne!(a, b);
        assert!(a.starts_with("__trust_unsupported_operand_b1_s2_o3_"));
        // Constants whose value is their identity have no unmodeled symbol.
        for modeled in [
            ConstValue::Int(1),
            ConstValue::Bool(true),
            ConstValue::Unit,
            ConstValue::Str { bytes: b"ab".to_vec() },
        ] {
            assert!(modeled.unmodeled_value_smt_var_name().is_none(), "{modeled:?}");
            assert!(modeled.opaque_origin().is_none(), "{modeled:?}");
        }
    }

    /// The wire format of the reference carriers and unsupported operands is
    /// unchanged: `"OpaqueConst"` stays a bare unit string, no `origin` is written,
    /// and a legacy dump loads placed and re-serializes byte-identically.
    #[test]
    fn reference_carrier_origins_never_reach_the_wire() {
        let unplaced = reference_body();
        let legacy = serde_json::to_string(&unplaced).expect("serialize");
        assert!(legacy.contains("\"OpaqueConst\""), "{legacy}");
        assert!(!legacy.contains("origin") && !legacy.contains("Site"), "{legacy}");
        let loaded: VerifiableBody = serde_json::from_str(&legacy).expect("deserialize");
        let mut placed = reference_body();
        placed.place_opaque_values();
        assert_eq!(all_origins(&loaded), all_origins(&placed));
        assert_eq!(serde_json::to_string(&loaded).expect("serialize"), legacy);
        assert_eq!(serde_json::to_string(&placed).expect("serialize"), legacy);
        let bare: ConstValue = serde_json::from_str("\"OpaqueConst\"").expect("legacy unit form");
        assert!(matches!(bare, ConstValue::OpaqueConst(OpaqueOrigin::Unplaced)));
    }
}
