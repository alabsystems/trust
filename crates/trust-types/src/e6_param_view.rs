// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The E6 **parameter view**: a borrow-erased copy of an extracted body in
//! which a frozen shared parameter's scalar fields are by-value scalar
//! parameters.
//!
//! WHY THIS EXISTS. A function with a `&self` / `&T` parameter can never be
//! E6-admitted today — `facet_inference::local_ty_in_closed_fragment` refuses
//! any `Ty::Ref`-typed local, so the body has no facets, so no `ensures` clause
//! on it can cite Lean. The five refusal layers are not the problem to fix:
//! the reason `tests/e6-fragment-probe/README.md`'s finding 6 gives for them is
//! that "the MIR read carries a `Deref`, and the pointee is not provably
//! unchanged between entry and exit", which is a real gap, not an oversight.
//!
//! WHAT THIS IS INSTEAD. This module never edits a refusal. It builds a
//! SEPARATE `VerifiableFunction` — the view — whose parameters are the scalar
//! field VALUES the body reads through the borrow, and hands THAT to the
//! unchanged facet validator, the unchanged `recognize_admissible_body`, and
//! the unchanged mints. The Lean-side defining equation is therefore a function
//! of pointee values, and the clause binds them as `self.x`. Nothing this
//! module produces ever enters `SessionFnFacets::accumulated`, so no existing
//! consumer sees a changed `arg_count` or local numbering.
//!
//! WHAT THAT COSTS, STATED ONCE. The view is sound only under an aliasing
//! assumption the compiler does not prove:
//!
//! > a live `&T` function argument with `T: Freeze` is dereferenceable, points
//! > to a valid `T`, and its pointee bytes are immutable for the duration of
//! > the call.
//!
//! That is **R1 (2026-09-17)**, recorded in
//! `docs/design-notes/2026-09-18-e6-parameter-view-ruling.md` and carried as a
//! named row in `docs/TCB.md`. The same ruling forbids reporting a row
//! discharged through a view as `Certified`: a view row is graded BELOW
//! `Certified` and carries the machine-readable marker [`VIEW_MARKER`] on the
//! spec-clean goal row, on the zero-authority denotation row, and in the
//! per-function discharge note. On the JSON wire it is disclosed by the
//! distinct solver label (`clean-kernel-view-citation` /
//! `clean-kernel-view-defeq`) and by the ABSENCE of any kernel proof evidence,
//! which is what makes the authenticated lane withhold the row on every path.
//! Nothing in this module decides that grade — it only supplies the marker's
//! name and the evidence the grader keys on.
//!
//! THE ADMITTED FRAGMENT. Everything this module accepts is listed in
//! `e6_param_view`'s own contract below. The rustc-side half — shared
//! reference, `Freeze` pointee (by rustc's `is_freeze` AND an independent
//! structural `UnsafeCell` walk), struct pointee, a plain named parameter
//! pattern — is computed by the compiler into a [`FrozenSharedParams`] table
//! and is NOT re-derivable here; this module VERIFIES the table against the
//! extracted IR and refuses the whole view on any disagreement, so a table that
//! claims a field the IR does not have, or a carrier the IR contradicts, mints
//! nothing.

use std::collections::{BTreeMap, BTreeSet};

use crate::{
    AdtKind, BasicBlock, LocalDecl, Operand, Place, Projection, Rvalue, Statement, Terminator, Ty,
    VerifiableFunction,
};

/// The machine-readable marker a view-discharged row carries, everywhere it is
/// reported. One constant so the spec-clean goal row, the denotation row, the
/// discharge note and `docs/TCB.md` cannot drift apart.
pub const VIEW_MARKER: &str = "frozen-shared-erased";

/// One scalar field of a frozen shared pointee that the view turns into a
/// by-value parameter.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FrozenRow {
    /// Index into the pointee ADT's DECLARED field list.
    pub field_index: usize,
    /// The declared field name (`x`), never the dotted clause spelling.
    pub field_name: String,
    /// The canonical Rust spelling of the field's carrier (`u32`), exactly as
    /// the clause-side row table records it.
    pub carrier: String,
}

/// The frozen shared pointee of ONE parameter: the compiler's decision about
/// which fields the view may read, and under which names.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FrozenPointee {
    /// The parameter's source binding name (`self`), which is also the row
    /// prefix and the extracted local's debug name.
    pub param_name: String,
    /// The pointee ADT's name, re-checked against the extracted IR type.
    pub adt_name: String,
    /// The rows, in DECLARED field order. Empty is a refusal, not a view.
    pub rows: Vec<FrozenRow>,
}

/// The rustc-free mirror of `trust_frozen_shared_param_table`, keyed by 0-BASED
/// source parameter index (extracted local `index + 1`).
pub type FrozenSharedParams = BTreeMap<usize, FrozenPointee>;

/// A borrow-erased, scalarized copy of an extracted body.
#[derive(Debug, Clone)]
pub struct E6ParamView {
    /// The view function. Same `def_path`, `name`, `span`, contracts and spec
    /// as the original — only `body` differs.
    pub func: VerifiableFunction,
    /// The CLAUSE-SIDE name of every view parameter, in order. Length is
    /// exactly `func.body.arg_count`, entries are pairwise distinct, and entry
    /// `i` equals the debug name of view local `i + 1`.
    pub param_names: Vec<String>,
    /// The source parameters this view erased (`self`), for disclosure in the
    /// discharge note. Empty is impossible: a view exists only when at least
    /// one borrow was erased.
    pub erased_params: Vec<String>,
}

/// Why a body has no E6 parameter view. Every variant maps to one `D-REF-*`
/// note in the ref-self design's §6; the compiler renders the note and the
/// v7/D3 options from it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ViewRefusal {
    /// D-REF-9: a parameter local with no recorded name. A view parameter's
    /// name IS its clause binder, so an unnamed one has no spelling to record
    /// and no row to compare against.
    UnnamedParam { local: usize },
    /// D-REF-1 / D-REF-3 / D-REF-6: a parameter the view vocabulary does not
    /// admit and for which the compiler recorded no frozen row.
    UnsupportedParam { local: usize, ty: String },
    /// C4: the extracted IR type of a frozen parameter disagrees with the
    /// compiler's table.
    PointeeMismatch { local: usize, detail: String },
    /// C4: one listed field disagrees with the extracted IR.
    FieldMismatch { local: usize, field: String, detail: String },
    /// A frozen entry with no rows would erase the parameter entirely.
    EmptyRows { local: usize },
    /// The body uses a construct outside the view's allow-list.
    UnsupportedConstruct { detail: String },
    /// V2: the borrow is used other than by a scalar field read.
    BorrowNotScalarRead { local: usize, detail: String },
    /// D-REF-4b: the borrow is captured whole into an aggregate, which is the
    /// shape a closure-form contract takes.
    BorrowCapturedByAggregate { local: usize },
    /// V3: the return type is not a by-value scalar of the view vocabulary.
    ReturnNotScalar { ty: String },
    /// Two view parameters would carry the same clause-side name.
    DuplicateViewParamName { name: String },
    /// The extracted body violates the dense-local invariant the validator
    /// requires, so nothing can be renumbered against it.
    MalformedBody { detail: String },
}

impl std::fmt::Display for ViewRefusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnnamedParam { local } => write!(
                f,
                "parameter local `_{local}` has no name, so it has no clause-side spelling"
            ),
            Self::UnsupportedParam { local, ty } => write!(
                f,
                "parameter local `_{local}` has type `{ty}`, which this lane admits neither by \
                 value nor as a frozen shared borrow"
            ),
            Self::PointeeMismatch { local, detail } => write!(
                f,
                "the extracted type of parameter local `_{local}` disagrees with the signature \
                 table: {detail}"
            ),
            Self::FieldMismatch { local, field, detail } => write!(
                f,
                "field `{field}` of parameter local `_{local}` disagrees with the signature \
                 table: {detail}"
            ),
            Self::EmptyRows { local } => {
                write!(f, "parameter local `_{local}` has no readable scalar field")
            }
            Self::UnsupportedConstruct { detail } => {
                write!(f, "the body is outside the view's allow-list: {detail}")
            }
            Self::BorrowNotScalarRead { local, detail } => write!(
                f,
                "the borrow `_{local}` is used other than by a scalar field read: {detail}"
            ),
            Self::BorrowCapturedByAggregate { local } => write!(
                f,
                "the borrow `_{local}` is captured whole into an aggregate (the shape a \
                 closure-form contract takes)"
            ),
            Self::ReturnNotScalar { ty } => {
                write!(f, "the return type `{ty}` is not a by-value scalar of this lane")
            }
            Self::DuplicateViewParamName { name } => {
                write!(f, "two view parameters would both be named `{name}`")
            }
            Self::MalformedBody { detail } => {
                write!(f, "the extracted body is malformed: {detail}")
            }
        }
    }
}

/// THE view vocabulary, as ONE function.
///
/// `usize`/`isize` are deliberately absent. The clause side types them
/// (`trust_fn_discharge_binder_types` resolves them to the target's fixed
/// width) but `trust_certify::clean_island::ty_to_domain` has no signed
/// pointer-sized arm, so admitting them here would put the two flattenings at
/// different arities for a signed pointer-sized field — the exact disagreement
/// the all-or-nothing comment in `clean_island.rs` records. The live `usize`
/// lane extends THIS function when it lands, and nothing else.
#[must_use]
pub fn e6_view_scalar(ty: &Ty) -> Option<&'static str> {
    match ty {
        Ty::Bool => Some("bool"),
        Ty::Int { width, signed } => match (*width, *signed) {
            (8, false) => Some("u8"),
            (16, false) => Some("u16"),
            (32, false) => Some("u32"),
            (64, false) => Some("u64"),
            (128, false) => Some("u128"),
            (8, true) => Some("i8"),
            (16, true) => Some("i16"),
            (32, true) => Some("i32"),
            (64, true) => Some("i64"),
            (128, true) => Some("i128"),
            _ => None,
        },
        _ => None,
    }
}

/// Build the E6 parameter view of `func` against the compiler's frozen-shared
/// parameter table.
///
/// * `Ok(None)` — no parameter local is a `Ty::Ref` and the table is empty:
///   the caller uses `func` exactly as it does today, byte for byte.
/// * `Ok(Some(view))` — every condition below holds and `view.func` is the
///   borrow-erased copy.
/// * `Err(refusal)` — the caller reports the matching `D-REF-*` note and mints
///   nothing.
///
/// The conditions, in the order they are checked:
///
/// 1. **Dense locals.** `locals[j].index == j`, `0 < arg_count < locals.len()`,
///    and `locals[0].ty == return_ty` — the same invariants
///    `facet_inference::is_valid_closed_leaf` requires, checked here because
///    the renumbering below is meaningless without them.
/// 2. **V3, the return.** `return_ty` is in the view vocabulary. A reference,
///    struct or `Option` return is refused: those go through the per-field mint
///    lane, which records and compares names separately and is not audited by
///    this design.
/// 3. **V1, the parameters.** Each parameter local is EITHER a by-value scalar
///    of the view vocabulary with a recorded name, OR has a frozen row in the
///    table. Anything else refuses. A frozen local is additionally verified
///    against the IR (C4): shared `Ty::Ref` whose pointee is a struct
///    (`variants` empty AND `adt_kind == Some(Struct)`) of the recorded name,
///    whose field `k` has the recorded name and a carrier equal to the recorded
///    one, and whose extracted debug name is the recorded parameter name.
///    Fields NOT listed are never inspected — they may be lowered opaquely.
/// 4. **V2 and the allow-list.** The whole body is rewritten. The rewrite is
///    TOTAL over what it accepts, so validation and rewriting cannot drift:
///    every statement, rvalue, operand, place and terminator is matched
///    exhaustively with NO wildcard arm (this module is inside `trust-types`,
///    so a new IR variant is a compile error here), and every occurrence of a
///    frozen local must be `Operand::Copy` of a place whose projections are
///    exactly `[Deref, Field(k)]` with `k` a listed row. A bare `_i`, a
///    `Move`, a whole-pointee read (`clone`), a deeper projection, an
///    unlisted field, any write rooted at `_i`, and any re-borrow, address-of
///    or `CopyForDeref` anywhere all refuse.
/// 5. **Distinct names.** The view parameter names are pairwise distinct.
///
/// What this function deliberately does NOT do: decide `Freeze`, decide
/// mutability, or read a Rust signature. Those are the compiler's, and the
/// table is their only channel.
pub fn e6_param_view(
    func: &VerifiableFunction,
    frozen: &FrozenSharedParams,
) -> Result<Option<E6ParamView>, ViewRefusal> {
    let body = &func.body;
    let arg_count = body.arg_count;

    let has_ref_param = (1..=arg_count)
        .any(|i| body.locals.get(i).is_some_and(|local| matches!(local.ty, Ty::Ref { .. })));
    if !has_ref_param && frozen.is_empty() {
        return Ok(None);
    }

    // (1) dense locals.
    if body.locals.is_empty() || arg_count == 0 || arg_count >= body.locals.len() {
        return Err(ViewRefusal::MalformedBody {
            detail: format!("arg_count {arg_count} against {} locals", body.locals.len()),
        });
    }
    for (index, local) in body.locals.iter().enumerate() {
        if local.index != index {
            return Err(ViewRefusal::MalformedBody {
                detail: format!("local at position {index} declares index {}", local.index),
            });
        }
    }
    if body.locals[0].ty != body.return_ty {
        return Err(ViewRefusal::MalformedBody {
            detail: "the return slot's type is not the declared return type".to_string(),
        });
    }
    // A table entry that names a parameter this body does not have is a
    // disagreement between the signature and the extraction, not a view.
    if let Some(index) = frozen.keys().find(|index| **index + 1 > arg_count) {
        return Err(ViewRefusal::PointeeMismatch {
            local: index + 1,
            detail: format!("the table names parameter {index}, but the body has {arg_count}"),
        });
    }

    // (2) V3.
    if e6_view_scalar(&body.return_ty).is_none() {
        return Err(ViewRefusal::ReturnNotScalar { ty: format!("{:?}", body.return_ty) });
    }

    // (3) V1 + C4, and the new local layout in one pass.
    let mut new_locals: Vec<LocalDecl> = vec![LocalDecl {
        index: 0,
        ty: body.locals[0].ty.clone(),
        name: body.locals[0].name.clone(),
    }];
    let mut param_names: Vec<String> = Vec::new();
    let mut erased_params: Vec<String> = Vec::new();
    // old local -> new local, for every local that survives as ONE local. The
    // return slot keeps position 0: `is_valid_closed_leaf` requires local 0's
    // type to equal the return type, and the recognizers key on `place.local
    // == 0`.
    let mut plain: Vec<Option<usize>> = vec![None; body.locals.len()];
    plain[0] = Some(0);
    // old frozen local -> (declared field index -> new local).
    let mut scalarized: BTreeMap<usize, BTreeMap<usize, usize>> = BTreeMap::new();

    for i in 1..=arg_count {
        let local = &body.locals[i];
        match frozen.get(&(i - 1)) {
            Some(pointee) => {
                let fields = verify_frozen_local(i, local, pointee)?;
                if pointee.rows.is_empty() {
                    return Err(ViewRefusal::EmptyRows { local: i });
                }
                let mut slots = BTreeMap::new();
                for row in &pointee.rows {
                    let index = new_locals.len();
                    let name = format!("{}.{}", pointee.param_name, row.field_name);
                    new_locals.push(LocalDecl {
                        index,
                        ty: fields[row.field_index].1.clone(),
                        name: Some(name.clone()),
                    });
                    param_names.push(name);
                    slots.insert(row.field_index, index);
                }
                scalarized.insert(i, slots);
                erased_params.push(pointee.param_name.clone());
            }
            None => {
                if e6_view_scalar(&local.ty).is_none() {
                    return Err(ViewRefusal::UnsupportedParam {
                        local: i,
                        ty: format!("{:?}", local.ty),
                    });
                }
                let Some(name) = local.name.clone() else {
                    return Err(ViewRefusal::UnnamedParam { local: i });
                };
                let index = new_locals.len();
                new_locals.push(LocalDecl {
                    index,
                    ty: local.ty.clone(),
                    name: Some(name.clone()),
                });
                param_names.push(name);
                plain[i] = Some(index);
            }
        }
    }
    let new_arg_count = new_locals.len() - 1;
    for i in (arg_count + 1)..body.locals.len() {
        let local = &body.locals[i];
        if matches!(local.ty, Ty::Ref { .. } | Ty::RawPtr { .. }) {
            // A non-parameter reference local means the body took or forwarded
            // an address; the pointee-immutability argument covers function
            // ARGUMENTS only.
            return Err(ViewRefusal::UnsupportedConstruct {
                detail: format!("local `_{i}` is a reference or raw pointer"),
            });
        }
        let index = new_locals.len();
        new_locals.push(LocalDecl { index, ty: local.ty.clone(), name: local.name.clone() });
        plain[i] = Some(index);
    }

    // (5) distinct names, before anything is rewritten.
    let mut seen: BTreeSet<&str> = BTreeSet::new();
    for name in &param_names {
        if !seen.insert(name.as_str()) {
            return Err(ViewRefusal::DuplicateViewParamName { name: name.clone() });
        }
    }

    // (4) V2 + allow-list, as one total rewrite.
    let rewriter = Rewriter { plain: &plain, scalarized: &scalarized };
    let mut new_blocks: Vec<BasicBlock> = Vec::with_capacity(body.blocks.len());
    for (index, block) in body.blocks.iter().enumerate() {
        if block.id.0 != index {
            return Err(ViewRefusal::MalformedBody {
                detail: format!("block at position {index} declares id {}", block.id.0),
            });
        }
        let mut stmts = Vec::with_capacity(block.stmts.len());
        for stmt in &block.stmts {
            stmts.push(rewriter.statement(stmt)?);
        }
        new_blocks.push(BasicBlock {
            id: block.id,
            stmts,
            terminator: rewriter.terminator(&block.terminator)?,
        });
    }

    let view = VerifiableFunction {
        name: func.name.clone(),
        def_path: func.def_path.clone(),
        span: func.span.clone(),
        body: crate::VerifiableBody {
            locals: new_locals,
            blocks: new_blocks,
            arg_count: new_arg_count,
            return_ty: body.return_ty.clone(),
            datatype_defs: body.datatype_defs.clone(),
        },
        contracts: func.contracts.clone(),
        preconditions: func.preconditions.clone(),
        postconditions: func.postconditions.clone(),
        spec: func.spec.clone(),
        tuple_layouts: func.tuple_layouts.clone(),
    };
    Ok(Some(E6ParamView { func: view, param_names, erased_params }))
}

/// C4: the extracted IR type of a frozen parameter against the compiler's
/// table. Returns the pointee's declared field list so the caller can take each
/// listed field's IR type without re-matching.
fn verify_frozen_local<'a>(
    local_index: usize,
    local: &'a LocalDecl,
    pointee: &FrozenPointee,
) -> Result<&'a Vec<(String, Ty)>, ViewRefusal> {
    if local.name.as_deref() != Some(pointee.param_name.as_str()) {
        return Err(ViewRefusal::PointeeMismatch {
            local: local_index,
            detail: format!(
                "extracted name {:?} is not the recorded parameter name `{}`",
                local.name, pointee.param_name
            ),
        });
    }
    let Ty::Ref { mutable: false, inner } = &local.ty else {
        return Err(ViewRefusal::PointeeMismatch {
            local: local_index,
            detail: "not an extracted shared reference".to_string(),
        });
    };
    let Ty::Adt { name, fields, variants, adt_kind, .. } = inner.as_ref() else {
        return Err(ViewRefusal::PointeeMismatch {
            local: local_index,
            detail: "the pointee is not an extracted ADT".to_string(),
        });
    };
    if !variants.is_empty() || *adt_kind != Some(AdtKind::Struct) {
        return Err(ViewRefusal::PointeeMismatch {
            local: local_index,
            detail: format!("the pointee is not a struct (adt_kind {adt_kind:?})"),
        });
    }
    if name != &pointee.adt_name {
        return Err(ViewRefusal::PointeeMismatch {
            local: local_index,
            detail: format!(
                "extracted pointee `{name}` is not the recorded `{}`",
                pointee.adt_name
            ),
        });
    }
    for row in &pointee.rows {
        let Some((field_name, field_ty)) = fields.get(row.field_index) else {
            return Err(ViewRefusal::FieldMismatch {
                local: local_index,
                field: row.field_name.clone(),
                detail: format!(
                    "the extracted pointee has {} fields, so index {} does not exist",
                    fields.len(),
                    row.field_index
                ),
            });
        };
        if field_name != &row.field_name {
            return Err(ViewRefusal::FieldMismatch {
                local: local_index,
                field: row.field_name.clone(),
                detail: format!("extracted field {} is named `{field_name}`", row.field_index),
            });
        }
        match e6_view_scalar(field_ty) {
            Some(carrier) if carrier == row.carrier => {}
            Some(carrier) => {
                return Err(ViewRefusal::FieldMismatch {
                    local: local_index,
                    field: row.field_name.clone(),
                    detail: format!(
                        "extracted carrier `{carrier}` is not the recorded `{}`",
                        row.carrier
                    ),
                });
            }
            None => {
                return Err(ViewRefusal::FieldMismatch {
                    local: local_index,
                    field: row.field_name.clone(),
                    detail: format!("extracted type {field_ty:?} is outside the view vocabulary"),
                });
            }
        }
    }
    Ok(fields)
}

/// The total rewrite. Every method is exhaustive over its IR enum with NO
/// wildcard arm, and every struct-variant is destructured FIELD BY FIELD — a
/// new variant OR a new field carrying a place or an operand is a compile
/// error in this file rather than a silently un-rewritten hole.
struct Rewriter<'a> {
    plain: &'a [Option<usize>],
    scalarized: &'a BTreeMap<usize, BTreeMap<usize, usize>>,
}

impl Rewriter<'_> {
    /// A READ place. A frozen local is admitted only as `[Deref, Field(k)]`
    /// with `k` a listed row, and becomes the bare scalar view local.
    fn read_place(&self, place: &Place) -> Result<Place, ViewRefusal> {
        if let Some(slots) = self.scalarized.get(&place.local) {
            // EXACTLY `[Deref, Field(k)]`, matched over the WHOLE slice: an
            // empty projection list (a bare `_i`, the closure-capture and
            // forward-to-sibling shapes) must refuse, not index out of range.
            let [Projection::Deref, Projection::Field(field)] = &place.projections[..] else {
                return Err(ViewRefusal::BorrowNotScalarRead {
                    local: place.local,
                    detail: format!("projections {:?}", place.projections),
                });
            };
            let Some(new_local) = slots.get(field) else {
                return Err(ViewRefusal::BorrowNotScalarRead {
                    local: place.local,
                    detail: format!("field {field} is not a readable row of this pointee"),
                });
            };
            return Ok(Place { local: *new_local, projections: Vec::new() });
        }
        let Some(&Some(new_local)) = self.plain.get(place.local) else {
            return Err(ViewRefusal::MalformedBody {
                detail: format!("place names local `_{}`, which does not exist", place.local),
            });
        };
        for projection in &place.projections {
            self.projection(projection)?;
        }
        Ok(Place { local: new_local, projections: place.projections.clone() })
    }

    /// A WRITE place (an assignment destination or a call destination). A
    /// frozen local can never be one: the view models a function of ENTRY
    /// values, and a write through the borrow would make that reading false.
    fn write_place(&self, place: &Place) -> Result<Place, ViewRefusal> {
        if self.scalarized.contains_key(&place.local) {
            return Err(ViewRefusal::BorrowNotScalarRead {
                local: place.local,
                detail: "it is the destination of a write".to_string(),
            });
        }
        self.read_place(place)
    }

    /// `Deref` is admitted ONLY as the first projection of a frozen local,
    /// which `read_place` handles before this is ever reached. Everything else
    /// must be a `Field`.
    fn projection(&self, projection: &Projection) -> Result<(), ViewRefusal> {
        match projection {
            Projection::Field(_) => Ok(()),
            Projection::Deref => Err(ViewRefusal::UnsupportedConstruct {
                detail: "a `Deref` projection outside a frozen shared parameter".to_string(),
            }),
            Projection::Index(_)
            | Projection::Downcast(_)
            | Projection::OpaqueCast(_)
            | Projection::UnwrapUnsafeBinder(_)
            | Projection::ConstantIndex { .. }
            | Projection::Subslice { .. } => Err(ViewRefusal::UnsupportedConstruct {
                detail: format!("projection {projection:?}"),
            }),
        }
    }

    fn operand(&self, operand: &Operand) -> Result<Operand, ViewRefusal> {
        match operand {
            Operand::Copy(place) => Ok(Operand::Copy(self.read_place(place)?)),
            Operand::Move(place) => {
                if self.scalarized.contains_key(&place.local) {
                    return Err(ViewRefusal::BorrowNotScalarRead {
                        local: place.local,
                        detail: "it is MOVED rather than read by copy".to_string(),
                    });
                }
                Ok(Operand::Move(self.read_place(place)?))
            }
            Operand::Constant(value) => Ok(Operand::Constant(value.clone())),
            Operand::Symbolic(_) => {
                Err(ViewRefusal::UnsupportedConstruct { detail: "a symbolic operand".to_string() })
            }
            Operand::Unsupported { kind, detail, .. } => Err(ViewRefusal::UnsupportedConstruct {
                detail: format!("unsupported operand {kind}: {detail}"),
            }),
        }
    }

    fn rvalue(&self, rvalue: &Rvalue) -> Result<Rvalue, ViewRefusal> {
        match rvalue {
            Rvalue::Use(operand) => Ok(Rvalue::Use(self.operand(operand)?)),
            Rvalue::BinaryOp(op, left, right) => {
                Ok(Rvalue::BinaryOp(*op, self.operand(left)?, self.operand(right)?))
            }
            Rvalue::CheckedBinaryOp(op, left, right) => {
                Ok(Rvalue::CheckedBinaryOp(*op, self.operand(left)?, self.operand(right)?))
            }
            Rvalue::UnaryOp(op, operand) => Ok(Rvalue::UnaryOp(*op, self.operand(operand)?)),
            Rvalue::Cast(operand, ty) => Ok(Rvalue::Cast(self.operand(operand)?, ty.clone())),
            Rvalue::Aggregate(kind, operands) => {
                // D-REF-4b: name the closure-capture shape explicitly. A
                // contract written in closure form injects an aggregate that
                // captures the borrow WHOLE, and "used other than by a scalar
                // read" is not a help an author can act on.
                for operand in operands {
                    if let Operand::Copy(place) | Operand::Move(place) = operand
                        && place.projections.is_empty()
                        && self.scalarized.contains_key(&place.local)
                    {
                        return Err(ViewRefusal::BorrowCapturedByAggregate { local: place.local });
                    }
                }
                let mut rewritten = Vec::with_capacity(operands.len());
                for operand in operands {
                    rewritten.push(self.operand(operand)?);
                }
                Ok(Rvalue::Aggregate(kind.clone(), rewritten))
            }
            // Everything below is refused. `Ref`/`AddressOf`/`CopyForDeref` are
            // the address-taking forms the soundness argument's step (a) rules
            // out; the rest have no reading in this fragment.
            Rvalue::Ref { .. } | Rvalue::AddressOf(..) | Rvalue::CopyForDeref(_) => {
                Err(ViewRefusal::UnsupportedConstruct {
                    detail: "the body takes or copies an address".to_string(),
                })
            }
            Rvalue::UncheckedBinaryOp(..)
            | Rvalue::Discriminant(_)
            | Rvalue::Len(_)
            | Rvalue::Repeat(..)
            | Rvalue::PtrOffset { .. }
            | Rvalue::Unsupported { .. } => {
                Err(ViewRefusal::UnsupportedConstruct { detail: format!("rvalue {rvalue:?}") })
            }
        }
    }

    fn statement(&self, statement: &Statement) -> Result<Statement, ViewRefusal> {
        match statement {
            Statement::Assign { place, rvalue, span } => Ok(Statement::Assign {
                place: self.write_place(place)?,
                rvalue: self.rvalue(rvalue)?,
                span: span.clone(),
            }),
            // A storage marker on a borrowed parameter would have to become N
            // markers and says nothing the view needs; refuse it. MIR does not
            // emit one for an argument, so this is fail-closed on a shape the
            // lane has never seen rather than a live restriction.
            Statement::StorageLive(local) => {
                Ok(Statement::StorageLive(self.storage_local(*local)?))
            }
            Statement::StorageDead(local) => {
                Ok(Statement::StorageDead(self.storage_local(*local)?))
            }
            Statement::Coverage => Ok(Statement::Coverage),
            Statement::ConstEvalCounter => Ok(Statement::ConstEvalCounter),
            Statement::Nop => Ok(Statement::Nop),
            Statement::SetDiscriminant { .. }
            | Statement::Deinit { .. }
            | Statement::Retag { .. }
            | Statement::PlaceMention(_)
            | Statement::Intrinsic { .. }
            | Statement::CopyNonOverlapping { .. }
            | Statement::Unsupported { .. } => Err(ViewRefusal::UnsupportedConstruct {
                detail: format!("statement {statement:?}"),
            }),
        }
    }

    fn storage_local(&self, local: usize) -> Result<usize, ViewRefusal> {
        if self.scalarized.contains_key(&local) {
            return Err(ViewRefusal::BorrowNotScalarRead {
                local,
                detail: "it carries a storage marker".to_string(),
            });
        }
        self.plain.get(local).copied().flatten().ok_or_else(|| ViewRefusal::MalformedBody {
            detail: format!("storage marker names local `_{local}`, which does not exist"),
        })
    }

    fn terminator(&self, terminator: &Terminator) -> Result<Terminator, ViewRefusal> {
        match terminator {
            Terminator::Goto(target) => Ok(Terminator::Goto(*target)),
            Terminator::Return => Ok(Terminator::Return),
            Terminator::SwitchInt {
                discr,
                targets,
                otherwise,
                exhaustive_enum_unreachable,
                span,
            } => Ok(Terminator::SwitchInt {
                discr: self.operand(discr)?,
                targets: targets.clone(),
                otherwise: *otherwise,
                exhaustive_enum_unreachable: *exhaustive_enum_unreachable,
                span: span.clone(),
            }),
            Terminator::Call {
                func,
                args,
                dest,
                target,
                span,
                atomic,
                is_foreign,
                is_unsafe_sig,
                unwind,
                callee_identity,
                callee_key,
            } => {
                let mut rewritten = Vec::with_capacity(args.len());
                for arg in args {
                    rewritten.push(self.operand(arg)?);
                }
                Ok(Terminator::Call {
                    func: func.clone(),
                    args: rewritten,
                    dest: self.write_place(dest)?,
                    target: *target,
                    span: span.clone(),
                    atomic: atomic.clone(),
                    is_foreign: *is_foreign,
                    is_unsafe_sig: *is_unsafe_sig,
                    unwind: unwind.clone(),
                    callee_identity: callee_identity.clone(),
                    // The param view REWRITES OPERANDS ONLY; the callee is the
                    // same item, so its structured key survives unchanged.
                    // Dropping it would send the unsafe mint back to display
                    // text for every call this view passes through.
                    callee_key: callee_key.clone(),
                })
            }
            Terminator::TailCall {
                func,
                args,
                span,
                atomic,
                is_foreign,
                is_unsafe_sig,
                callee_identity,
                callee_key,
            } => {
                let mut rewritten = Vec::with_capacity(args.len());
                for arg in args {
                    rewritten.push(self.operand(arg)?);
                }
                Ok(Terminator::TailCall {
                    func: func.clone(),
                    args: rewritten,
                    span: span.clone(),
                    atomic: atomic.clone(),
                    is_foreign: *is_foreign,
                    is_unsafe_sig: *is_unsafe_sig,
                    callee_identity: callee_identity.clone(),
                    callee_key: callee_key.clone(),
                })
            }
            Terminator::Assert { cond, expected, msg, target, span, unwind } => {
                Ok(Terminator::Assert {
                    cond: self.operand(cond)?,
                    expected: *expected,
                    msg: msg.clone(),
                    target: *target,
                    span: span.clone(),
                    unwind: unwind.clone(),
                })
            }
            Terminator::Drop { .. }
            | Terminator::Opaque { .. }
            | Terminator::Unreachable
            | Terminator::Resume => Err(ViewRefusal::UnsupportedConstruct {
                detail: format!("terminator {terminator:?}"),
            }),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        AggregateKind, BinOp, BlockId, ConstValue, SourceSpan, UnwindEdge, VerifiableBody,
    };

    /// `Point { x: u32, y: u32 }` as the EXTRACTOR spells it: a real struct
    /// (`adt_kind: Some(Struct)`), not a hand-built `Ty::adt` (whose
    /// `adt_kind` is `None` and which the view therefore refuses).
    fn point_ty(fields: Vec<(String, Ty)>) -> Ty {
        let Ty::Adt {
            name,
            variants,
            disc_index_safe,
            faithful_enum_repr,
            layout,
            enum_layout,
            arbitrary_precision,
            validity_wrapper,
            ..
        } = Ty::adt("k::Point", fields.clone())
        else {
            unreachable!("Ty::adt builds an Adt")
        };
        Ty::Adt {
            name,
            fields: fields.into(),
            variants,
            disc_index_safe,
            faithful_enum_repr,
            layout,
            enum_layout,
            adt_kind: Some(AdtKind::Struct),
            arbitrary_precision,
            validity_wrapper,
        }
    }

    fn point() -> Ty {
        point_ty(vec![("x".into(), Ty::u32()), ("y".into(), Ty::u32())])
    }

    fn frozen_self(rows: Vec<(usize, &str, &str)>) -> FrozenSharedParams {
        let mut table = FrozenSharedParams::new();
        table.insert(
            0,
            FrozenPointee {
                param_name: "self".into(),
                adt_name: "k::Point".into(),
                rows: rows
                    .into_iter()
                    .map(|(field_index, field_name, carrier)| FrozenRow {
                        field_index,
                        field_name: field_name.into(),
                        carrier: carrier.into(),
                    })
                    .collect(),
            },
        );
        table
    }

    fn assign(place: Place, rvalue: Rvalue) -> Statement {
        Statement::Assign { place, rvalue, span: SourceSpan::default() }
    }

    fn deref_field(local: usize, field: usize) -> Place {
        Place { local, projections: vec![Projection::Deref, Projection::Field(field)] }
    }

    fn bare(local: usize) -> Place {
        Place { local, projections: Vec::new() }
    }

    /// `fn x_ref(&self) -> u32 { self.x }` exactly as probe `v08` measured the
    /// extracted body: `_0 = Copy((*_1).0); return`, locals
    /// `[_0: u32, _1 "self": &Point]`.
    fn x_ref(stmts: Vec<Statement>) -> VerifiableFunction {
        VerifiableFunction {
            name: "x_ref".into(),
            def_path: "k::Point::x_ref".into(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::u32(), name: None },
                    LocalDecl {
                        index: 1,
                        ty: Ty::Ref { mutable: false, inner: Box::new(point()) },
                        name: Some("self".into()),
                    },
                ],
                blocks: vec![BasicBlock { id: BlockId(0), stmts, terminator: Terminator::Return }],
                arg_count: 1,
                return_ty: Ty::u32(),
                datatype_defs: Default::default(),
            },
            contracts: Vec::new(),
            preconditions: Vec::new(),
            postconditions: Vec::new(),
            spec: Default::default(),
            tuple_layouts: Default::default(),
        }
    }

    fn getter() -> VerifiableFunction {
        x_ref(vec![assign(bare(0), Rvalue::Use(Operand::Copy(deref_field(1, 0))))])
    }

    fn rows_xy() -> FrozenSharedParams {
        frozen_self(vec![(0, "x", "u32"), (1, "y", "u32")])
    }

    // ---------------------------------------------------------------- positive

    #[test]
    fn a_ref_self_getter_becomes_a_two_parameter_scalar_projection() {
        let view = e6_param_view(&getter(), &rows_xy()).expect("admitted").expect("a view exists");
        assert_eq!(view.param_names, vec!["self.x".to_string(), "self.y".to_string()]);
        assert_eq!(view.erased_params, vec!["self".to_string()]);
        assert_eq!(view.func.body.arg_count, 2);
        assert_eq!(view.func.def_path, "k::Point::x_ref", "the view keeps the function identity");
        // Locals are dense and carry the clause-side names, which is what
        // `clean_island::param_flat_rows` reads back.
        let names: Vec<Option<&str>> =
            view.func.body.locals.iter().map(|l| l.name.as_deref()).collect();
        assert_eq!(names, vec![None, Some("self.x"), Some("self.y")]);
        for (index, local) in view.func.body.locals.iter().enumerate() {
            assert_eq!(local.index, index, "the validator requires dense local indices");
        }
        // …and the body is the by-value projection the recognizer admits.
        assert_eq!(
            crate::admissible_body::recognize_admissible_body(&view.func),
            Some(crate::admissible_body::AdmissibleBody::Projection { param: 0 }),
            "the scalarized body must recognize as the by-value twin's shape"
        );
    }

    #[test]
    fn the_view_is_certified_where_the_borrow_bearing_body_is_not() {
        // The point of the view: the UNCHANGED validator certifies it.
        let view = e6_param_view(&getter(), &rows_xy()).unwrap().unwrap();
        let facets = crate::facet_inference::infer_facets(std::slice::from_ref(&view.func));
        assert!(
            facets.get("k::Point::x_ref").copied().unwrap_or_default().all(),
            "the view must be all-four-facet certified in isolation"
        );
        // …and the ORIGINAL body still is not, so nothing was weakened.
        let original = getter();
        let before = crate::facet_inference::infer_facets(std::slice::from_ref(&original));
        assert!(
            !before.get("k::Point::x_ref").copied().unwrap_or_default().all(),
            "the borrow-bearing body must still be refused by the unchanged validator"
        );
    }

    #[test]
    fn a_second_field_read_is_admitted_and_maps_to_its_own_parameter() {
        let f = x_ref(vec![assign(bare(0), Rvalue::Use(Operand::Copy(deref_field(1, 1))))]);
        let view = e6_param_view(&f, &rows_xy()).unwrap().unwrap();
        assert_eq!(
            crate::admissible_body::recognize_admissible_body(&view.func),
            Some(crate::admissible_body::AdmissibleBody::Projection { param: 1 }),
            "`self.y` must project parameter 1, not parameter 0"
        );
    }

    #[test]
    fn a_body_with_no_reference_parameter_returns_ok_none() {
        let mut f = getter();
        f.body.locals[1] = LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) };
        f.body.blocks[0].stmts = vec![assign(bare(0), Rvalue::Use(Operand::Copy(bare(1))))];
        assert!(
            e6_param_view(&f, &FrozenSharedParams::new()).unwrap().is_none(),
            "with no borrow the caller must use today's body byte for byte"
        );
    }

    #[test]
    fn a_by_value_scalar_beside_the_borrow_keeps_its_own_name_and_position() {
        let mut f = getter();
        f.body.locals.push(LocalDecl { index: 2, ty: Ty::u32(), name: Some("bump".into()) });
        f.body.arg_count = 2;
        f.body.blocks[0].stmts = vec![assign(
            bare(0),
            Rvalue::BinaryOp(BinOp::Add, Operand::Copy(deref_field(1, 0)), Operand::Copy(bare(2))),
        )];
        let view = e6_param_view(&f, &rows_xy()).unwrap().unwrap();
        assert_eq!(
            view.param_names,
            vec!["self.x".to_string(), "self.y".to_string(), "bump".to_string()],
            "the erased borrow's rows come first, in declaration order, then the by-value scalar"
        );
        assert_eq!(view.func.body.arg_count, 3);
    }

    #[test]
    fn a_temporary_is_renumbered_past_the_expansion() {
        let mut f = getter();
        f.body.locals.push(LocalDecl { index: 2, ty: Ty::u32(), name: None });
        f.body.blocks[0].stmts = vec![
            assign(bare(2), Rvalue::Use(Operand::Copy(deref_field(1, 0)))),
            assign(bare(0), Rvalue::Use(Operand::Copy(bare(2)))),
        ];
        let view = e6_param_view(&f, &rows_xy()).unwrap().unwrap();
        // `self` became locals 1 and 2, so the temporary must have moved to 3.
        assert_eq!(view.func.body.locals.len(), 4);
        let Statement::Assign { place, .. } = &view.func.body.blocks[0].stmts[0] else {
            panic!("expected an assignment")
        };
        assert_eq!(place.local, 3, "the temporary must be renumbered past the expansion");
        for (index, local) in view.func.body.locals.iter().enumerate() {
            assert_eq!(local.index, index);
        }
    }

    // ---------------------------------------------------------- close negatives

    #[test]
    fn n_a_mutable_borrow_has_no_table_row_and_is_refused() {
        let mut f = getter();
        f.body.locals[1].ty = Ty::Ref { mutable: true, inner: Box::new(point()) };
        // The compiler's table never admits a `&mut`, so the view sees a
        // reference parameter with no row.
        let refusal = e6_param_view(&f, &FrozenSharedParams::new()).unwrap_err();
        assert!(
            matches!(refusal, ViewRefusal::UnsupportedParam { local: 1, .. }),
            "got {refusal:?}"
        );
    }

    #[test]
    fn n_a_mutable_borrow_is_refused_even_if_a_table_claimed_it() {
        // Defence in depth: C4 re-reads the extracted mutability, so a table
        // that wrongly claimed a `&mut` pointee still mints nothing.
        let mut f = getter();
        f.body.locals[1].ty = Ty::Ref { mutable: true, inner: Box::new(point()) };
        let refusal = e6_param_view(&f, &rows_xy()).unwrap_err();
        assert!(
            matches!(refusal, ViewRefusal::PointeeMismatch { local: 1, .. }),
            "got {refusal:?}"
        );
    }

    #[test]
    fn n_a_hand_built_adt_without_a_struct_kind_is_refused() {
        // `Ty::adt` leaves `adt_kind: None`; only the rustc-driven extractor
        // stamps `Some(Struct)`. A union is `Some(Union)` and lands here too.
        let mut f = getter();
        f.body.locals[1].ty = Ty::Ref {
            mutable: false,
            inner: Box::new(Ty::adt(
                "k::Point",
                vec![("x".into(), Ty::u32()), ("y".into(), Ty::u32())],
            )),
        };
        let refusal = e6_param_view(&f, &rows_xy()).unwrap_err();
        assert!(
            matches!(refusal, ViewRefusal::PointeeMismatch { local: 1, .. }),
            "got {refusal:?}"
        );
    }

    #[test]
    fn n_a_carrier_disagreement_refuses_the_whole_view() {
        // The table says `u32`; the extracted field is `u64`. A wrong carrier
        // would mint a defining equation at the wrong width.
        let mut f = getter();
        f.body.locals[1].ty = Ty::Ref {
            mutable: false,
            inner: Box::new(point_ty(vec![("x".into(), Ty::u64()), ("y".into(), Ty::u32())])),
        };
        let refusal = e6_param_view(&f, &rows_xy()).unwrap_err();
        assert!(
            matches!(&refusal, ViewRefusal::FieldMismatch { local: 1, field, .. } if field == "x"),
            "got {refusal:?}"
        );
    }

    #[test]
    fn n_a_field_name_disagreement_refuses_the_whole_view() {
        let mut f = getter();
        f.body.locals[1].ty = Ty::Ref {
            mutable: false,
            inner: Box::new(point_ty(vec![("row".into(), Ty::u32()), ("y".into(), Ty::u32())])),
        };
        let refusal = e6_param_view(&f, &rows_xy()).unwrap_err();
        assert!(
            matches!(&refusal, ViewRefusal::FieldMismatch { local: 1, field, .. } if field == "x"),
            "got {refusal:?}"
        );
    }

    #[test]
    fn n_a_pointee_name_disagreement_refuses_the_whole_view() {
        let mut f = getter();
        f.body.locals[1].ty = Ty::Ref {
            mutable: false,
            inner: Box::new(point_ty(vec![("x".into(), Ty::u32()), ("y".into(), Ty::u32())])),
        };
        let Ty::Ref { inner, .. } = &mut f.body.locals[1].ty else { unreachable!() };
        let Ty::Adt { name, .. } = inner.as_mut() else { unreachable!() };
        *name = "k::Other".into();
        let refusal = e6_param_view(&f, &rows_xy()).unwrap_err();
        assert!(
            matches!(refusal, ViewRefusal::PointeeMismatch { local: 1, .. }),
            "got {refusal:?}"
        );
    }

    #[test]
    fn n_a_whole_pointee_read_is_refused() {
        // `derive(Clone)`'s `clone(&self)` is `_0 = Copy(*_1)` — a read of the
        // whole struct, which no scalar row denotes ([M-2] probe v08).
        let f = x_ref(vec![assign(
            bare(0),
            Rvalue::Use(Operand::Copy(Place { local: 1, projections: vec![Projection::Deref] })),
        )]);
        let refusal = e6_param_view(&f, &rows_xy()).unwrap_err();
        assert!(
            matches!(refusal, ViewRefusal::BorrowNotScalarRead { local: 1, .. }),
            "got {refusal:?}"
        );
    }

    #[test]
    fn n_a_bare_borrow_operand_is_refused() {
        let f = x_ref(vec![assign(bare(0), Rvalue::Use(Operand::Copy(bare(1))))]);
        let refusal = e6_param_view(&f, &rows_xy()).unwrap_err();
        assert!(
            matches!(refusal, ViewRefusal::BorrowNotScalarRead { local: 1, .. }),
            "got {refusal:?}"
        );
    }

    #[test]
    fn n_a_moved_borrow_is_refused() {
        let f = x_ref(vec![assign(bare(0), Rvalue::Use(Operand::Move(deref_field(1, 0))))]);
        let refusal = e6_param_view(&f, &rows_xy()).unwrap_err();
        assert!(
            matches!(&refusal, ViewRefusal::BorrowNotScalarRead { local: 1, detail }
                if detail.contains("MOVED")),
            "got {refusal:?}"
        );
    }

    #[test]
    fn n_an_unlisted_field_is_refused() {
        // The table lists `x` only; the body reads field 1.
        let f = x_ref(vec![assign(bare(0), Rvalue::Use(Operand::Copy(deref_field(1, 1))))]);
        let refusal = e6_param_view(&f, &frozen_self(vec![(0, "x", "u32")])).unwrap_err();
        assert!(
            matches!(&refusal, ViewRefusal::BorrowNotScalarRead { local: 1, detail }
                if detail.contains("not a readable row")),
            "got {refusal:?}"
        );
    }

    #[test]
    fn n_a_deeper_projection_through_the_borrow_is_refused() {
        let f = x_ref(vec![assign(
            bare(0),
            Rvalue::Use(Operand::Copy(Place {
                local: 1,
                projections: vec![Projection::Deref, Projection::Field(0), Projection::Field(0)],
            })),
        )]);
        let refusal = e6_param_view(&f, &rows_xy()).unwrap_err();
        assert!(
            matches!(refusal, ViewRefusal::BorrowNotScalarRead { local: 1, .. }),
            "got {refusal:?}"
        );
    }

    #[test]
    fn n_an_address_escape_is_refused() {
        let f = x_ref(vec![assign(bare(0), Rvalue::AddressOf(false, deref_field(1, 0)))]);
        let refusal = e6_param_view(&f, &rows_xy()).unwrap_err();
        assert!(
            matches!(&refusal, ViewRefusal::UnsupportedConstruct { detail }
                if detail.contains("address")),
            "got {refusal:?}"
        );
    }

    #[test]
    fn n_a_reborrow_is_refused() {
        let f =
            x_ref(vec![assign(bare(0), Rvalue::Ref { mutable: false, place: deref_field(1, 0) })]);
        let refusal = e6_param_view(&f, &rows_xy()).unwrap_err();
        assert!(
            matches!(&refusal, ViewRefusal::UnsupportedConstruct { detail }
                if detail.contains("address")),
            "got {refusal:?}"
        );
    }

    #[test]
    fn n_a_copy_for_deref_is_refused() {
        let f = x_ref(vec![assign(bare(0), Rvalue::CopyForDeref(deref_field(1, 0)))]);
        let refusal = e6_param_view(&f, &rows_xy()).unwrap_err();
        assert!(matches!(refusal, ViewRefusal::UnsupportedConstruct { .. }), "got {refusal:?}");
    }

    #[test]
    fn n_a_borrow_forwarded_to_a_sibling_method_is_refused() {
        let mut f = getter();
        f.body.locals.push(LocalDecl { index: 2, ty: Ty::u32(), name: None });
        f.body.blocks = vec![
            BasicBlock {
                id: BlockId(0),
                stmts: Vec::new(),
                terminator: Terminator::Call {
                    func: "k::Point::helper".into(),
                    args: vec![Operand::Copy(bare(1))],
                    dest: bare(2),
                    target: Some(BlockId(1)),
                    span: SourceSpan::default(),
                    atomic: None,
                    is_foreign: false,
                    is_unsafe_sig: false,
                    unwind: UnwindEdge::default(),
                    callee_identity: None,
                    callee_key: None,
                },
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![assign(bare(0), Rvalue::Use(Operand::Copy(bare(2))))],
                terminator: Terminator::Return,
            },
        ];
        let refusal = e6_param_view(&f, &rows_xy()).unwrap_err();
        assert!(
            matches!(refusal, ViewRefusal::BorrowNotScalarRead { local: 1, .. }),
            "passing the borrow to a sibling reaches state this view does not model: {refusal:?}"
        );
    }

    #[test]
    fn n_a_write_through_the_borrow_is_refused() {
        let f = x_ref(vec![
            assign(deref_field(1, 0), Rvalue::Use(Operand::Constant(ConstValue::Uint(1, 32)))),
            assign(bare(0), Rvalue::Use(Operand::Copy(deref_field(1, 0)))),
        ]);
        let refusal = e6_param_view(&f, &rows_xy()).unwrap_err();
        assert!(
            matches!(&refusal, ViewRefusal::BorrowNotScalarRead { local: 1, detail }
                if detail.contains("destination")),
            "got {refusal:?}"
        );
    }

    #[test]
    fn n_a_call_destination_rooted_at_the_borrow_is_refused() {
        let mut f = getter();
        f.body.blocks = vec![
            BasicBlock {
                id: BlockId(0),
                stmts: Vec::new(),
                terminator: Terminator::Call {
                    func: "k::mk".into(),
                    args: Vec::new(),
                    dest: deref_field(1, 0),
                    target: Some(BlockId(1)),
                    span: SourceSpan::default(),
                    atomic: None,
                    is_foreign: false,
                    is_unsafe_sig: false,
                    unwind: UnwindEdge::default(),
                    callee_identity: None,
                    callee_key: None,
                },
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![assign(bare(0), Rvalue::Use(Operand::Copy(deref_field(1, 0))))],
                terminator: Terminator::Return,
            },
        ];
        let refusal = e6_param_view(&f, &rows_xy()).unwrap_err();
        assert!(
            matches!(&refusal, ViewRefusal::BorrowNotScalarRead { local: 1, detail }
                if detail.contains("destination")),
            "got {refusal:?}"
        );
    }

    #[test]
    fn n_a_closure_form_contract_capturing_the_borrow_is_named_as_such() {
        let mut f = getter();
        f.body.locals.push(LocalDecl { index: 2, ty: Ty::Tuple(vec![Ty::u32()]), name: None });
        f.body.blocks[0].stmts = vec![
            assign(bare(2), Rvalue::Aggregate(AggregateKind::Tuple, vec![Operand::Copy(bare(1))])),
            assign(bare(0), Rvalue::Use(Operand::Copy(deref_field(1, 0)))),
        ];
        let refusal = e6_param_view(&f, &rows_xy()).unwrap_err();
        assert!(
            matches!(refusal, ViewRefusal::BorrowCapturedByAggregate { local: 1 }),
            "got {refusal:?}"
        );
    }

    #[test]
    fn an_aggregate_over_scalar_field_reads_is_still_walked_and_admitted() {
        // Control for the test above: the aggregate refusal is about the BARE
        // borrow, not about aggregates.
        let mut f = getter();
        f.body.locals.push(LocalDecl { index: 2, ty: Ty::Tuple(vec![Ty::u32()]), name: None });
        f.body.blocks[0].stmts = vec![
            assign(
                bare(2),
                Rvalue::Aggregate(AggregateKind::Tuple, vec![Operand::Copy(deref_field(1, 0))]),
            ),
            assign(bare(0), Rvalue::Use(Operand::Copy(deref_field(1, 0)))),
        ];
        let view = e6_param_view(&f, &rows_xy()).expect("no refusal").expect("a view");
        assert_eq!(view.func.body.arg_count, 2);
    }

    #[test]
    fn n_a_reference_return_is_refused() {
        let mut f = getter();
        f.body.return_ty = Ty::Ref { mutable: false, inner: Box::new(Ty::u32()) };
        f.body.locals[0].ty = f.body.return_ty.clone();
        let refusal = e6_param_view(&f, &rows_xy()).unwrap_err();
        assert!(matches!(refusal, ViewRefusal::ReturnNotScalar { .. }), "got {refusal:?}");
    }

    #[test]
    fn n_a_struct_return_is_refused() {
        let mut f = getter();
        f.body.return_ty = point();
        f.body.locals[0].ty = point();
        let refusal = e6_param_view(&f, &rows_xy()).unwrap_err();
        assert!(matches!(refusal, ViewRefusal::ReturnNotScalar { .. }), "got {refusal:?}");
    }

    #[test]
    fn n_a_raw_pointer_parameter_beside_a_table_entry_is_refused() {
        let mut f = getter();
        f.body.locals[1].ty = Ty::RawPtr { mutable: false, pointee: Box::new(point()) };
        f.body.blocks[0].stmts =
            vec![assign(bare(0), Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 32))))];
        let refusal = e6_param_view(&f, &rows_xy()).unwrap_err();
        assert!(
            matches!(refusal, ViewRefusal::PointeeMismatch { local: 1, .. }),
            "got {refusal:?}"
        );
    }

    #[test]
    fn n_a_second_reference_parameter_with_no_row_is_refused() {
        let mut f = getter();
        f.body.locals.push(LocalDecl {
            index: 2,
            ty: Ty::Ref { mutable: false, inner: Box::new(Ty::u32()) },
            name: Some("r".into()),
        });
        f.body.arg_count = 2;
        let refusal = e6_param_view(&f, &rows_xy()).unwrap_err();
        assert!(
            matches!(refusal, ViewRefusal::UnsupportedParam { local: 2, .. }),
            "a scalar pointee awaits ruling R5 and must stay refused: {refusal:?}"
        );
    }

    #[test]
    fn n_a_by_value_struct_parameter_beside_the_borrow_is_refused() {
        let mut f = getter();
        f.body.locals.push(LocalDecl { index: 2, ty: point(), name: Some("c".into()) });
        f.body.arg_count = 2;
        let refusal = e6_param_view(&f, &rows_xy()).unwrap_err();
        assert!(
            matches!(refusal, ViewRefusal::UnsupportedParam { local: 2, .. }),
            "the by-value struct scalarization is a separate design: {refusal:?}"
        );
    }

    #[test]
    fn n_an_unnamed_by_value_parameter_is_refused() {
        let mut f = getter();
        f.body.locals.push(LocalDecl { index: 2, ty: Ty::u32(), name: None });
        f.body.arg_count = 2;
        let refusal = e6_param_view(&f, &rows_xy()).unwrap_err();
        assert!(matches!(refusal, ViewRefusal::UnnamedParam { local: 2 }), "got {refusal:?}");
    }

    #[test]
    fn n_an_unnamed_borrowed_parameter_is_refused() {
        // `_: &Point` and `&Point { x, .. }: &Point` both extract with no local
        // name; the recorded prefix then has nothing to equal.
        let mut f = getter();
        f.body.locals[1].name = None;
        let refusal = e6_param_view(&f, &rows_xy()).unwrap_err();
        assert!(
            matches!(refusal, ViewRefusal::PointeeMismatch { local: 1, .. }),
            "got {refusal:?}"
        );
    }

    #[test]
    fn n_a_name_collision_between_a_row_and_a_by_value_parameter_is_refused() {
        // A parameter literally named `self.x` is not writable in Rust, but the
        // gate is cheap and the failure it prevents (two binders under one
        // name) is the one the kernel cannot see.
        let mut f = getter();
        f.body.locals.push(LocalDecl { index: 2, ty: Ty::u32(), name: Some("self.x".into()) });
        f.body.arg_count = 2;
        f.body.blocks[0].stmts = vec![assign(bare(0), Rvalue::Use(Operand::Copy(bare(2))))];
        let refusal = e6_param_view(&f, &rows_xy()).unwrap_err();
        assert!(
            matches!(&refusal, ViewRefusal::DuplicateViewParamName { name } if name == "self.x"),
            "got {refusal:?}"
        );
    }

    #[test]
    fn n_an_empty_row_list_is_refused() {
        let refusal = e6_param_view(&getter(), &frozen_self(Vec::new())).unwrap_err();
        assert!(matches!(refusal, ViewRefusal::EmptyRows { local: 1 }), "got {refusal:?}");
    }

    #[test]
    fn n_a_drop_terminator_is_refused() {
        let mut f = getter();
        f.body.blocks = vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![assign(bare(0), Rvalue::Use(Operand::Copy(deref_field(1, 0))))],
                terminator: Terminator::Drop {
                    place: bare(0),
                    target: BlockId(1),
                    span: SourceSpan::default(),
                    unwind: UnwindEdge::default(),
                },
            },
            BasicBlock { id: BlockId(1), stmts: Vec::new(), terminator: Terminator::Return },
        ];
        let refusal = e6_param_view(&f, &rows_xy()).unwrap_err();
        assert!(matches!(refusal, ViewRefusal::UnsupportedConstruct { .. }), "got {refusal:?}");
    }

    #[test]
    fn n_a_retag_statement_is_refused() {
        let f = x_ref(vec![
            Statement::Retag { place: bare(1) },
            assign(bare(0), Rvalue::Use(Operand::Copy(deref_field(1, 0)))),
        ]);
        let refusal = e6_param_view(&f, &rows_xy()).unwrap_err();
        assert!(matches!(refusal, ViewRefusal::UnsupportedConstruct { .. }), "got {refusal:?}");
    }

    #[test]
    fn n_a_place_mention_of_the_borrow_is_refused() {
        let f = x_ref(vec![
            Statement::PlaceMention(bare(1)),
            assign(bare(0), Rvalue::Use(Operand::Copy(deref_field(1, 0)))),
        ]);
        let refusal = e6_param_view(&f, &rows_xy()).unwrap_err();
        assert!(matches!(refusal, ViewRefusal::UnsupportedConstruct { .. }), "got {refusal:?}");
    }

    #[test]
    fn n_a_storage_marker_on_the_borrow_is_refused() {
        let f = x_ref(vec![
            Statement::StorageLive(1),
            assign(bare(0), Rvalue::Use(Operand::Copy(deref_field(1, 0)))),
        ]);
        let refusal = e6_param_view(&f, &rows_xy()).unwrap_err();
        assert!(
            matches!(refusal, ViewRefusal::BorrowNotScalarRead { local: 1, .. }),
            "got {refusal:?}"
        );
    }

    #[test]
    fn n_a_non_dense_local_vector_is_refused() {
        let mut f = getter();
        f.body.locals[1].index = 7;
        let refusal = e6_param_view(&f, &rows_xy()).unwrap_err();
        assert!(matches!(refusal, ViewRefusal::MalformedBody { .. }), "got {refusal:?}");
    }

    #[test]
    fn n_a_table_naming_a_parameter_the_body_does_not_have_is_refused() {
        let mut table = rows_xy();
        table.insert(
            4,
            FrozenPointee {
                param_name: "other".into(),
                adt_name: "k::Point".into(),
                rows: vec![FrozenRow {
                    field_index: 0,
                    field_name: "x".into(),
                    carrier: "u32".into(),
                }],
            },
        );
        let refusal = e6_param_view(&getter(), &table).unwrap_err();
        assert!(matches!(refusal, ViewRefusal::PointeeMismatch { .. }), "got {refusal:?}");
    }

    // ------------------------------------------------------- mutation controls

    #[test]
    fn m_the_field_index_is_load_bearing_for_the_minted_equation() {
        // A table that swapped the two rows' FIELD INDICES would mint
        // `fun p0 p1 => p1` for a body that returns `self.x`: a well-typed,
        // FALSE defining equation the kernel cannot catch. The view's
        // field-name re-check is what refuses it.
        let swapped = frozen_self(vec![(1, "x", "u32"), (0, "y", "u32")]);
        let refusal = e6_param_view(&getter(), &swapped).unwrap_err();
        assert!(matches!(refusal, ViewRefusal::FieldMismatch { .. }), "got {refusal:?}");
    }

    #[test]
    fn m_the_row_order_decides_which_view_parameter_a_read_becomes() {
        // Same two fields, DECLARED order reversed in the table. The body reads
        // field 0, so the view must project whichever position field 0 took —
        // and the recorded `param_names` must say the same — and they cannot
        // disagree, because both are written by the same loop from the same
        // rows. That is why `elaborate_ensures`' list comparison is NOT a
        // backstop on this lane: what actually refuses a table/IR mismatch is
        // `verify_frozen_local`'s per-row name check, measured by
        // `m_a_swapped_row_list_across_a_skipped_field_is_refused`.
        let reversed = frozen_self(vec![(1, "y", "u32"), (0, "x", "u32")]);
        let view = e6_param_view(&getter(), &reversed).unwrap().unwrap();
        assert_eq!(view.param_names, vec!["self.y".to_string(), "self.x".to_string()]);
        assert_eq!(
            crate::admissible_body::recognize_admissible_body(&view.func),
            Some(crate::admissible_body::AdmissibleBody::Projection { param: 1 }),
            "field 0 sits at view position 1 under this ordering"
        );
    }

    // ------------------------------------------------- I2: skipped-field rows
    //
    // Increment I2 (disposition R4, implementer-proposed) deleted the compiler-side all-or-nothing
    // rule D-REF-8: a declared field outside the scalar vocabulary is now
    // SKIPPED and its siblings still get rows. NOTHING IN THIS MODULE CHANGED
    // for it — the view already verified only the fields the table listed, and
    // that is the property I2 rests on. These tests measure it rather than
    // assume it, at the exact shapes I2 newly admits.

    /// `Cursor { row: u32, limit: u32, cells: <opaque> }` as the extractor
    /// spells it: three DECLARED fields in declaration order, the third of a
    /// type this lane cannot carry. `Vec<u8>` lowers to something this module
    /// must never inspect, so the test uses a stand-in the module is equally
    /// blind to and asserts the blindness.
    fn cursor_ty(third: Ty) -> Ty {
        cursor_ty_named(
            "k::Cursor",
            vec![
                ("row".to_string(), Ty::u32()),
                ("limit".to_string(), Ty::u32()),
                ("cells".to_string(), third),
            ],
        )
    }

    /// A struct ADT with the extractor's `adt_kind` stamp, under an arbitrary
    /// name and field list. `point_ty` is the fixed `k::Point` case of it.
    fn cursor_ty_named(name: &str, fields: Vec<(String, Ty)>) -> Ty {
        let Ty::Adt {
            variants,
            disc_index_safe,
            faithful_enum_repr,
            layout,
            enum_layout,
            arbitrary_precision,
            validity_wrapper,
            ..
        } = Ty::adt(name, fields.clone())
        else {
            unreachable!("Ty::adt builds an Adt")
        };
        Ty::Adt {
            name: name.to_string(),
            fields: fields.into(),
            variants,
            disc_index_safe,
            faithful_enum_repr,
            layout,
            enum_layout,
            adt_kind: Some(AdtKind::Struct),
            arbitrary_precision,
            validity_wrapper,
        }
    }

    /// `fn row_of(&self) -> u32 { .. }` over `Cursor`, with `stmts` as the body.
    fn cursor_fn(third: Ty, stmts: Vec<Statement>) -> VerifiableFunction {
        let mut f = x_ref(stmts);
        f.name = "row_of".into();
        f.def_path = "k::Cursor::row_of".into();
        f.body.locals[1].ty = Ty::Ref { mutable: false, inner: Box::new(cursor_ty(third)) };
        f
    }

    fn cursor_rows(adt_name: &str) -> FrozenSharedParams {
        let mut table = FrozenSharedParams::new();
        table.insert(
            0,
            FrozenPointee {
                param_name: "self".into(),
                adt_name: adt_name.into(),
                rows: vec![
                    FrozenRow { field_index: 0, field_name: "row".into(), carrier: "u32".into() },
                    FrozenRow { field_index: 1, field_name: "limit".into(), carrier: "u32".into() },
                ],
            },
        );
        table
    }

    /// THE I2 PAYOFF, at this layer. The table lists two of three declared
    /// fields; the third is outside the vocabulary and is never mentioned. The
    /// view is built over the two, the skipped field contributes NO parameter,
    /// and the minted shape is the same `Projection { param: 0 }` the
    /// all-scalar case produces.
    #[test]
    fn a_partial_row_list_builds_a_view_over_the_scalar_fields_alone() {
        let f = cursor_fn(
            Ty::Float { width: 64 },
            vec![assign(bare(0), Rvalue::Use(Operand::Copy(deref_field(1, 0))))],
        );
        let view = e6_param_view(&f, &cursor_rows("k::Cursor")).unwrap().unwrap();
        assert_eq!(view.param_names, vec!["self.row".to_string(), "self.limit".to_string()]);
        assert_eq!(view.func.body.arg_count, 2, "the skipped field contributes no parameter");
        assert_eq!(
            crate::admissible_body::recognize_admissible_body(&view.func),
            Some(crate::admissible_body::AdmissibleBody::Projection { param: 0 }),
        );
    }

    /// The skipped field's IR TYPE is never inspected. The extractor may lower
    /// a `Vec`/`String`/map field to anything at all — an opaque ADT, a
    /// compacted by-name datatype — and the view must not care, because the
    /// body can never read it. Four unrelated lowerings, one result.
    #[test]
    fn the_lowering_of_a_skipped_field_is_never_inspected() {
        for third in [
            Ty::Float { width: 64 },
            Ty::adt("alloc::vec::Vec", vec![("len".into(), Ty::u64())]),
            Ty::Str,
            Ty::Ref { mutable: true, inner: Box::new(Ty::u8()) },
        ] {
            let f = cursor_fn(
                third.clone(),
                vec![assign(bare(0), Rvalue::Use(Operand::Copy(deref_field(1, 0))))],
            );
            let view = e6_param_view(&f, &cursor_rows("k::Cursor"))
                .unwrap_or_else(|e| panic!("refused for {third:?}: {e}"))
                .expect("a view exists");
            assert_eq!(view.param_names.len(), 2, "for {third:?}");
        }
    }

    /// A SKIPPED field in the MIDDLE of the declaration order. This is the
    /// index-mapping test that a leading or trailing skip cannot make: the
    /// listed rows keep their DECLARED indices (0 and 2), the body's
    /// `Field(2)` read must land on view position 1, and `Field(1)` — the
    /// skipped one — must refuse.
    #[test]
    fn a_skipped_middle_field_keeps_the_declared_index_of_its_siblings() {
        let mut f = x_ref(vec![assign(bare(0), Rvalue::Use(Operand::Copy(deref_field(1, 2))))]);
        f.body.locals[1].ty = Ty::Ref {
            mutable: false,
            inner: Box::new(cursor_ty_named(
                "k::Gap",
                vec![
                    ("head".to_string(), Ty::u32()),
                    ("body".to_string(), Ty::Float { width: 64 }),
                    ("tail".to_string(), Ty::u32()),
                ],
            )),
        };
        let mut table = FrozenSharedParams::new();
        table.insert(
            0,
            FrozenPointee {
                param_name: "self".into(),
                adt_name: "k::Gap".into(),
                rows: vec![
                    FrozenRow { field_index: 0, field_name: "head".into(), carrier: "u32".into() },
                    FrozenRow { field_index: 2, field_name: "tail".into(), carrier: "u32".into() },
                ],
            },
        );
        let view = e6_param_view(&f, &table).unwrap().unwrap();
        assert_eq!(view.param_names, vec!["self.head".to_string(), "self.tail".to_string()]);
        assert_eq!(
            crate::admissible_body::recognize_admissible_body(&view.func),
            Some(crate::admissible_body::AdmissibleBody::Projection { param: 1 }),
            "declared field 2 is view parameter 1"
        );
    }

    /// THE CLOSE NEGATIVE TWIN of the payoff: a body that READS a skipped
    /// field. The view has no value for it — that is the whole point of
    /// skipping — so the WHOLE view refuses and the function mints nothing.
    /// Anything weaker would mint a defining equation over a value the body
    /// does not compute from.
    #[test]
    fn n_a_body_that_reads_a_skipped_field_refuses_the_whole_view() {
        let f = cursor_fn(
            Ty::Float { width: 64 },
            vec![assign(bare(0), Rvalue::Use(Operand::Copy(deref_field(1, 2))))],
        );
        let refusal = e6_param_view(&f, &cursor_rows("k::Cursor")).unwrap_err();
        assert!(
            matches!(&refusal, ViewRefusal::BorrowNotScalarRead { local: 1, detail }
                if detail.contains("not a readable row")),
            "got {refusal:?}"
        );
    }

    /// The table can never make a non-scalar field into a row by CLAIMING one.
    /// If the compiler's filter and the extracted IR ever disagreed about
    /// `cells`, this is the net: the view types every LISTED field against the
    /// IR and refuses the whole view. It is why the skip is safe to make on one
    /// side only.
    #[test]
    fn n_a_table_that_lists_a_non_scalar_field_refuses_the_whole_view() {
        let f = cursor_fn(
            Ty::Float { width: 64 },
            vec![assign(bare(0), Rvalue::Use(Operand::Copy(deref_field(1, 0))))],
        );
        let mut table = cursor_rows("k::Cursor");
        table.get_mut(&0).unwrap().rows.push(FrozenRow {
            field_index: 2,
            field_name: "cells".into(),
            carrier: "u64".into(),
        });
        let refusal = e6_param_view(&f, &table).unwrap_err();
        assert!(
            matches!(&refusal, ViewRefusal::FieldMismatch { field, .. } if field == "cells"),
            "got {refusal:?}"
        );
    }

    /// **THE `Freeze` LOAD-BEARING MEASUREMENT, and the reason the compiler
    /// must not lose C2 or K2.**
    ///
    /// Before I2 a `Cell<u32>` SIBLING was refused twice: by `is_freeze` (C2)
    /// and K2 in the compiler, and again by the carrier rule, because
    /// `Cell<u32>` is an ADT outside the scalar vocabulary and the flattening
    /// was all-or-nothing. I2 deletes the second net BY CONSTRUCTION — a cell
    /// sibling is skipped exactly like a `Vec` one.
    ///
    /// This test is that deletion, measured: hand the view the table a
    /// compiler with `is_freeze` and K2 STUBBED OUT would produce for
    /// `Counter { n: u32, hits: Cell<u32> }`, and the view builds. Nothing in
    /// `trust-types` refuses it, and nothing in `trust-types` can: interior
    /// mutability is not visible in the extracted IR, where `Cell<u32>` is an
    /// ordinary one-field ADT. **From I2 on, C2 and K2 are the only thing
    /// standing between this lane and a defining equation over bytes another
    /// alias may legally mutate during the call.** `docs/TCB.md`'s
    /// `EnsuresCitationViewDischarge` row says so; probes `f71`/`f84` against
    /// their `Freeze` twin `f85` are the end-to-end differential.
    #[test]
    fn m_freeze_is_the_only_net_left_for_a_cell_sibling() {
        let cell_u32 = Ty::adt("core::cell::Cell", vec![("value".into(), Ty::u32())]);
        let mut f = x_ref(vec![assign(bare(0), Rvalue::Use(Operand::Copy(deref_field(1, 0))))]);
        f.body.locals[1].ty = Ty::Ref {
            mutable: false,
            inner: Box::new(cursor_ty_named(
                "k::Counter",
                vec![("n".to_string(), Ty::u32()), ("hits".to_string(), cell_u32)],
            )),
        };
        let mut table = FrozenSharedParams::new();
        table.insert(
            0,
            FrozenPointee {
                param_name: "self".into(),
                adt_name: "k::Counter".into(),
                rows: vec![FrozenRow {
                    field_index: 0,
                    field_name: "n".into(),
                    carrier: "u32".into(),
                }],
            },
        );
        let view = e6_param_view(&f, &table)
            .expect("the IR carries no interior-mutability fact, so this layer cannot refuse")
            .expect("a view exists");
        assert_eq!(
            view.param_names,
            vec!["self.n".to_string()],
            "the cell sibling is skipped like any other unsupported field — C2/K2 are the net"
        );
    }

    /// THE FIELD-ORDER SWAP, with a SKIPPED field in the way — the mutation
    /// `m_the_field_index_is_load_bearing_for_the_minted_equation` makes on the
    /// all-scalar shape, re-made where the index arithmetic is not the identity.
    ///
    /// The table claims `head` is at declared index 2 and `tail` at 0, which
    /// would mint `fun p0 p1 => p1` for a body returning `head` — well-typed,
    /// FALSE, and invisible to the kernel, because a swap keeps the goal
    /// well-typed. What refuses it is the view typing each LISTED row against
    /// the extracted IR by NAME, not the carrier (both are `u32`, so a carrier
    /// check would pass). Its end-to-end pin is probe `f94`, whose island
    /// definition distinguishes its two arguments.
    #[test]
    fn m_a_swapped_row_list_across_a_skipped_field_is_refused() {
        let mut f = x_ref(vec![assign(bare(0), Rvalue::Use(Operand::Copy(deref_field(1, 0))))]);
        f.body.locals[1].ty = Ty::Ref {
            mutable: false,
            inner: Box::new(cursor_ty_named(
                "k::Gap",
                vec![
                    ("head".to_string(), Ty::u32()),
                    ("body".to_string(), Ty::Float { width: 64 }),
                    ("tail".to_string(), Ty::u32()),
                ],
            )),
        };
        let mut table = FrozenSharedParams::new();
        table.insert(
            0,
            FrozenPointee {
                param_name: "self".into(),
                adt_name: "k::Gap".into(),
                rows: vec![
                    FrozenRow { field_index: 2, field_name: "head".into(), carrier: "u32".into() },
                    FrozenRow { field_index: 0, field_name: "tail".into(), carrier: "u32".into() },
                ],
            },
        );
        let refusal = e6_param_view(&f, &table).unwrap_err();
        assert!(
            matches!(&refusal, ViewRefusal::FieldMismatch { field, .. }
                if field == "head" || field == "tail"),
            "got {refusal:?}"
        );
    }

    /// The SKIPPED field itself cannot be swapped into a row's place either:
    /// a table claiming `head` sits at the skipped field's declared index is
    /// refused on the carrier, not merely on the name, so both halves of the
    /// per-row check are exercised.
    #[test]
    fn m_a_row_pointed_at_the_skipped_field_is_refused_on_its_carrier() {
        let mut f = x_ref(vec![assign(bare(0), Rvalue::Use(Operand::Copy(deref_field(1, 0))))]);
        f.body.locals[1].ty = Ty::Ref {
            mutable: false,
            inner: Box::new(cursor_ty_named(
                "k::Gap",
                vec![
                    ("head".to_string(), Ty::u32()),
                    ("body".to_string(), Ty::Float { width: 64 }),
                    ("tail".to_string(), Ty::u32()),
                ],
            )),
        };
        let mut table = FrozenSharedParams::new();
        table.insert(
            0,
            FrozenPointee {
                param_name: "self".into(),
                adt_name: "k::Gap".into(),
                rows: vec![FrozenRow {
                    field_index: 1,
                    field_name: "head".into(),
                    carrier: "u32".into(),
                }],
            },
        );
        let refusal = e6_param_view(&f, &table).unwrap_err();
        assert!(
            matches!(&refusal, ViewRefusal::FieldMismatch { field, .. } if field == "head"),
            "got {refusal:?}"
        );
    }
}
