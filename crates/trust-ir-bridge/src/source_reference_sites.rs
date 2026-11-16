//! Trust (C1, 2026-11-06): the source reference sites the compiler's authorizable
//! lowering saw BEFORE type erasure, kept beside the module they were lowered into.
//!
//! trust-mc's source-consumption gate admits a load through an erased reference
//! parameter only with live `SourceReferenceFacts` (trust-mc DQ, 2026-10-30, "Keep
//! initialized reference facts separate from pointer transport"): `ValidBorrow`
//! alone establishes no initializedness, and the final module cannot tell `&u32`
//! from `&MaybeUninit<u32>` (both are a `Ptr` loaded as `U32`). This module
//! records the two kinds of claim the compiler path may make while the source type
//! is still visible, and nothing else:
//!
//! * a PARAMETER site: an argument local whose SOURCE type is `&T`/`&mut T` with
//!   `T` literally `bool` or a fixed-width integer, or (2026-11-07) a finite
//!   product of them (a tuple or a local `struct` whose field tree is all
//!   `bool`/integers, see [`source_reference_to_claimable_pointee`]), in a
//!   function the compiler attested borrow-provenance-clean;
//! * a LOAD site: a `Projection::Deref` load through such a reference that the
//!   lowering stamped `ValidBorrow`; `reconcile` keeps it only when its pointer
//!   is a reconciled parameter claim of the same function and pointee;
//! * a reference VALUE site (2026-11-07): the `FreshSymbolicHavoc`-stamped
//!   `Undef(Ptr)` the lowering emits for the promoted SHARED borrow of a
//!   fieldless (zero-sized) struct the extractor recovered from a valtree
//!   (`ConstValue::StructScalarFieldsRef` with no fields: `&UnitStruct`) or
//!   (2026-11-10, EMPTY-CLOSURE-REF-VALUE-1) of an upvar-free closure
//!   (`ConstValue::EmptyClosureRef`: `apply(&|x| x / 2, 7)`), see
//!   [`promoted_zst_shared_borrow`]. The claim is only that the erased pointer
//!   BITS are an initialized value, never which address or what the pointee
//!   holds (trust-mc `SourceReferenceValueFact`): a MIR constant of type `&T`
//!   passed rustc's const validation, so it is a non-null aligned reference, and
//!   valtree construction refuses statics, `UnsafeCell` and raw pointers. The
//!   carrier is held to the shape trust-mc's contract names (a promoted borrow of
//!   a stateless ZST: the empty closure itself, or a fieldless struct): a non-ZST pointee
//!   (`&Newtype(N)`, `&Enum::Variant`) gains nothing from a pointee-free fact
//!   (the callee's parameter requirement asks for the pointee) and is not
//!   claimed. `ConstValue::OpaqueConst` is NOT claimed: the extractor also uses
//!   it for runtime pointer values it does not model.
//!
//! The claim is semantic TCB (`docs/TCB.md`, "Source reference facts"): a genuine
//! safe reference to `bool`/an integer points to an initialized value (Rust's
//! validity rule for references), and the compiler's clean set says the function
//! fabricates no reference. A finite product's certificate is the walk of its
//! pre-erasure source type over the full logical field tree in this session
//! (2026-11-07): a safe reference to a struct/tuple of initialized scalars
//! points to a value whose every field is initialized. Excluded on purpose:
//! unions, enums, unstamped/synthetic ADTs, every `core`/`std`/`alloc` ADT
//! (`UnsafeCell`, `Cell`, `MaybeUninit`, `ManuallyDrop`, ...), ZST pointees,
//! raw pointers, unclean
//! functions, and every plain/public/test path (where `borrow_provenance_clean`
//! defaults to `true` and proves nothing). `char` and `isize`/`usize` are refused
//! only where the extractor keeps their identity (`Ty::Char`/`Ty::PtrSizedInt`,
//! the faithful-scalar lane). On the default extraction lane they arrive already
//! as `Ty::Int` (`char` as an unsigned 32-bit integer, `usize`/`isize` at the
//! target width) and are claimed as initialized integers of that width: a valid
//! `char` or `usize` is such an integer, so the claim is weaker than the truth
//! and implies no range (no `char` scalar-value bound is claimed).
//!
//! A table is plain data with no authority. It is constructible only inside this
//! crate, is neither `Clone` nor serializable, and grants nothing until
//! [`LoweredSourceReferenceSites::reconcile`] has matched every claim against the
//! FINAL module and the compiler's single issuer has bound the survivors to the
//! live bundle and its `SourceGenerationAuthority`. Reconciliation WITHDRAWS
//! (never repairs) any claim whose function, value, site, pointer, type or
//! `ValidBorrow` stamp no longer matches.

use trust_ir::node::InstrNode;
use trust_ir::proof::ProofAnnotation;
use trust_ir::ty::Ty;
use trust_ir::value::{BlockId, FuncId, ValueId};
use trust_ir::{Inst, Module};
use trust_types::fx::{FxHashMap, FxHashSet};

/// The source reference sites of ONE lowering call, keyed by the `FuncId` that
/// call assigned (`FuncId == index` into its input list).
#[derive(Debug, Default, PartialEq)]
pub struct LoweredSourceReferenceSites {
    functions: Vec<LoweredFunctionSourceReferences>,
}

#[derive(Debug, PartialEq)]
pub(crate) struct LoweredFunctionSourceReferences {
    pub(crate) function: FuncId,
    pub(crate) def_path: String,
    /// The module function's name after link-symbol disambiguation; a final
    /// function of another name at this id withdraws every claim.
    pub(crate) link_name: String,
    pub(crate) parameters: Vec<SourceReferenceParameterSite>,
    pub(crate) loads: Vec<SourceReferenceLoadSite>,
    pub(crate) values: Vec<SourceReferenceValueSite>,
}

#[derive(Debug, PartialEq)]
pub(crate) struct SourceReferenceParameterSite {
    pub(crate) value: ValueId,
    pub(crate) pointee: Ty,
}

#[derive(Debug, PartialEq)]
pub(crate) struct SourceReferenceLoadSite {
    pub(crate) result: ValueId,
    pub(crate) pointer: ValueId,
    pub(crate) pointee: Ty,
}

/// The result of the stamped `Undef(Ptr)` a valtree-recovered shared-reference
/// constant lowered to (see the module doc).
#[derive(Debug, PartialEq)]
pub(crate) struct SourceReferenceValueSite {
    pub(crate) result: ValueId,
}

/// A parameter claim matched against the final module: `params[parameter_index]`
/// of `function`'s entry block is `(value, Ty::Ptr)`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReconciledSourceReferenceParameter {
    pub function: FuncId,
    pub parameter_index: u32,
    pub value: ValueId,
    pub pointee: Ty,
}

/// A load claim matched against the final module: `block.body[instruction_index]`
/// is the unique node defining `result`, a non-volatile `Load` of `pointee`
/// through `pointer` with `align: None` that still carries `ValidBorrow`, and
/// `pointer` is a reconciled parameter claim of `function` with the same pointee.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReconciledSourceReferenceLoad {
    pub function: FuncId,
    pub block: BlockId,
    pub instruction_index: u32,
    pub result: ValueId,
    pub pointer: ValueId,
    pub pointee: Ty,
}

/// A reference VALUE claim matched against the final module:
/// `block.body[instruction_index]` is the unique node defining `result`, a
/// single-result `Undef { ty: Ptr }` stamped `FreshSymbolicHavoc`, and `result`
/// is no block parameter and no parameter or load claim.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReconciledSourceReferenceValue {
    pub function: FuncId,
    pub block: BlockId,
    pub instruction_index: u32,
    pub result: ValueId,
}

/// What survived reconciliation, plus how many claims were withdrawn (diagnostic
/// only; a count grants nothing).
#[derive(Debug, Default, PartialEq, Eq)]
pub struct ReconciledSourceReferenceSites {
    pub parameters: Vec<ReconciledSourceReferenceParameter>,
    pub loads: Vec<ReconciledSourceReferenceLoad>,
    pub values: Vec<ReconciledSourceReferenceValue>,
    pub withdrawn: usize,
}

impl ReconciledSourceReferenceSites {
    pub fn is_empty(&self) -> bool {
        self.parameters.is_empty() && self.loads.is_empty() && self.values.is_empty()
    }
}

/// Depth and node bounds of the pointee walks, equal to trust-mc's
/// `supported_pointee` bounds so a claim the bridge makes is never one the
/// constructor's shape check runs out of budget on.
const MAX_POINTEE_DEPTH: usize = 64;
const MAX_POINTEE_NODES: usize = 16_384;

/// Is `ty` a pointee this table may claim, in `module`'s type tables: `Bool` or
/// a FIXED-width integer, or (2026-11-07) a finite product of them: a `Tuple` or
/// a `Struct` of `module` whose fields are all claimable, `Unit` allowed as a
/// field. `Char`, `Isize`/`Usize`, enums, pointers, arrays, floats and
/// everything else are refused. This mirrors trust-mc's `supported_pointee`
/// (minus pointer-width integers), with the same bounds.
pub(crate) fn claimable_pointee(module: &Module, ty: &Ty) -> bool {
    fn walk(module: &Module, ty: &Ty, depth: usize, work: &mut usize) -> bool {
        if depth == 0 || *work == 0 {
            return false;
        }
        *work -= 1;
        match ty {
            Ty::Bool
            | Ty::Unit
            | Ty::I8
            | Ty::I16
            | Ty::I32
            | Ty::I64
            | Ty::I128
            | Ty::U8
            | Ty::U16
            | Ty::U32
            | Ty::U64
            | Ty::U128 => true,
            Ty::Tuple(fields) => fields.iter().all(|field| walk(module, field, depth - 1, work)),
            Ty::Struct(id) => module.structs.get(id.as_usize()).is_some_and(|definition| {
                definition.id == *id
                    && definition
                        .fields
                        .iter()
                        .all(|field| walk(module, &field.ty, depth - 1, work))
            }),
            _ => false,
        }
    }
    let mut work = MAX_POINTEE_NODES;
    !matches!(ty, Ty::Unit) && walk(module, ty, MAX_POINTEE_DEPTH, &mut work)
}

/// Is the constant operand `cv`, lowered at `expected_ty`, the promoted SHARED
/// borrow of a stateless ZST (a value site, see the module doc)? Both sides must
/// agree, for one of two carriers:
///
/// * the valtree-recovered `StructScalarFieldsRef` carries no field (rustc's own
///   `AdtDef` is a struct with zero fields, so the pointee is a ZST), and the
///   pre-erasure expected type is `&S` with `S` the same extractor-stamped
///   `AdtKind::Struct` with no fields and no variants;
/// * (2026-11-10, EMPTY-CLOSURE-REF-VALUE-1) the extractor's promoted
///   `EmptyClosureRef`, and the pre-erasure expected type is `&C` with `C` the
///   same-named `Ty::Closure` with no upvars (a closure without captures is a
///   ZST). This is the carrier trust-mc's value-fact contract names.
///
/// `UnitVariantRef`, `OpaqueConst` (at any type, a closure's included), every
/// non-empty field or upvar list, `&mut`, unstamped ADTs and a name disagreement
/// refuse.
pub(crate) fn promoted_zst_shared_borrow(
    cv: &trust_types::ConstValue,
    expected_ty: &trust_types::Ty,
) -> bool {
    let trust_types::Ty::Ref { mutable: false, inner } = expected_ty else { return false };
    if let trust_types::ConstValue::EmptyClosureRef { closure, .. } = cv {
        return matches!(
            inner.as_ref(),
            trust_types::Ty::Closure { name, upvars, .. } if upvars.is_empty() && name == closure
        );
    }
    let trust_types::ConstValue::StructScalarFieldsRef { adt_name, fields, .. } = cv else {
        return false;
    };
    let trust_types::Ty::Adt { name, fields: ty_fields, variants, adt_kind, .. } = inner.as_ref()
    else {
        return false;
    };
    fields.is_empty()
        && ty_fields.is_empty()
        && variants.is_empty()
        && matches!(adt_kind, Some(trust_types::AdtKind::Struct))
        && name == adt_name
}

/// Is the SOURCE type `&T`/`&mut T` with `T` an initialized-by-validity pointee:
/// `bool`, a legacy-lane integer (`Ty::Int`), or (2026-11-07) a finite product
/// of them with at least one such scalar leaf? Checked on the pre-erasure type,
/// where an erased wrapper (`MaybeUninit<u32>`, `Cell<u32>`, `ManuallyDrop`) is
/// still a `Ty::Adt` even where it maps to `U32` below. A product is:
///
/// * a tuple whose elements are all claimable (`()` only inside a product);
/// * a `Ty::Adt` the extractor stamped `AdtKind::Struct` (never a union, an enum,
///   or an unstamped synthetic ADT), with no variants, defined outside
///   `core`/`std`/`alloc` (so no `UnsafeCell`, `Cell`, `MaybeUninit`,
///   `ManuallyDrop`, `PhantomData` or other library wrapper; interior
///   mutability exists only through `core`'s `UnsafeCell`, which any field
///   reaching it is refused for), whose fields are all claimable.
///
/// A ZST pointee (`&()`, `&UnitStruct`) has no leaf to claim and is refused.
/// `PtrSizedInt` and `Char` are refused; on the default extraction lane
/// `char`/`usize`/`isize` already ARE `Ty::Int` here, and are claimed only as
/// initialized integers (see the module doc).
pub(crate) fn source_reference_to_claimable_pointee(source: &trust_types::Ty) -> bool {
    fn library_type(name: &str) -> bool {
        let root = name.trim_start_matches(['<', '&', ' ']).split("::").next().unwrap_or_default();
        matches!(root, "core" | "std" | "alloc")
    }
    fn walk(ty: &trust_types::Ty, depth: usize, work: &mut usize, leaves: &mut usize) -> bool {
        if depth == 0 || *work == 0 {
            return false;
        }
        *work -= 1;
        match ty {
            trust_types::Ty::Bool | trust_types::Ty::Int { .. } => {
                *leaves += 1;
                true
            }
            trust_types::Ty::Tuple(fields) => {
                fields.iter().all(|field| walk(field, depth - 1, work, leaves))
            }
            trust_types::Ty::Adt { name, fields, variants, adt_kind, .. } => {
                matches!(adt_kind, Some(trust_types::AdtKind::Struct))
                    && variants.is_empty()
                    && !library_type(name)
                    && fields.iter().all(|(_, field)| walk(field, depth - 1, work, leaves))
            }
            _ => false,
        }
    }
    let trust_types::Ty::Ref { inner, .. } = source else { return false };
    let mut leaves = 0;
    let mut work = MAX_POINTEE_NODES;
    walk(inner, MAX_POINTEE_DEPTH, &mut work, &mut leaves) && leaves > 0
}

impl LoweredSourceReferenceSites {
    pub(crate) fn push_function(&mut self, function: LoweredFunctionSourceReferences) {
        self.functions.push(function);
    }

    /// Stamp each record with its function's final link name (after
    /// `disambiguate_function_link_symbols`). A record whose id names no module
    /// function keeps an empty name and is withdrawn by `reconcile`.
    pub(crate) fn bind_link_names(&mut self, module: &Module) {
        for record in &mut self.functions {
            record.link_name = module
                .functions
                .get(record.function.index() as usize)
                .filter(|function| function.id == record.function)
                .map(|function| function.name.clone())
                .unwrap_or_default();
        }
    }

    /// Withdraw every claim of the function at `index` (lowering order). Used
    /// when a later compiler analysis withholds that function's reference
    /// provenance (borrow-provenance conjunct 3, `strip_unattested_reach`).
    pub fn withdraw_function(&mut self, index: usize) {
        self.functions.retain(|record| record.function.index() as usize != index);
    }

    /// The def paths with at least one claim (diagnostic only).
    pub fn claimed_def_paths(&self) -> impl Iterator<Item = &str> {
        self.functions.iter().map(|record| record.def_path.as_str())
    }

    /// Number of claims before reconciliation (diagnostic only).
    pub fn claim_count(&self) -> usize {
        self.functions
            .iter()
            .map(|record| record.parameters.len() + record.loads.len() + record.values.len())
            .sum()
    }

    /// Match every claim against `module`, the FINAL module the bundle is built
    /// from, and keep only exact matches. Never repairs a claim.
    pub fn reconcile(&self, module: &Module) -> ReconciledSourceReferenceSites {
        #[derive(Clone, Copy)]
        enum ValueDefSite<'a> {
            Single(BlockId, u32, &'a InstrNode),
            Duplicate,
        }

        let mut out = ReconciledSourceReferenceSites::default();
        let mut seen_functions: FxHashSet<FuncId> =
            FxHashSet::with_capacity_and_hasher(self.functions.len(), Default::default());
        for record in &self.functions {
            let claims = record.parameters.len() + record.loads.len() + record.values.len();
            let function = module
                .functions
                .get(record.function.index() as usize)
                .filter(|function| function.id == record.function);
            let Some(function) = function.filter(|function| {
                !record.link_name.is_empty() && function.name == record.link_name
            }) else {
                out.withdrawn += claims;
                continue;
            };
            // Two records for one function cannot both be this lowering's.
            if !seen_functions.insert(record.function) {
                out.withdrawn += claims;
                continue;
            }
            if claims == 0 {
                continue;
            }
            let entry = function.blocks.iter().find(|block| block.id == function.entry);
            let mut parameter_pointees: FxHashMap<ValueId, &Ty> =
                FxHashMap::with_capacity_and_hasher(record.parameters.len(), Default::default());
            for parameter in &record.parameters {
                let position = entry.and_then(|entry| {
                    let mut matches = entry
                        .params
                        .iter()
                        .enumerate()
                        .filter(|(_, (value, _))| *value == parameter.value);
                    match (matches.next(), matches.next()) {
                        (Some((index, (_, Ty::Ptr))), None) => Some(index),
                        _ => None,
                    }
                });
                let Some(position) =
                    position.filter(|_| claimable_pointee(module, &parameter.pointee))
                else {
                    out.withdrawn += 1;
                    continue;
                };
                if parameter_pointees.insert(parameter.value, &parameter.pointee).is_some() {
                    out.withdrawn += 1;
                    continue;
                }
                out.parameters.push(ReconciledSourceReferenceParameter {
                    function: record.function,
                    parameter_index: position as u32,
                    value: parameter.value,
                    pointee: parameter.pointee.clone(),
                });
            }
            if record.loads.is_empty() && record.values.is_empty() {
                continue;
            }
            // Every defining node of each value, so an SSA duplicate (or a value
            // that is also a block parameter) withdraws without allocating per-value Vecs.
            let approx_defs: usize = function.blocks.iter().map(|b| b.body.len()).sum();
            let approx_params: usize = function.blocks.iter().map(|b| b.params.len()).sum();
            let mut definitions: FxHashMap<ValueId, ValueDefSite<'_>> =
                FxHashMap::with_capacity_and_hasher(approx_defs, Default::default());
            let mut block_parameters: FxHashSet<ValueId> =
                FxHashSet::with_capacity_and_hasher(approx_params, Default::default());
            for block in &function.blocks {
                for (index, node) in block.body.iter().enumerate() {
                    for result in &node.results {
                        definitions
                            .entry(*result)
                            .and_modify(|site| *site = ValueDefSite::Duplicate)
                            .or_insert(ValueDefSite::Single(block.id, index as u32, node));
                    }
                }
                block_parameters.extend(block.params.iter().map(|(value, _)| *value));
            }
            let mut seen_loads: FxHashSet<ValueId> =
                FxHashSet::with_capacity_and_hasher(record.loads.len(), Default::default());
            for load in &record.loads {
                let site = match definitions.get(&load.result) {
                    Some(&ValueDefSite::Single(block, index, node))
                        if !block_parameters.contains(&load.result) =>
                    {
                        Some((block, index, node))
                    }
                    _ => None,
                };
                let exact = site.filter(|(_, _, node)| {
                    node.results.as_slice() == [load.result]
                        && matches!(&node.inst, Inst::Load { ty, ptr, volatile: false, align: None }
                            if *ty == load.pointee && *ptr == load.pointer)
                        && node.proofs.contains(&ProofAnnotation::ValidBorrow)
                        && claimable_pointee(module, &load.pointee)
                });
                // A load is claimed only through a reconciled PARAMETER claim of
                // this function with the same pointee. A reference the body made
                // itself (a call result such as `MaybeUninit::assume_init_ref`, a
                // reborrow, a field) is valid only if an unsafe precondition held,
                // which is exactly what the solve must not be told.
                let agrees_with_parameter = parameter_pointees
                    .get(&load.pointer)
                    .is_some_and(|pointee| **pointee == load.pointee);
                match exact {
                    Some((block, instruction_index, _))
                        if agrees_with_parameter && seen_loads.insert(load.result) =>
                    {
                        out.loads.push(ReconciledSourceReferenceLoad {
                            function: record.function,
                            block,
                            instruction_index,
                            result: load.result,
                            pointer: load.pointer,
                            pointee: load.pointee.clone(),
                        });
                    }
                    _ => out.withdrawn += 1,
                }
            }
            let load_result_set: Option<FxHashSet<ValueId>> = (!record.values.is_empty()
                && record.loads.len() > 8)
                .then(|| record.loads.iter().map(|load| load.result).collect());
            let mut seen_values: FxHashSet<ValueId> =
                FxHashSet::with_capacity_and_hasher(record.values.len(), Default::default());
            for claim in &record.values {
                let site = match definitions.get(&claim.result) {
                    Some(&ValueDefSite::Single(block, index, node))
                        if !block_parameters.contains(&claim.result) =>
                    {
                        Some((block, index, node))
                    }
                    _ => None,
                };
                let exact = site.filter(|(_, _, node)| {
                    node.results.as_slice() == [claim.result]
                        && matches!(&node.inst, Inst::Undef { ty: Ty::Ptr })
                        && node.proofs.contains(&ProofAnnotation::FreshSymbolicHavoc)
                });
                // A value claim never overlaps a parameter or load claim.
                let overlaps_load = match &load_result_set {
                    Some(set) => set.contains(&claim.result),
                    None => record.loads.iter().any(|load| load.result == claim.result),
                };
                let distinct = !parameter_pointees.contains_key(&claim.result) && !overlaps_load;
                match exact {
                    Some((block, instruction_index, _))
                        if distinct && seen_values.insert(claim.result) =>
                    {
                        out.values.push(ReconciledSourceReferenceValue {
                            function: record.function,
                            block,
                            instruction_index,
                            result: claim.result,
                        });
                    }
                    _ => out.withdrawn += 1,
                }
            }
        }
        out.parameters.sort_by_key(|parameter| (parameter.function, parameter.parameter_index));
        out.loads.sort_by_key(|load| (load.function, load.result));
        out.values.sort_by_key(|value| (value.function, value.result));
        out
    }
}

#[cfg(test)]
mod tests;
