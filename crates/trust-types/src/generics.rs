// trust-types/generics.rs: Generic instantiation and substitution model
//
// Models Rust's generic type parameters, arguments, and substitutions
// for verification of generic code. Provides type-level substitution
// that can be applied to types, formulas, and specifications.
//
// Part of #153
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Serialize};

use crate::formula::{Formula, Sort};
use crate::fx::FxHashMap;
use crate::model::{FnSig, SourceSpan, Ty};
use crate::traits::TraitBound;

// ---------------------------------------------------------------------------
// Generic parameters
// ---------------------------------------------------------------------------

/// A generic parameter declaration on a function, struct, or impl block.
///
/// Represents `<T: Clone, 'a, const N: usize>` as a list of parameters,
/// each with its kind (type, lifetime, or const) and optional bounds.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct GenericParam {
    /// Parameter name (e.g., "T", "'a", "N").
    pub name: String,
    /// What kind of generic parameter this is.
    pub kind: GenericParamKind,
    /// Source location of the parameter declaration.
    pub span: SourceSpan,
}

/// The kind of a generic parameter.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum GenericParamKind {
    /// A type parameter (e.g., `T`, `T: Clone + Debug`).
    Type {
        /// Trait bounds on this type parameter.
        bounds: Vec<TraitBound>,
        /// Default type, if any (e.g., `T = i32`).
        default: Option<Ty>,
    },
    /// A lifetime parameter (e.g., `'a`, `'a: 'b`).
    Lifetime {
        /// Lifetime bounds (names of lifetimes this must outlive).
        bounds: Vec<String>,
    },
    /// A const generic parameter (e.g., `const N: usize`).
    Const {
        /// The type of the const parameter.
        ty: Ty,
    },
}

impl GenericParam {
    /// Create a type parameter with no bounds or default.
    #[must_use]
    pub fn type_param(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            kind: GenericParamKind::Type { bounds: vec![], default: None },
            span: SourceSpan::default(),
        }
    }

    /// Create a type parameter with trait bounds.
    #[must_use]
    pub fn type_param_bounded(name: impl Into<String>, bounds: Vec<TraitBound>) -> Self {
        Self {
            name: name.into(),
            kind: GenericParamKind::Type { bounds, default: None },
            span: SourceSpan::default(),
        }
    }

    /// Create a lifetime parameter with no bounds.
    #[must_use]
    pub fn lifetime(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            kind: GenericParamKind::Lifetime { bounds: vec![] },
            span: SourceSpan::default(),
        }
    }

    /// Create a const generic parameter.
    #[must_use]
    pub fn const_param(name: impl Into<String>, ty: Ty) -> Self {
        Self {
            name: name.into(),
            kind: GenericParamKind::Const { ty },
            span: SourceSpan::default(),
        }
    }

    /// Whether this is a type parameter.
    #[must_use]
    pub fn is_type(&self) -> bool {
        matches!(self.kind, GenericParamKind::Type { .. })
    }

    /// Whether this is a lifetime parameter.
    #[must_use]
    pub fn is_lifetime(&self) -> bool {
        matches!(self.kind, GenericParamKind::Lifetime { .. })
    }

    /// Whether this is a const generic parameter.
    #[must_use]
    pub fn is_const(&self) -> bool {
        matches!(self.kind, GenericParamKind::Const { .. })
    }
}

// ---------------------------------------------------------------------------
// Generic arguments
// ---------------------------------------------------------------------------

/// A concrete argument supplied for a generic parameter.
///
/// Represents the concrete types/lifetimes/consts in `Vec<i32>` or
/// `HashMap<String, u64>`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum GenericArg {
    /// A concrete type argument (e.g., `i32` in `Vec<i32>`).
    Type(Ty),
    /// A lifetime argument (e.g., `'static`).
    Lifetime(String),
    /// A const argument (e.g., `32` in `[u8; 32]`).
    Const(i128),
}

impl GenericArg {
    /// Extract the type if this is a Type argument.
    #[must_use]
    pub fn as_type(&self) -> Option<&Ty> {
        match self {
            GenericArg::Type(ty) => Some(ty),
            _ => None,
        }
    }

    /// Extract the lifetime name if this is a Lifetime argument.
    #[must_use]
    pub fn as_lifetime(&self) -> Option<&str> {
        match self {
            GenericArg::Lifetime(name) => Some(name),
            _ => None,
        }
    }

    /// Extract the const value if this is a Const argument.
    #[must_use]
    pub fn as_const(&self) -> Option<i128> {
        match self {
            GenericArg::Const(val) => Some(*val),
            _ => None,
        }
    }
}

// ---------------------------------------------------------------------------
// Substitution
// ---------------------------------------------------------------------------

/// A substitution mapping generic parameter names to concrete arguments.
///
/// Used to monomorphize generic code: replace all occurrences of type
/// parameters with their concrete types, lifetime parameters with
/// concrete lifetimes, and const parameters with concrete values.
#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct Substitution {
    /// Mapping from parameter name to concrete argument.
    bindings: FxHashMap<String, GenericArg>,
}

impl Substitution {
    /// Create an empty substitution.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Create a substitution from a list of parameter-argument pairs.
    #[must_use]
    pub fn from_pairs(pairs: Vec<(String, GenericArg)>) -> Self {
        Self { bindings: pairs.into_iter().collect() }
    }

    /// Create a substitution from generic params and matching arguments.
    ///
    /// Returns None if the number of params and args don't match.
    #[must_use]
    pub fn from_params_and_args(params: &[GenericParam], args: &[GenericArg]) -> Option<Self> {
        if params.len() != args.len() {
            return None;
        }
        let bindings = params
            .iter()
            .zip(args.iter())
            .map(|(param, arg)| (param.name.clone(), arg.clone()))
            .collect();
        Some(Self { bindings })
    }

    /// Add a type binding to the substitution.
    pub fn bind_type(&mut self, name: impl Into<String>, ty: Ty) {
        self.bindings.insert(name.into(), GenericArg::Type(ty));
    }

    /// Add a lifetime binding to the substitution.
    pub fn bind_lifetime(&mut self, name: impl Into<String>, lifetime: impl Into<String>) {
        self.bindings.insert(name.into(), GenericArg::Lifetime(lifetime.into()));
    }

    /// Add a const binding to the substitution.
    pub fn bind_const(&mut self, name: impl Into<String>, value: i128) {
        self.bindings.insert(name.into(), GenericArg::Const(value));
    }

    /// Look up the argument for a parameter name.
    #[must_use]
    pub fn get(&self, name: &str) -> Option<&GenericArg> {
        self.bindings.get(name)
    }

    /// Look up the type binding for a parameter name.
    #[must_use]
    pub fn get_type(&self, name: &str) -> Option<&Ty> {
        self.bindings.get(name).and_then(GenericArg::as_type)
    }

    /// Number of bindings in this substitution.
    #[must_use]
    pub fn len(&self) -> usize {
        self.bindings.len()
    }

    /// Whether this substitution is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.bindings.is_empty()
    }

    /// Iterate over all bindings.
    pub fn iter(&self) -> impl Iterator<Item = (&String, &GenericArg)> {
        self.bindings.iter()
    }

    /// Compose two substitutions: apply `other` after `self`.
    ///
    /// For each binding in `self`, apply `other` to the argument.
    /// Then add any bindings from `other` not already in `self`.
    #[must_use]
    pub fn compose(&self, other: &Substitution) -> Substitution {
        let mut result = Substitution::new();

        // Apply `other` to each binding in `self`.
        for (name, arg) in &self.bindings {
            let substituted = match arg {
                GenericArg::Type(ty) => GenericArg::Type(other.apply_ty(ty)),
                other_arg => other_arg.clone(),
            };
            result.bindings.insert(name.clone(), substituted);
        }

        // Add bindings from `other` not already present.
        for (name, arg) in &other.bindings {
            result.bindings.entry(name.clone()).or_insert_with(|| arg.clone());
        }

        result
    }
}

// ---------------------------------------------------------------------------
// Substitution application
// ---------------------------------------------------------------------------

impl Substitution {
    /// Apply this substitution to a type.
    ///
    /// Replaces type parameters (represented as single-character Adt names
    /// with no fields) with their concrete types from the substitution.
    /// Recursively substitutes through composite types.
    #[must_use]
    pub fn apply_ty(&self, ty: &Ty) -> Ty {
        match ty {
            // Check if this Adt is actually a type parameter.
            Ty::Adt { name, fields, variants, .. } if fields.is_empty() && variants.is_empty() => {
                if let Some(GenericArg::Type(concrete)) = self.bindings.get(name) {
                    concrete.clone()
                } else {
                    ty.clone()
                }
            }
            // Recursively substitute through composite types — both the
            // struct/union `fields` view and (Trust P4) each enum variant's
            // own field list.
            Ty::Adt { name, fields, variants, disc_index_safe, faithful_enum_repr, layout, enum_layout: _, adt_kind } => Ty::Adt {
                name: name.clone(),
                fields: fields
                    .iter()
                    .map(|(fname, fty)| (fname.clone(), self.apply_ty(fty)))
                    .collect(),
                variants: variants
                    .iter()
                    .map(|v| crate::model::VariantDef {
                        name: v.name.clone(),
                        discriminant: v.discriminant,
                        fields: v
                            .fields
                            .iter()
                            .map(|(fname, fty)| (fname.clone(), self.apply_ty(fty)))
                            .collect(),
                    })
                    .collect(),
                // Trust: enum-disc-full-native — substitution preserves layout
                // shape (it only rewrites field types), so the niche-safety
                // classification carries through unchanged.
                disc_index_safe: *disc_index_safe,
                // Trust (B3-1): the faithful-lane marker + repr hint likewise
                // survive substitution untouched (they classify the DEF, not
                // the field types).
                faithful_enum_repr: *faithful_enum_repr,
                // Trust (B3-4 T3): substitution rewrites field TYPES only; the
                // concrete layout was computed for the pre-substitution concrete
                // type and stays valid (a generic Adt never carries Some).
                layout: layout.clone(), enum_layout: None,
                // Trust: W19 — substitution rewrites field TYPES only; the ADT
                // kind (struct/union/enum) is a property of the DEF, unchanged.
                adt_kind: *adt_kind,
            },
            Ty::Ref { mutable, inner } => {
                Ty::Ref { mutable: *mutable, inner: Box::new(self.apply_ty(inner)) }
            }
            Ty::Slice { elem } => Ty::Slice { elem: Box::new(self.apply_ty(elem)) },
            Ty::Array { elem, len } => Ty::Array { elem: Box::new(self.apply_ty(elem)), len: *len },
            // Trust: piece #7a — substitute the element type but PRESERVE the
            // const-param length identity. Type-substitution does not rewrite a
            // const-generic length param, so `len_sym` carries through unchanged.
            Ty::SymArray { elem, len_sym } => {
                Ty::SymArray { elem: Box::new(self.apply_ty(elem)), len_sym: len_sym.clone() }
            }
            Ty::Tuple(elems) => Ty::Tuple(elems.iter().map(|t| self.apply_ty(t)).collect()),
            Ty::RawPtr { mutable, pointee } => {
                Ty::RawPtr { mutable: *mutable, pointee: Box::new(self.apply_ty(pointee)) }
            }
            // Trust: #828 — recursively substitute through new function-like and composite types.
            Ty::Closure { name, upvars, call } => Ty::Closure {
                name: name.clone(),
                upvars: upvars.iter().map(|t| self.apply_ty(t)).collect(),
                call: call.as_ref().map(|c| {
                    Box::new(crate::ClosureCallSig {
                        kind: c.kind,
                        params: c.params.iter().map(|t| self.apply_ty(t)).collect(),
                        ret: c.ret.as_ref().map(|t| self.apply_ty(t)),
                    })
                }),
            },
            Ty::FnDef { name, sig } => Ty::FnDef {
                name: name.clone(),
                sig: Box::new(FnSig {
                    params: sig.params.iter().map(|t| self.apply_ty(t)).collect(),
                    ret: Box::new(self.apply_ty(&sig.ret)),
                }),
            },
            Ty::FnPtr { sig } => Ty::FnPtr {
                sig: Box::new(FnSig {
                    params: sig.params.iter().map(|t| self.apply_ty(t)).collect(),
                    ret: Box::new(self.apply_ty(&sig.ret)),
                }),
            },
            Ty::Dynamic { .. } => ty.clone(),
            // v25 B1 faithful scalar spellings: parameter-free leaves.
            Ty::PtrSizedInt { .. } | Ty::Char => ty.clone(),
            Ty::Coroutine { name, upvars } => Ty::Coroutine {
                name: name.clone(),
                upvars: upvars.iter().map(|t| self.apply_ty(t)).collect(),
            },
            // Lever A — recursively substitute through each datatype variant's own
            // field list. A by-name reference (empty variants) substitutes to
            // itself (no fields to descend into). SOUNDNESS: pure structural
            // descent, mirroring the `Ty::Adt` arm; it introduces no facts.
            Ty::Datatype { name, variants } => Ty::Datatype {
                name: name.clone(),
                variants: variants
                    .iter()
                    .map(|(ctor, fields)| {
                        (
                            ctor.clone(),
                            fields
                                .iter()
                                .map(|(fname, fty)| (fname.clone(), self.apply_ty(fty)))
                                .collect(),
                        )
                    })
                    .collect(),
            },
            // Primitive types pass through unchanged.
            Ty::Bool
            | Ty::Int { .. }
            | Ty::Float { .. }
            | Ty::Bv(_)
            | Ty::Unit
            | Ty::Never
            | Ty::Str
            | Ty::Unsupported { .. } => ty.clone(),
        }
    }

    /// Apply this substitution to a formula.
    ///
    /// Replaces variables whose names match type parameter bindings
    /// with appropriately typed fresh variables. Updates sorts when
    /// a type parameter is resolved to a concrete type.
    #[must_use]
    pub fn apply_formula(&self, formula: &Formula) -> Formula {
        match formula {
            Formula::Var(name, sort) => {
                // Check if the variable name matches a type param and update sort.
                let new_sort = self.apply_sort(sort);
                Formula::Var(name.clone(), new_sort)
            }
            // SymVar preserves symbol, applies sort substitution.
            Formula::SymVar(sym, sort) => {
                let new_sort = self.apply_sort(sort);
                Formula::SymVar(*sym, new_sort)
            }
            Formula::Not(inner) => Formula::Not(Box::new(self.apply_formula(inner))),
            Formula::And(clauses) => {
                Formula::And(clauses.iter().map(|c| self.apply_formula(c)).collect())
            }
            Formula::Or(clauses) => {
                Formula::Or(clauses.iter().map(|c| self.apply_formula(c)).collect())
            }
            Formula::Implies(lhs, rhs) => Formula::Implies(
                Box::new(self.apply_formula(lhs)),
                Box::new(self.apply_formula(rhs)),
            ),
            Formula::Eq(lhs, rhs) => {
                Formula::Eq(Box::new(self.apply_formula(lhs)), Box::new(self.apply_formula(rhs)))
            }
            Formula::Lt(lhs, rhs) => {
                Formula::Lt(Box::new(self.apply_formula(lhs)), Box::new(self.apply_formula(rhs)))
            }
            Formula::Le(lhs, rhs) => {
                Formula::Le(Box::new(self.apply_formula(lhs)), Box::new(self.apply_formula(rhs)))
            }
            Formula::Gt(lhs, rhs) => {
                Formula::Gt(Box::new(self.apply_formula(lhs)), Box::new(self.apply_formula(rhs)))
            }
            Formula::Ge(lhs, rhs) => {
                Formula::Ge(Box::new(self.apply_formula(lhs)), Box::new(self.apply_formula(rhs)))
            }
            Formula::Add(lhs, rhs) => {
                Formula::Add(Box::new(self.apply_formula(lhs)), Box::new(self.apply_formula(rhs)))
            }
            Formula::Sub(lhs, rhs) => {
                Formula::Sub(Box::new(self.apply_formula(lhs)), Box::new(self.apply_formula(rhs)))
            }
            Formula::Mul(lhs, rhs) => {
                Formula::Mul(Box::new(self.apply_formula(lhs)), Box::new(self.apply_formula(rhs)))
            }
            Formula::Div(lhs, rhs) => {
                Formula::Div(Box::new(self.apply_formula(lhs)), Box::new(self.apply_formula(rhs)))
            }
            Formula::Rem(lhs, rhs) => {
                Formula::Rem(Box::new(self.apply_formula(lhs)), Box::new(self.apply_formula(rhs)))
            }
            Formula::Neg(inner) => Formula::Neg(Box::new(self.apply_formula(inner))),
            Formula::Ite(cond, then_f, else_f) => Formula::Ite(
                Box::new(self.apply_formula(cond)),
                Box::new(self.apply_formula(then_f)),
                Box::new(self.apply_formula(else_f)),
            ),
            Formula::Forall(vars, body) => {
                let new_vars =
                    vars.iter().map(|(name, sort)| (*name, self.apply_sort(sort))).collect();
                Formula::Forall(new_vars, Box::new(self.apply_formula(body)))
            }
            Formula::Exists(vars, body) => {
                let new_vars =
                    vars.iter().map(|(name, sort)| (*name, self.apply_sort(sort))).collect();
                Formula::Exists(new_vars, Box::new(self.apply_formula(body)))
            }
            Formula::Select(arr, idx) => Formula::Select(
                Box::new(self.apply_formula(arr)),
                Box::new(self.apply_formula(idx)),
            ),
            Formula::Store(arr, idx, val) => Formula::Store(
                Box::new(self.apply_formula(arr)),
                Box::new(self.apply_formula(idx)),
                Box::new(self.apply_formula(val)),
            ),
            // Uninterpreted predicate: apply substitution to each argument term.
            Formula::Pred(name, args) => {
                Formula::Pred(*name, args.iter().map(|a| self.apply_formula(a)).collect())
            }
            Formula::BvAdd(lhs, rhs, width) => Formula::BvAdd(
                Box::new(self.apply_formula(lhs)),
                Box::new(self.apply_formula(rhs)),
                *width,
            ),
            Formula::BvSub(lhs, rhs, width) => Formula::BvSub(
                Box::new(self.apply_formula(lhs)),
                Box::new(self.apply_formula(rhs)),
                *width,
            ),
            Formula::BvMul(lhs, rhs, width) => Formula::BvMul(
                Box::new(self.apply_formula(lhs)),
                Box::new(self.apply_formula(rhs)),
                *width,
            ),
            Formula::BvUDiv(lhs, rhs, width) => Formula::BvUDiv(
                Box::new(self.apply_formula(lhs)),
                Box::new(self.apply_formula(rhs)),
                *width,
            ),
            Formula::BvSDiv(lhs, rhs, width) => Formula::BvSDiv(
                Box::new(self.apply_formula(lhs)),
                Box::new(self.apply_formula(rhs)),
                *width,
            ),
            Formula::BvURem(lhs, rhs, width) => Formula::BvURem(
                Box::new(self.apply_formula(lhs)),
                Box::new(self.apply_formula(rhs)),
                *width,
            ),
            Formula::BvSRem(lhs, rhs, width) => Formula::BvSRem(
                Box::new(self.apply_formula(lhs)),
                Box::new(self.apply_formula(rhs)),
                *width,
            ),
            Formula::BvAnd(lhs, rhs, width) => Formula::BvAnd(
                Box::new(self.apply_formula(lhs)),
                Box::new(self.apply_formula(rhs)),
                *width,
            ),
            Formula::BvOr(lhs, rhs, width) => Formula::BvOr(
                Box::new(self.apply_formula(lhs)),
                Box::new(self.apply_formula(rhs)),
                *width,
            ),
            Formula::BvXor(lhs, rhs, width) => Formula::BvXor(
                Box::new(self.apply_formula(lhs)),
                Box::new(self.apply_formula(rhs)),
                *width,
            ),
            Formula::BvNot(inner, width) => {
                Formula::BvNot(Box::new(self.apply_formula(inner)), *width)
            }
            Formula::BvShl(lhs, rhs, width) => Formula::BvShl(
                Box::new(self.apply_formula(lhs)),
                Box::new(self.apply_formula(rhs)),
                *width,
            ),
            Formula::BvLShr(lhs, rhs, width) => Formula::BvLShr(
                Box::new(self.apply_formula(lhs)),
                Box::new(self.apply_formula(rhs)),
                *width,
            ),
            Formula::BvAShr(lhs, rhs, width) => Formula::BvAShr(
                Box::new(self.apply_formula(lhs)),
                Box::new(self.apply_formula(rhs)),
                *width,
            ),
            Formula::BvULt(lhs, rhs, width) => Formula::BvULt(
                Box::new(self.apply_formula(lhs)),
                Box::new(self.apply_formula(rhs)),
                *width,
            ),
            Formula::BvULe(lhs, rhs, width) => Formula::BvULe(
                Box::new(self.apply_formula(lhs)),
                Box::new(self.apply_formula(rhs)),
                *width,
            ),
            Formula::BvSLt(lhs, rhs, width) => Formula::BvSLt(
                Box::new(self.apply_formula(lhs)),
                Box::new(self.apply_formula(rhs)),
                *width,
            ),
            Formula::BvSLe(lhs, rhs, width) => Formula::BvSLe(
                Box::new(self.apply_formula(lhs)),
                Box::new(self.apply_formula(rhs)),
                *width,
            ),
            // BvBinary/BvCompare unified variants not yet in Formula
            Formula::BvToInt(inner, width, is_signed) => {
                Formula::BvToInt(Box::new(self.apply_formula(inner)), *width, *is_signed)
            }
            Formula::IntToBv(inner, width) => {
                Formula::IntToBv(Box::new(self.apply_formula(inner)), *width)
            }
            Formula::BvExtract { inner, high, low } => Formula::BvExtract {
                inner: Box::new(self.apply_formula(inner)),
                high: *high,
                low: *low,
            },
            Formula::BvConcat(lhs, rhs) => Formula::BvConcat(
                Box::new(self.apply_formula(lhs)),
                Box::new(self.apply_formula(rhs)),
            ),
            Formula::BvZeroExt(inner, width) => {
                Formula::BvZeroExt(Box::new(self.apply_formula(inner)), *width)
            }
            Formula::BvSignExt(inner, width) => {
                Formula::BvSignExt(Box::new(self.apply_formula(inner)), *width)
            }
            Formula::Bool(_) | Formula::Int(_) | Formula::UInt(_) | Formula::BitVec { .. } => {
                formula.clone()
            }
            // `Formula` is #[non_exhaustive] (defined in trust-ir-contract).
            // Leave any future variant structurally unchanged — a conservative
            // no-op substitution, never a wrong one.
            _ => formula.clone(),
        }
    }

    /// Apply this substitution to a sort.
    ///
    /// When a sort is `Int` (the fallback for type parameters), check
    /// if we can resolve it to a more specific sort based on the type
    /// bindings. Array sorts are recursively substituted.
    #[must_use]
    pub fn apply_sort(&self, sort: &Sort) -> Sort {
        match sort {
            Sort::Array(key, val) => {
                Sort::Array(Box::new(self.apply_sort(key)), Box::new(self.apply_sort(val)))
            }
            // Primitive sorts pass through.
            _ => sort.clone(),
        }
    }
}

// ---------------------------------------------------------------------------
// Generic signature
// ---------------------------------------------------------------------------

/// A complete generic signature for a function or type.
///
/// Combines the parameter declarations with where clauses. Used to
/// validate that concrete arguments satisfy all bounds before
/// monomorphization.
#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct GenericSignature {
    /// The generic parameters.
    pub params: Vec<GenericParam>,
    /// Additional where-clause bounds beyond those on the params.
    pub where_clauses: Vec<crate::trait_resolution::WhereClause>,
}

impl GenericSignature {
    /// Create an empty (non-generic) signature.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Number of type parameters.
    #[must_use]
    pub fn type_param_count(&self) -> usize {
        self.params.iter().filter(|p| p.is_type()).count()
    }

    /// Number of lifetime parameters.
    #[must_use]
    pub fn lifetime_param_count(&self) -> usize {
        self.params.iter().filter(|p| p.is_lifetime()).count()
    }

    /// Number of const parameters.
    #[must_use]
    pub fn const_param_count(&self) -> usize {
        self.params.iter().filter(|p| p.is_const()).count()
    }

    /// Whether this signature has any generic parameters.
    #[must_use]
    pub fn is_generic(&self) -> bool {
        !self.params.is_empty()
    }

    /// Get all type parameter names.
    #[must_use]
    pub fn type_param_names(&self) -> Vec<&str> {
        self.params.iter().filter(|p| p.is_type()).map(|p| p.name.as_str()).collect()
    }

    /// Collect all trait bounds from both params and where clauses.
    #[must_use]
    pub fn all_bounds(&self) -> Vec<(&str, &TraitBound)> {
        let mut bounds = Vec::new();

        // Bounds from type parameter declarations.
        for param in &self.params {
            if let GenericParamKind::Type { bounds: param_bounds, .. } = &param.kind {
                for bound in param_bounds {
                    bounds.push((param.name.as_str(), bound));
                }
            }
        }

        // Bounds from where clauses.
        for clause in &self.where_clauses {
            for bound in &clause.bounds {
                bounds.push((clause.type_param.as_str(), bound));
            }
        }

        bounds
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::model::Ty;
    use crate::trait_resolution::WhereClause;

    // --- GenericParam tests ---

    #[test]
    fn test_generic_param_type() {
        let param = GenericParam::type_param("T");
        assert_eq!(param.name, "T");
        assert!(param.is_type());
        assert!(!param.is_lifetime());
        assert!(!param.is_const());
    }

    #[test]
    fn test_generic_param_type_bounded() {
        let bounds = vec![TraitBound {
            trait_name: "Clone".to_string(),
            type_params: vec![],
            associated_types: vec![],
        }];
        let param = GenericParam::type_param_bounded("T", bounds.clone());
        assert!(param.is_type());
        if let GenericParamKind::Type { bounds: b, default } = &param.kind {
            assert_eq!(b.len(), 1);
            assert_eq!(b[0].trait_name, "Clone");
            assert!(default.is_none());
        } else {
            panic!("expected Type kind");
        }
    }

    #[test]
    fn test_generic_param_lifetime() {
        let param = GenericParam::lifetime("'a");
        assert_eq!(param.name, "'a");
        assert!(param.is_lifetime());
        assert!(!param.is_type());
    }

    #[test]
    fn test_generic_param_const() {
        let param = GenericParam::const_param("N", Ty::usize());
        assert_eq!(param.name, "N");
        assert!(param.is_const());
        assert!(!param.is_type());
        if let GenericParamKind::Const { ty } = &param.kind {
            assert_eq!(ty, &Ty::usize());
        } else {
            panic!("expected Const kind");
        }
    }

    // --- GenericArg tests ---

    #[test]
    fn test_generic_arg_type() {
        let arg = GenericArg::Type(Ty::i32());
        assert_eq!(arg.as_type(), Some(&Ty::i32()));
        assert!(arg.as_lifetime().is_none());
        assert!(arg.as_const().is_none());
    }

    #[test]
    fn test_generic_arg_lifetime() {
        let arg = GenericArg::Lifetime("'static".to_string());
        assert_eq!(arg.as_lifetime(), Some("'static"));
        assert!(arg.as_type().is_none());
    }

    #[test]
    fn test_generic_arg_const() {
        let arg = GenericArg::Const(42);
        assert_eq!(arg.as_const(), Some(42));
        assert!(arg.as_type().is_none());
    }

    // --- Substitution construction tests ---

    #[test]
    fn test_substitution_empty() {
        let subst = Substitution::new();
        assert!(subst.is_empty());
        assert_eq!(subst.len(), 0);
    }

    #[test]
    fn test_substitution_bind_type() {
        let mut subst = Substitution::new();
        subst.bind_type("T", Ty::i32());
        assert_eq!(subst.len(), 1);
        assert_eq!(subst.get_type("T"), Some(&Ty::i32()));
        assert!(subst.get_type("U").is_none());
    }

    #[test]
    fn test_substitution_bind_lifetime() {
        let mut subst = Substitution::new();
        subst.bind_lifetime("'a", "'static");
        assert_eq!(subst.len(), 1);
        assert_eq!(subst.get("'a"), Some(&GenericArg::Lifetime("'static".to_string())));
    }

    #[test]
    fn test_substitution_bind_const() {
        let mut subst = Substitution::new();
        subst.bind_const("N", 64);
        assert_eq!(subst.len(), 1);
        assert_eq!(subst.get("N"), Some(&GenericArg::Const(64)));
    }

    #[test]
    fn test_substitution_from_pairs() {
        let subst = Substitution::from_pairs(vec![
            ("T".to_string(), GenericArg::Type(Ty::i32())),
            ("U".to_string(), GenericArg::Type(Ty::Bool)),
        ]);
        assert_eq!(subst.len(), 2);
        assert_eq!(subst.get_type("T"), Some(&Ty::i32()));
        assert_eq!(subst.get_type("U"), Some(&Ty::Bool));
    }

    #[test]
    fn test_substitution_from_params_and_args() {
        let params = vec![GenericParam::type_param("T"), GenericParam::type_param("U")];
        let args = vec![GenericArg::Type(Ty::i32()), GenericArg::Type(Ty::Bool)];
        let subst = Substitution::from_params_and_args(&params, &args);
        assert!(subst.is_some());
        let subst = subst.unwrap();
        assert_eq!(subst.get_type("T"), Some(&Ty::i32()));
        assert_eq!(subst.get_type("U"), Some(&Ty::Bool));
    }

    #[test]
    fn test_substitution_from_params_and_args_mismatch() {
        let params = vec![GenericParam::type_param("T")];
        let args = vec![GenericArg::Type(Ty::i32()), GenericArg::Type(Ty::Bool)];
        assert!(Substitution::from_params_and_args(&params, &args).is_none());
    }

    // --- Type substitution tests ---

    #[test]
    fn test_apply_ty_type_parameter() {
        let mut subst = Substitution::new();
        subst.bind_type("T", Ty::i32());

        // A bare type parameter is Adt { name: "T", fields: [] }.
        let param_ty = Ty::Adt { adt_kind: None, layout: None,  variants: Vec::new(), name: "T".to_string(), fields: vec![],
            disc_index_safe: false,  faithful_enum_repr: None, enum_layout: None, };
        let result = subst.apply_ty(&param_ty);
        assert_eq!(result, Ty::i32());
    }

    #[test]
    fn test_apply_ty_unbound_parameter() {
        let subst = Substitution::new();
        let param_ty = Ty::Adt { adt_kind: None, layout: None,  variants: Vec::new(), name: "T".to_string(), fields: vec![],
            disc_index_safe: false,  faithful_enum_repr: None, enum_layout: None, };
        // Unbound parameter stays as-is.
        let result = subst.apply_ty(&param_ty);
        assert_eq!(result, param_ty);
    }

    #[test]
    fn test_apply_ty_primitive_passthrough() {
        let mut subst = Substitution::new();
        subst.bind_type("T", Ty::i32());

        assert_eq!(subst.apply_ty(&Ty::Bool), Ty::Bool);
        assert_eq!(subst.apply_ty(&Ty::Unit), Ty::Unit);
        assert_eq!(subst.apply_ty(&Ty::Never), Ty::Never);
        assert_eq!(subst.apply_ty(&Ty::i32()), Ty::i32());
    }

    #[test]
    fn test_apply_ty_ref() {
        let mut subst = Substitution::new();
        subst.bind_type("T", Ty::i32());

        let ref_ty = Ty::Ref {
            mutable: false,
            inner: Box::new(Ty::Adt { adt_kind: None, layout: None,  variants: Vec::new(), name: "T".to_string(), fields: vec![],
                disc_index_safe: false,  faithful_enum_repr: None, enum_layout: None, }),
        };
        let result = subst.apply_ty(&ref_ty);
        assert_eq!(result, Ty::Ref { mutable: false, inner: Box::new(Ty::i32()) });
    }

    #[test]
    fn test_apply_ty_slice() {
        let mut subst = Substitution::new();
        subst.bind_type("T", Ty::u32());

        let slice_ty =
            Ty::Slice { elem: Box::new(Ty::Adt { adt_kind: None, layout: None,  variants: Vec::new(), name: "T".to_string(), fields: vec![],
                disc_index_safe: false,  faithful_enum_repr: None, enum_layout: None, }) };
        let result = subst.apply_ty(&slice_ty);
        assert_eq!(result, Ty::Slice { elem: Box::new(Ty::u32()) });
    }

    #[test]
    fn test_apply_ty_array() {
        let mut subst = Substitution::new();
        subst.bind_type("T", Ty::Bool);

        let array_ty = Ty::Array {
            elem: Box::new(Ty::Adt { adt_kind: None, layout: None,  variants: Vec::new(), name: "T".to_string(), fields: vec![],
                disc_index_safe: false,  faithful_enum_repr: None, enum_layout: None, }),
            len: 10,
        };
        let result = subst.apply_ty(&array_ty);
        assert_eq!(result, Ty::Array { elem: Box::new(Ty::Bool), len: 10 });
    }

    #[test]
    fn test_apply_ty_tuple() {
        let mut subst = Substitution::new();
        subst.bind_type("T", Ty::i32());
        subst.bind_type("U", Ty::Bool);

        let tuple_ty = Ty::Tuple(vec![
            Ty::Adt { adt_kind: None, layout: None,  variants: Vec::new(), name: "T".to_string(), fields: vec![],
                disc_index_safe: false,  faithful_enum_repr: None, enum_layout: None, },
            Ty::Adt { adt_kind: None, layout: None,  variants: Vec::new(), name: "U".to_string(), fields: vec![],
                disc_index_safe: false,  faithful_enum_repr: None, enum_layout: None, },
        ]);
        let result = subst.apply_ty(&tuple_ty);
        assert_eq!(result, Ty::Tuple(vec![Ty::i32(), Ty::Bool]));
    }

    #[test]
    fn test_apply_ty_adt_with_fields() {
        let mut subst = Substitution::new();
        subst.bind_type("T", Ty::i32());

        let adt_ty = Ty::Adt { adt_kind: None, layout: None,  variants: Vec::new(),
            name: "MyStruct".to_string(),
            fields: vec![("value".to_string(), Ty::Adt { adt_kind: None, layout: None,  variants: Vec::new(), name: "T".to_string(), fields: vec![],
                disc_index_safe: false,  faithful_enum_repr: None, enum_layout: None, })],
            disc_index_safe: false,
         faithful_enum_repr: None, enum_layout: None, };
        let result = subst.apply_ty(&adt_ty);
        assert_eq!(
            result,
            Ty::Adt { adt_kind: None, layout: None,  variants: Vec::new(),
                name: "MyStruct".to_string(),
                fields: vec![("value".to_string(), Ty::i32())],
                disc_index_safe: false,
             faithful_enum_repr: None, enum_layout: None, }
        );
    }

    #[test]
    fn test_apply_ty_nested() {
        // Vec<Option<T>> where T = i32
        let mut subst = Substitution::new();
        subst.bind_type("T", Ty::i32());

        let inner = Ty::Adt { adt_kind: None, layout: None,  variants: Vec::new(),
            name: "Option".to_string(),
            fields: vec![("value".to_string(), Ty::Adt { adt_kind: None, layout: None,  variants: Vec::new(), name: "T".to_string(), fields: vec![],
                disc_index_safe: false,  faithful_enum_repr: None, enum_layout: None, })],
            disc_index_safe: false,
         faithful_enum_repr: None, enum_layout: None, };
        let outer = Ty::Adt { adt_kind: None, layout: None,  variants: Vec::new(), name: "Vec".to_string(), fields: vec![("elem".to_string(), inner)],
            disc_index_safe: false,  faithful_enum_repr: None, enum_layout: None, };

        let result = subst.apply_ty(&outer);
        if let Ty::Adt { name, fields, .. } = &result {
            assert_eq!(name, "Vec");
            if let Ty::Adt { fields: inner_fields, .. } = &fields[0].1 {
                assert_eq!(inner_fields[0].1, Ty::i32());
            } else {
                panic!("expected inner Adt");
            }
        } else {
            panic!("expected Adt");
        }
    }

    // --- Formula substitution tests ---

    #[test]
    fn test_apply_formula_var() {
        let subst = Substitution::new();
        let var = Formula::Var("x".to_string(), Sort::Int);
        let result = subst.apply_formula(&var);
        assert_eq!(result, var);
    }

    #[test]
    fn test_apply_formula_binary() {
        let subst = Substitution::new();
        let formula = Formula::Add(
            Box::new(Formula::Var("a".to_string(), Sort::Int)),
            Box::new(Formula::Var("b".to_string(), Sort::Int)),
        );
        let result = subst.apply_formula(&formula);
        assert_eq!(result, formula);
    }

    #[test]
    fn test_apply_formula_quantifier() {
        let subst = Substitution::new();
        let formula = Formula::Forall(
            vec![("x".into(), Sort::Int)],
            Box::new(Formula::Gt(
                Box::new(Formula::Var("x".to_string(), Sort::Int)),
                Box::new(Formula::Int(0)),
            )),
        );
        let result = subst.apply_formula(&formula);
        assert_eq!(result, formula);
    }

    #[test]
    fn test_apply_formula_sort_substitution() {
        let subst = Substitution::new();
        let formula =
            Formula::Var("x".to_string(), Sort::Array(Box::new(Sort::Int), Box::new(Sort::Bool)));
        let result = subst.apply_formula(&formula);
        assert_eq!(result, formula);
    }

    #[test]
    fn test_apply_formula_nested_logic() {
        let subst = Substitution::new();
        let formula = Formula::Implies(
            Box::new(Formula::And(vec![
                Formula::Bool(true),
                Formula::Var("p".to_string(), Sort::Bool),
            ])),
            Box::new(Formula::Or(vec![
                Formula::Bool(false),
                Formula::Var("q".to_string(), Sort::Bool),
            ])),
        );
        let result = subst.apply_formula(&formula);
        assert_eq!(result, formula);
    }

    #[test]
    fn test_apply_formula_ite() {
        let subst = Substitution::new();
        let formula = Formula::Ite(
            Box::new(Formula::Bool(true)),
            Box::new(Formula::Int(1)),
            Box::new(Formula::Int(0)),
        );
        let result = subst.apply_formula(&formula);
        assert_eq!(result, formula);
    }

    #[test]
    fn test_apply_formula_store_select() {
        let subst = Substitution::new();
        let arr =
            Formula::Var("arr".to_string(), Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int)));
        let formula = Formula::Select(
            Box::new(Formula::Store(
                Box::new(arr),
                Box::new(Formula::Int(0)),
                Box::new(Formula::Int(42)),
            )),
            Box::new(Formula::Int(0)),
        );
        let result = subst.apply_formula(&formula);
        assert_eq!(result, formula);
    }

    // --- Composition tests ---

    #[test]
    fn test_substitution_compose_basic() {
        let mut s1 = Substitution::new();
        s1.bind_type("T", Ty::Adt { adt_kind: None, layout: None,  variants: Vec::new(), name: "U".to_string(), fields: vec![],
            disc_index_safe: false,  faithful_enum_repr: None, enum_layout: None, });

        let mut s2 = Substitution::new();
        s2.bind_type("U", Ty::i32());

        let composed = s1.compose(&s2);
        // T -> U -> i32 after composition.
        assert_eq!(composed.get_type("T"), Some(&Ty::i32()));
        // U -> i32 carried from s2.
        assert_eq!(composed.get_type("U"), Some(&Ty::i32()));
    }

    #[test]
    fn test_substitution_compose_no_conflict() {
        let mut s1 = Substitution::new();
        s1.bind_type("T", Ty::i32());

        let mut s2 = Substitution::new();
        s2.bind_type("U", Ty::Bool);

        let composed = s1.compose(&s2);
        assert_eq!(composed.get_type("T"), Some(&Ty::i32()));
        assert_eq!(composed.get_type("U"), Some(&Ty::Bool));
    }

    #[test]
    fn test_substitution_compose_self_priority() {
        let mut s1 = Substitution::new();
        s1.bind_type("T", Ty::i32());

        let mut s2 = Substitution::new();
        s2.bind_type("T", Ty::Bool);

        let composed = s1.compose(&s2);
        // s1's binding for T takes priority (applied first).
        assert_eq!(composed.get_type("T"), Some(&Ty::i32()));
    }

    // --- GenericSignature tests ---

    #[test]
    fn test_generic_signature_empty() {
        let sig = GenericSignature::new();
        assert!(!sig.is_generic());
        assert_eq!(sig.type_param_count(), 0);
        assert_eq!(sig.lifetime_param_count(), 0);
        assert_eq!(sig.const_param_count(), 0);
    }

    #[test]
    fn test_generic_signature_mixed() {
        let sig = GenericSignature {
            params: vec![
                GenericParam::type_param("T"),
                GenericParam::type_param("U"),
                GenericParam::lifetime("'a"),
                GenericParam::const_param("N", Ty::usize()),
            ],
            where_clauses: vec![],
        };
        assert!(sig.is_generic());
        assert_eq!(sig.type_param_count(), 2);
        assert_eq!(sig.lifetime_param_count(), 1);
        assert_eq!(sig.const_param_count(), 1);
        assert_eq!(sig.type_param_names(), vec!["T", "U"]);
    }

    #[test]
    fn test_generic_signature_all_bounds() {
        let sig = GenericSignature {
            params: vec![GenericParam::type_param_bounded(
                "T",
                vec![TraitBound {
                    trait_name: "Clone".to_string(),
                    type_params: vec![],
                    associated_types: vec![],
                }],
            )],
            where_clauses: vec![WhereClause {
                type_param: "T".to_string(),
                bounds: vec![TraitBound {
                    trait_name: "Debug".to_string(),
                    type_params: vec![],
                    associated_types: vec![],
                }],
            }],
        };

        let bounds = sig.all_bounds();
        assert_eq!(bounds.len(), 2);
        assert_eq!(bounds[0].0, "T");
        assert_eq!(bounds[0].1.trait_name, "Clone");
        assert_eq!(bounds[1].0, "T");
        assert_eq!(bounds[1].1.trait_name, "Debug");
    }

    // --- Iterator tests ---

    #[test]
    fn test_substitution_iter() {
        let mut subst = Substitution::new();
        subst.bind_type("T", Ty::i32());
        subst.bind_type("U", Ty::Bool);

        let pairs: Vec<_> = subst.iter().collect();
        assert_eq!(pairs.len(), 2);
    }

    // --- Serialization tests ---

    #[test]
    fn test_generic_param_serialization_roundtrip() {
        let param = GenericParam::type_param_bounded(
            "T",
            vec![TraitBound {
                trait_name: "Clone".to_string(),
                type_params: vec![],
                associated_types: vec![],
            }],
        );
        let json = serde_json::to_string(&param).expect("serialize");
        let roundtrip: GenericParam = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(roundtrip.name, "T");
        assert!(roundtrip.is_type());
    }

    #[test]
    fn test_generic_arg_serialization_roundtrip() {
        let arg = GenericArg::Type(Ty::i32());
        let json = serde_json::to_string(&arg).expect("serialize");
        let roundtrip: GenericArg = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(roundtrip.as_type(), Some(&Ty::i32()));
    }

    #[test]
    fn test_substitution_serialization_roundtrip() {
        let mut subst = Substitution::new();
        subst.bind_type("T", Ty::i32());
        subst.bind_const("N", 32);

        let json = serde_json::to_string(&subst).expect("serialize");
        let roundtrip: Substitution = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(roundtrip.len(), 2);
        assert_eq!(roundtrip.get_type("T"), Some(&Ty::i32()));
        assert_eq!(roundtrip.get("N"), Some(&GenericArg::Const(32)));
    }

    #[test]
    fn test_generic_signature_serialization_roundtrip() {
        let sig = GenericSignature {
            params: vec![GenericParam::type_param("T"), GenericParam::lifetime("'a")],
            where_clauses: vec![WhereClause::single(
                "T",
                TraitBound {
                    trait_name: "Clone".to_string(),
                    type_params: vec![],
                    associated_types: vec![],
                },
            )],
        };

        let json = serde_json::to_string(&sig).expect("serialize");
        let roundtrip: GenericSignature = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(roundtrip.params.len(), 2);
        assert_eq!(roundtrip.where_clauses.len(), 1);
    }
}
