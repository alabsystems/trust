//! Per-function cached scans for `trust-source-contract` bundle construction.
//!
//! Precomputes function-invariant local/CFG properties once per
//! [`VerifiableFunction`] so functions with many VCs do not re-scan
//! `body.locals` and `body.blocks` on every obligation.

use std::collections::BTreeMap;
use std::hash::{Hash, Hasher};

use serde_json::{Value as JsonValue, json};
use trust_types::fx::{FxHashMap, FxHashSet, FxHasher};
use trust_types::{Formula, LocalDecl, Sort, Ty, VerifiableFunction};

use crate::{
    local_name, reject_unsupported_trust_vc_memory_statement,
    reject_unsupported_trust_vc_memory_terminator, reject_unsupported_trust_vc_memory_ty,
    trust_vc_sort_for_ty,
};

#[inline]
pub(crate) fn fx_hash_selected_formula(
    schema: &str,
    typed_payload: &str,
    selected_formula: &Formula,
) -> (usize, usize, u64) {
    let mut hasher = FxHasher::default();
    schema.hash(&mut hasher);
    typed_payload.hash(&mut hasher);
    selected_formula.hash(&mut hasher);
    (schema.len(), typed_payload.len(), hasher.finish())
}

fn parse_canonical_local_ident(s: &str) -> Option<usize> {
    let digits = s.strip_prefix('_')?;
    if digits.is_empty()
        || (digits.len() > 1 && digits.starts_with('0'))
        || !digits.bytes().all(|b| b.is_ascii_digit())
    {
        return None;
    }
    digits.parse::<usize>().ok()
}

fn is_narrow_unsigned_local_decl(local: &LocalDecl) -> bool {
    matches!(local.ty, Ty::Int { width, signed: false } if width <= 64)
}

/// Pre-indexed narrow-unsigned local lookup table for one [`VerifiableFunction`].
///
/// Matches [`crate::formula_vars_are_narrow_unsigned_locals`] exactly while
/// answering each variable query in `O(1)` instead of scanning `body.locals`.
pub(crate) struct NarrowUnsignedLocalIndex<'a> {
    locals: &'a [LocalDecl],
    is_dense: bool,
    has_underscore_name: bool,
    /// Maps each source local name `base` to `true` iff at least one local
    /// carries `Some(base)` with a narrow unsigned type AND no local carrying
    /// `Some(base)` has a non-narrow-unsigned type (review round 36 shadow
    /// rule). `Some(false)` means a wider/non-unsigned local shares `base`.
    name_narrow: FxHashMap<&'a str, bool>,
}

impl<'a> NarrowUnsignedLocalIndex<'a> {
    pub(crate) fn new(function: &'a VerifiableFunction) -> Self {
        let locals = &function.body.locals;
        let mut is_dense = true;
        let mut has_underscore_name = false;
        let mut name_narrow: FxHashMap<&'a str, bool> =
            FxHashMap::with_capacity_and_hasher(locals.len(), Default::default());
        for (pos, local) in locals.iter().enumerate() {
            if local.index != pos {
                is_dense = false;
            }
            if let Some(name) = local.name.as_deref() {
                if name.starts_with('_') {
                    has_underscore_name = true;
                }
                if is_narrow_unsigned_local_decl(local) {
                    name_narrow.entry(name).or_insert(true);
                } else {
                    name_narrow.insert(name, false);
                }
            }
        }
        Self { locals, is_dense, has_underscore_name, name_narrow }
    }

    #[inline]
    fn has_local_index(&self, idx: usize) -> bool {
        if self.is_dense {
            idx < self.locals.len()
        } else {
            self.locals.get(idx).is_some_and(|l| l.index == idx)
                || self.locals.iter().any(|l| l.index == idx)
        }
    }

    #[inline]
    fn is_narrow_by_idx(&self, idx: usize) -> bool {
        if self.is_dense {
            self.locals.get(idx).is_some_and(is_narrow_unsigned_local_decl)
        } else {
            self.locals.get(idx).is_some_and(|l| l.index == idx && is_narrow_unsigned_local_decl(l))
                || self.locals.iter().any(|l| l.index == idx && is_narrow_unsigned_local_decl(l))
        }
    }

    #[inline]
    fn is_narrow_and_not_wide_named(&self, base: &str) -> bool {
        let in_narrow_by_idx =
            parse_canonical_local_ident(base).is_some_and(|idx| self.is_narrow_by_idx(idx));
        if base.starts_with('_') && !self.has_underscore_name {
            return in_narrow_by_idx;
        }
        match self.name_narrow.get(base).copied() {
            Some(true) => true,
            Some(false) => false,
            None => in_narrow_by_idx,
        }
    }

    #[inline]
    fn is_slice_root(&self, root: &str) -> bool {
        if parse_canonical_local_ident(root).is_some_and(|idx| self.has_local_index(idx)) {
            return true;
        }
        if root.starts_with('_') && !self.has_underscore_name {
            return false;
        }
        self.name_narrow.contains_key(root)
    }

    #[inline]
    fn admits_var_name(&self, name: &str) -> bool {
        let base = name.split('#').next().unwrap_or(name);
        self.is_narrow_and_not_wide_named(base)
            || base.strip_suffix("__slice_len").is_some_and(|root| self.is_slice_root(root))
    }

    pub(crate) fn admits_formula(&self, formula: &Formula) -> bool {
        trust_types::all_formula_nodes(formula, &mut |node| match node {
            Formula::Var(_, Sort::Bool) | Formula::SymVar(_, Sort::Bool) => true,
            Formula::Var(name, _) => self.admits_var_name(name),
            Formula::SymVar(sym, _) => self.admits_var_name(sym.as_str()),
            _ => true,
        })
    }
}

pub(crate) struct ScannedMemoryLocal {
    pub(crate) index: usize,
    pub(crate) name: String,
    pub(crate) sort: Result<JsonValue, String>,
    pub(crate) borrow_kind: Option<&'static str>,
}

/// Cached per-function scan for `trust_vc_mir_memory_proof_unit_payload`.
///
/// Preserves the exact error-message precedence of
/// `reject_unsupported_trust_vc_memory_function` while scanning `locals`,
/// `return_ty`, and `blocks` at most once per function.
pub(crate) struct TrustVcMemoryFunctionScan {
    pub(crate) locals: Vec<ScannedMemoryLocal>,
    pub(crate) first_local_ty_error: Option<String>,
    pub(crate) post_locals_return_sort: Result<JsonValue, String>,
}

impl TrustVcMemoryFunctionScan {
    pub(crate) fn new(function: &VerifiableFunction) -> Self {
        let mut locals = Vec::with_capacity(function.body.locals.len());
        let mut first_local_ty_error = None;
        for local in &function.body.locals {
            if let Err(reason) = reject_unsupported_trust_vc_memory_ty(&local.ty) {
                first_local_ty_error = Some(format!("{reason} in local {}", local.index));
                break;
            }
            let borrow_kind = match &local.ty {
                Ty::Ref { mutable: true, .. } => Some("mutable"),
                Ty::Ref { mutable: false, .. } => Some("shared"),
                _ => None,
            };
            locals.push(ScannedMemoryLocal {
                index: local.index,
                name: local_name(local),
                sort: trust_vc_sort_for_ty(&local.ty),
                borrow_kind,
            });
        }

        let post_locals_return_sort = if first_local_ty_error.is_none() {
            Self::scan_return_and_blocks(function)
        } else {
            Err(String::new())
        };

        Self { locals, first_local_ty_error, post_locals_return_sort }
    }

    fn scan_return_and_blocks(function: &VerifiableFunction) -> Result<JsonValue, String> {
        reject_unsupported_trust_vc_memory_ty(&function.body.return_ty)
            .map_err(|reason| format!("{reason} in return type"))?;
        let return_sort = trust_vc_sort_for_ty(&function.body.return_ty)?;
        for block in &function.body.blocks {
            for stmt in &block.stmts {
                reject_unsupported_trust_vc_memory_statement(stmt, &function.body.locals)
                    .map_err(|reason| format!("{reason} in bb{}", block.id.0))?;
            }
            reject_unsupported_trust_vc_memory_terminator(&block.terminator, &function.body.locals)
                .map_err(|reason| format!("{reason} in bb{}", block.id.0))?;
        }
        Ok(return_sort)
    }

    pub(crate) fn validate_and_return_sort(
        &self,
        formula_variables: &BTreeMap<String, JsonValue>,
    ) -> Result<JsonValue, String> {
        for local in &self.locals {
            if local.index == 0 || formula_variables.contains_key(&local.name) {
                if let Err(err) = &local.sort {
                    return Err(err.clone());
                }
            }
        }
        if let Some(err) = &self.first_local_ty_error {
            return Err(err.clone());
        }
        self.post_locals_return_sort.as_ref().map_err(Clone::clone).cloned()
    }

    pub(crate) fn ownership_state(
        &self,
        formula_variables: &BTreeMap<String, JsonValue>,
    ) -> Result<JsonValue, String> {
        let mut places = Vec::with_capacity(self.locals.len());
        let mut borrows = Vec::new();

        for local in &self.locals {
            let sort = if let Some(sort) = formula_variables.get(&local.name) {
                sort.clone()
            } else {
                match &local.sort {
                    Ok(sort) => sort.clone(),
                    Err(_) => continue,
                }
            };
            if let Some(kind) = local.borrow_kind {
                borrows.push(json!({
                    "region": format!("r{}", local.index),
                    "place": local.name,
                    "kind": kind,
                }));
            }
            places.push(json!({
                "place": local.name,
                "sort": sort,
            }));
        }

        if places.is_empty() {
            return Err(
                "trust-vc MIR memory proof unit omitted because no typed MIR locals were available for ownership state"
                    .to_string(),
            );
        }

        let mut ownership = json!({
            "places": places,
        });
        if !borrows.is_empty() {
            if let Some(obj) = ownership.as_object_mut() {
                obj.insert("borrows".to_string(), JsonValue::Array(borrows));
            }
        }
        Ok(ownership)
    }
}

/// Fast path for [`crate::factor_shared_disjunct_conjuncts`] when the first
/// disjunct has `> 16` conjuncts: uses `FxHashSet<&Formula>` instead of
/// `O(|first| * |rest| * |disjunct|)` linear `.contains` scans.
pub(crate) fn factor_shared_disjuncts_fast(
    disjuncts: Vec<Formula>,
    conjuncts_of: fn(&Formula) -> &[Formula],
) -> Formula {
    let Some((first, rest)) = disjuncts.split_first() else {
        return Formula::Or(disjuncts);
    };
    if rest.is_empty() {
        return Formula::Or(disjuncts);
    }
    let first_conjuncts = conjuncts_of(first);
    let rest_sets: Vec<FxHashSet<&Formula>> = rest
        .iter()
        .map(|d| conjuncts_of(d).iter().collect::<FxHashSet<&Formula>>())
        .collect();
    let mut shared: Vec<&Formula> = Vec::new();
    let mut shared_set: FxHashSet<&Formula> = FxHashSet::default();
    for candidate in first_conjuncts {
        if !shared_set.contains(candidate) && rest_sets.iter().all(|set| set.contains(candidate)) {
            shared_set.insert(candidate);
            shared.push(candidate);
        }
    }
    if shared.is_empty() {
        return Formula::Or(disjuncts);
    }
    let mut residues = Vec::with_capacity(disjuncts.len());
    for disjunct in &disjuncts {
        let residue: Vec<Formula> = conjuncts_of(disjunct)
            .iter()
            .filter(|conjunct| !shared_set.contains(*conjunct))
            .cloned()
            .collect();
        match residue.len() {
            0 => return Formula::And(shared.into_iter().cloned().collect()),
            1 => residues.extend(residue),
            _ => residues.push(Formula::And(residue)),
        }
    }
    let mut factored: Vec<Formula> = shared.into_iter().cloned().collect();
    factored.push(Formula::Or(residues));
    Formula::And(factored)
}
