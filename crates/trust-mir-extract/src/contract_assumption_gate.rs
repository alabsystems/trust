//! Soundness gates for using `#[trust::requires]` predicates as *body
//! assumptions* (hypotheses conjoined onto the function's own safety VCs).
//!
//! A contract precondition is caller-proved, so assuming it inside the body is
//! assume-guarantee sound — but only if the assumed fact really speaks about
//! the function's *entry parameters*. Two live hazards gate-checked here:
//!
//! * **Shadow collision (P0, observed false-PROVE):** the VC variable namespace
//!   is debug names, and `build_debug_name_map` is last-write-wins. A body
//!   `let x = …;` shadowing a parameter `x` makes the predicate's `x > 0`
//!   constrain the *body* local in the formula — proving overflow obligations
//!   about an unconstrained value (probe `t_shadow`, 2026-06-09).
//! * **Vacuity:** an unsatisfiable predicate (`x > 10 && x < 5`) would admit
//!   any body under a false hypothesis. We require a concrete ground witness
//!   before assuming; a found witness is a model, so the check cannot
//!   false-positive.
//!
//! Gate failure NEVER rejects the function — it only drops the assumption
//! (assume nothing), which can only weaken PROVE toward FAIL/UNKNOWN. The
//! call-site Precondition VCs are generated from a separate re-parse and are
//! deliberately NOT gated: callers must prove the full declared predicate.

use trust_types::fx::{FxHashMap, FxHashSet};
use trust_types::{Formula, Rvalue, Statement, Terminator, Ty, VerifiableBody};

/// Why contract-derived preconditions were not assumed for body verification.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AssumeSkipReason {
    /// Predicate uses syntax outside the v1 integer/boolean fragment.
    UnsupportedSyntax,
    /// Predicate references a variable that is not a parameter debug name.
    NonParamVariable(String),
    /// A non-parameter local shares a debug name with a referenced parameter,
    /// so the formula-level fact would bind the wrong variable.
    ShadowedParamName(String),
    /// No concrete ground witness found — the predicate is (or may be)
    /// unsatisfiable; assuming it could vacuously verify the body.
    NoSatisfiableWitness,
}

impl AssumeSkipReason {
    pub fn describe(&self) -> String {
        match self {
            AssumeSkipReason::UnsupportedSyntax => {
                "predicate uses syntax outside the assumable integer fragment".to_string()
            }
            AssumeSkipReason::NonParamVariable(name) => {
                format!("predicate references `{name}`, which is not a parameter")
            }
            AssumeSkipReason::ShadowedParamName(name) => format!(
                "a body local shadows parameter `{name}`; the assumed fact would bind the wrong variable"
            ),
            AssumeSkipReason::NoSatisfiableWitness => {
                "no satisfiable witness found for the predicate; refusing a possibly-vacuous assumption"
            }
            .to_string(),
        }
    }
}

/// Gate contract-derived preconditions before they become body hypotheses.
///
/// `debug_name_locals` is the RAW debug-info name → locals multimap (every
/// `var_debug_info` entry, no last-write-wins collapse). The collapsed
/// per-local names on `body.locals` are NOT sufficient: optimized MIR
/// copy-propagates `let x = z;` so the shadow's debug entry lands on `z`'s own
/// param local — invisible to an index-based scan, observed still-false-proving
/// in build #32 validation.
///
/// On ANY gate failure, drops ALL contract-derived preconditions (collective
/// drop — partial assumption sets are harder to reason about) and returns the
/// reasons for diagnostics. Synthetic always-true facts (enum-discriminant
/// ranges) are appended by the caller AFTER this gate and are not affected.
pub fn gate_contract_preconditions(
    preconditions: &mut Vec<Formula>,
    body: &VerifiableBody,
    debug_name_locals: &FxHashMap<String, Vec<usize>>,
) -> Vec<AssumeSkipReason> {
    if preconditions.is_empty() {
        return Vec::new();
    }

    let param_names: FxHashSet<&str> = body
        .locals
        .iter()
        .filter(|local| local.index >= 1 && local.index <= body.arg_count)
        .filter_map(|local| local.name.as_deref())
        .collect();

    // Parameters that are SHARED references (`&T`, not `&mut T`). The pointee of
    // a `&T` is immutable for the parameter's lifetime, so a caller-proved entry
    // fact over `*a` (`#[requires(*a <= 100)]`) holds at every body read — assuming
    // it is assume-guarantee sound. A `&mut T` pointee CAN be mutated in the body,
    // which would stale the entry fact (a false-PROVE hazard), so those derefs are
    // NOT assumable. See `assumable_param_base`.
    let shared_ref_params: FxHashSet<&str> = body
        .locals
        .iter()
        .filter(|local| local.index >= 1 && local.index <= body.arg_count)
        .filter(|local| matches!(&local.ty, Ty::Ref { mutable: false, .. }))
        .filter_map(|local| local.name.as_deref())
        .collect();

    // Trust (piece #8 — length-relationship preconditions): the LENGTH symbols
    // admissible for THIS body's slice/array PARAMETERS. A precondition like
    // `n <= arr__slice_len` speaks about the length of a slice/array parameter
    // `arr`, which is an ENTRY fact the caller can render (σ-length rendering) and
    // discharge — exactly the caller-supplied-loop-bound family (`for i in 0..n {
    // arr[i] }`). The admitted solver spellings are:
    //   * `<param_debug_name>__slice_len` — a runtime `&[T]`/`&mut [T]`/`*mut [T]`
    //     slice parameter's canonical length var, and
    //   * `__trust_constparam_{index}_{name}` — a const-generic array parameter's
    //     length (`&[T; N]`, `[T; N]` with N a const param).
    // Exact source parsing lowers `arr.len()` to the projection leaf `arr_len`.
    // That leaf is NEVER admitted as an independent free variable: for one
    // unique, length-stable runtime-slice parameter only, `admissible_lengths`
    // rebinds it to canonical `arr__slice_len` before validation and witness
    // search. Thus the source contract, bounds VC, and modular σ summary all
    // consume one Formula term rather than relying on a free-variable coincidence.
    // Admitting a length symbol is sound ONLY when the parameter's length is
    // STABLE for the whole body (INV-1): a `&mut [T]` param that the body reslices
    // to a shorter view (`let arr = &mut arr[..1];`) would make `arr__slice_len`
    // denote the ORIGINAL length while the indexed slice is shorter — a false
    // PROVE. `slice_param_length_is_stable` rejects any reslice/reassign/`&mut`/
    // projected store of the param, so an unstable slice param drops its length
    // symbol from the whitelist (fail-closed: the assumption is dropped, never a
    // false PROVE). An immutable array/SymArray length has no mutation channel at
    // all (INV-3), so it is always admissible.
    let lengths = admissible_lengths(body, debug_name_locals);
    for formula in preconditions.iter_mut() {
        for (source, canonical) in &lengths.source_rebindings {
            if formula.free_variables().contains(source) {
                *formula = formula.rename_var(source, canonical);
            }
        }
    }
    let length_syms = lengths.canonical;

    let mut reasons = Vec::new();
    let mut referenced: FxHashSet<String> = FxHashSet::default();

    for formula in preconditions.iter() {
        if !in_assumable_fragment(formula) {
            reasons.push(AssumeSkipReason::UnsupportedSyntax);
            continue;
        }
        for var in formula.free_variables() {
            // Trust (piece #8): a whitelisted slice/array-parameter length symbol is
            // admissible and EXEMPT from the debug-name shadow/witness discipline —
            // it is not a debug name, so it cannot shadow a local or alias a param
            // local. Skip it before `assumable_param_base` (which would reject it as
            // a NonParamVariable). It is NOT added to `referenced`, so the shadow
            // loops below never see it.
            if length_syms.contains(var.as_str()) {
                continue;
            }
            // Normalize each free variable to the PARAMETER it is caller-bound to
            // (bare `a`, or a shared-ref deref `a*` → `a`); anything else is not
            // assumable. The shadow/witness checks below then operate on the base
            // parameter name, so a sound deref term binds the real parameter local.
            match assumable_param_base(&var, &param_names, &shared_ref_params) {
                Some(base) => {
                    referenced.insert(base.to_string());
                }
                None => {
                    // A raw debug name can still point at a parameter local even
                    // when the collapsed per-local name chose a different alias.
                    // Calling that shape merely "non-parameter" loses the more
                    // important fact: the formula namespace is ambiguous.  It is
                    // exactly the copy-propagated-shadow hazard this gate exists
                    // to reject.  Classify it as shadowing and keep it in the
                    // referenced set so the multimap checks below also diagnose
                    // every colliding alias on that local.
                    let raw_base = var.strip_suffix('*').unwrap_or(var.as_str());
                    // If `raw_base` is already the parameter's canonical name,
                    // rejection came from the term shape (for example `a*` on
                    // `a: &mut T`), not from a debug-name alias. Keep that as a
                    // non-parameter term; only the collapsed-name mismatch is
                    // evidence of the copy-propagated shadow hazard.
                    let aliases_param = !param_names.contains(raw_base)
                        && debug_name_locals.get(raw_base).is_some_and(|locals| {
                            locals.iter().any(|local| *local >= 1 && *local <= body.arg_count)
                        });
                    if aliases_param {
                        referenced.insert(raw_base.to_string());
                        reasons.push(AssumeSkipReason::ShadowedParamName(raw_base.to_string()));
                    } else {
                        reasons.push(AssumeSkipReason::NonParamVariable(var.clone()));
                    }
                }
            }
        }
    }

    // Shadow collision. The formula namespace is debug names, so an assumed
    // fact about name N is sound only when N denotes EXACTLY ONE local and
    // that local is a parameter. Two hazard shapes, both fatal:
    //  * a body local carries a referenced param's name (classic shadow);
    //  * copy-prop attached a shadow's debug entry to ANOTHER local (often a
    //    different param's), so N maps to several locals — or a param local
    //    carries several names. Multiplicity in the raw multimap catches both.
    for name in &referenced {
        match debug_name_locals.get(name.as_str()) {
            Some(locals) => {
                let mut distinct: Vec<usize> = locals.clone();
                distinct.sort_unstable();
                distinct.dedup();
                let is_unique_param =
                    distinct.len() == 1 && distinct[0] >= 1 && distinct[0] <= body.arg_count;
                if !is_unique_param {
                    reasons.push(AssumeSkipReason::ShadowedParamName(name.clone()));
                }
            }
            // Referenced but absent from debug info entirely: cannot bind it
            // to a parameter value.
            None => reasons.push(AssumeSkipReason::NonParamVariable(name.clone())),
        }
    }

    // A param local carrying MORE THAN ONE debug name (e.g. its own plus a
    // copy-propagated shadow's) makes any referenced name on it ambiguous.
    for (name, locals) in debug_name_locals {
        if referenced.contains(name) {
            continue;
        }
        for local in locals {
            if *local >= 1 && *local <= body.arg_count {
                // Another name aliases a param local; if any referenced name
                // also resolves to this local the binding is ambiguous.
                if debug_name_locals.iter().any(|(other, ls)| {
                    other != name && referenced.contains(other) && ls.contains(local)
                }) {
                    reasons.push(AssumeSkipReason::ShadowedParamName(name.clone()));
                }
            }
        }
    }

    if reasons.is_empty() && !has_ground_witness(preconditions, body, &length_syms) {
        reasons.push(AssumeSkipReason::NoSatisfiableWitness);
    }

    if !reasons.is_empty() {
        preconditions.clear();
    }
    reasons
}

/// The parameter a precondition free variable is caller-bound to, if any:
///   * a bare parameter name `a` → `a` (the parameter itself);
///   * a shared-reference-parameter deref `a*` → `a` (the `&T` pointee, which
///     `place_to_var_name` renders as the suffix `*`). The pointee of a `&T` is
///     immutable for the parameter's lifetime, so a caller-proved entry fact
///     over it holds at every body read — assume-guarantee sound;
///   * a LITERAL projection chain off a parameter head (see below).
///
/// A `&mut T` deref, a runtime index (`a[_i]`), a `*` anywhere but immediately
/// after the head, or a non-parameter name returns `None`, which drops the
/// whole assumption set (fail-closed — can only weaken PROVE toward
/// FAIL/UNKNOWN, never a false PROVE).
fn assumable_param_base<'a>(
    var: &'a str,
    param_names: &FxHashSet<&str>,
    shared_ref_params: &FxHashSet<&str>,
) -> Option<&'a str> {
    if let Some(base) = var.strip_suffix('*') {
        // A `<base>*` deref is assumable ONLY when `<base>` is a shared-ref param.
        return shared_ref_params.contains(base).then_some(base);
    }
    if param_names.contains(var) {
        return Some(var);
    }
    // Trust (float field-magnitude preconditions): a LITERAL projection chain off
    // a parameter is caller-bound and assumable when the projected value is stable
    // for the parameter's lifetime. The base parameter name is returned so the
    // shadow/witness discipline below runs on that parameter exactly as for a
    // bare scalar param (the full chained name never enters the referenced set).
    // Accepted shape — a small grammar, parsed segment by segment:
    //   <head> ['*'] ( '.' <digits> | '[' <digits> ']' )+
    //   * `<head>` is a plain identifier (no projection token). With the optional
    //     `'*'` it must be a SHARED-ref param: the `&T` pointee is immutable, so a
    //     caller-proved entry fact over any part of it holds at every body read —
    //     the same rationale (and soundness) as the `<p>*` whole-pointee case
    //     above; a `&mut` pointee is NOT admitted, matching the `<p>*` &mut
    //     rejection. Without the `'*'` it must be a BY-VALUE param: a body
    //     reassignment anywhere under the param is handled EXACTLY as for a bare
    //     scalar param — the versioned conjoin renames the written place, leaving
    //     the bare entry fact name-disjoint and inert (the S2c entry-read
    //     exemption), so an assumed chain fact can only ever bind the entry value.
    //   * `.<digits>` — a numeric tuple/struct field (`self.0.2`); `[<digits>]` —
    //     a LITERAL array index (`self.0[3]`). Any depth, in any order. A literal
    //     index selects one fixed element of the entry value, so the field
    //     rationale carries over unchanged; a RUNTIME index (`[_i]`, `[x]`) is
    //     not entry-determined and is rejected.
    // Anything else — a `*` not immediately after the head, empty/non-numeric
    // segments, unclosed brackets — falls through to `None` (fail-closed). The
    // `place_to_var_name` twin renders fields as `.i` and a leading deref as `*`;
    // literal-index body renders are canonicalized to `[k]` by the float-contract
    // matcher before lookup, so an admitted var binds its body place byte-for-byte.
    let head_end = var.find(['.', '*', '['])?;
    let (head, mut rest) = var.split_at(head_end);
    if !is_plain_base_ident(head) {
        return None;
    }
    // Optional deref marker, ONLY directly after the head. (`rest` cannot be empty
    // afterwards: a trailing-`*` var was consumed by the strip_suffix arm above.)
    let starred = match rest.strip_prefix('*') {
        Some(stripped) => {
            rest = stripped;
            true
        }
        None => false,
    };
    if rest.is_empty() {
        return None;
    }
    while !rest.is_empty() {
        if let Some(after_dot) = rest.strip_prefix('.') {
            let digits = leading_ascii_digits_len(after_dot);
            if digits == 0 {
                return None;
            }
            rest = &after_dot[digits..];
        } else if let Some(after_bracket) = rest.strip_prefix('[') {
            let digits = leading_ascii_digits_len(after_bracket);
            if digits == 0 {
                return None;
            }
            match after_bracket[digits..].strip_prefix(']') {
                Some(tail) => rest = tail,
                None => return None,
            }
        } else {
            return None;
        }
    }
    if starred {
        shared_ref_params.contains(head).then_some(head)
    } else {
        param_names.contains(head).then_some(head)
    }
}

/// A bare base identifier carrying no projection token (`.`, `*`, `[`) — the head
/// of a field-projection var name (`self` in `self.0` / `self*.2`).
fn is_plain_base_ident(s: &str) -> bool {
    !s.is_empty() && !s.contains(['.', '*', '['])
}

/// Length of the leading run of ASCII digits — the numeric tuple/struct field
/// index or literal array index that opens a projection segment (0 = malformed).
fn leading_ascii_digits_len(s: &str) -> usize {
    s.bytes().take_while(|b| b.is_ascii_digit()).count()
}

struct AdmissibleLengths {
    /// Canonical solver leaves that may occur in an assumed precondition.
    canonical: FxHashSet<String>,
    /// Exact source projection leaf -> canonical solver leaf. The source leaf
    /// is rewritten and is never admitted as an independent Formula variable.
    source_rebindings: Vec<(String, String)>,
}

/// Trust (piece #8 — length-relationship preconditions): canonical length
/// symbols that a precondition may reference, drawn from THIS body's slice/array
/// PARAMETERS, plus exact source-to-canonical rebindings:
///   * `<param_debug_name>__slice_len` — a runtime slice parameter's canonical
///     length var for `&[T]` / `&mut [T]` / `*mut [T]` / bare `[T]` params.
///     Exact source `<param>.len()` first lowers to `<param>_len`; this function
///     authorizes rewriting that leaf to the canonical spelling. Both operations
///     are allowed ONLY when the parameter is LENGTH-STABLE for the whole body
///     (INV-1): the param must not be resliced/reassigned/`&mut`-reborrowed/
///     projected-stored, because such a reslice would make `<p>__slice_len`
///     denote the ORIGINAL length while the indexed view is shorter (a false
///     PROVE).
///   * `__trust_constparam_{index}_{name}` — a const-generic array parameter's
///     length (`&[T; N]` / `[T; N]` with N a const param). The length is the
///     immutable TYPE parameter — no mutation channel changes it (INV-3) — so it
///     is admitted unconditionally for any array/SymArray param.
///
/// A `<name>_len`/`<name>__slice_len` whose base is not a unique, stable slice
/// parameter is neither rebound nor admitted. A `__trust_constparam_*` symbol is
/// admitted only when some array/SymArray parameter actually produces it. The
/// whitelist is derived from the extracted body plus the raw debug-name
/// multimap, so optimized-MIR aliases cannot bypass the same shadow discipline
/// applied to scalar parameters.
fn admissible_lengths(
    body: &VerifiableBody,
    debug_name_locals: &FxHashMap<String, Vec<usize>>,
) -> AdmissibleLengths {
    // Count collapsed debug-name multiplicity across ALL extracted locals. A
    // runtime length symbol is admissible ONLY when `name` denotes exactly one
    // local — the parameter. If a body local shadows the param name (e.g. INV-1's
    // reslice binds a new `arr`), the failed VC could key on the shorter shadow
    // while σ renders the caller's original length — a false PROVE.
    let mut name_count: FxHashMap<&str, usize> = FxHashMap::default();
    for local in &body.locals {
        if let Some(name) = local.name.as_deref() {
            *name_count.entry(name).or_default() += 1;
        }
    }

    let mut canonical = FxHashSet::default();
    let mut source_rebindings = Vec::new();
    for local in &body.locals {
        if local.index < 1 || local.index > body.arg_count {
            continue;
        }
        // `__trust_constparam_{index}_{name}` is derived from the immutable
        // parameter type, not its debug name, so shadowing cannot change which
        // length it denotes (INV-3).
        if let Some(len_sym) = symarray_len_sym_of(&local.ty) {
            canonical.insert(trust_types::const_param_symbol(len_sym.index, &len_sym.name));
        }
        let Some(name) = local.name.as_deref() else { continue };
        // Require both the collapsed extracted model and the raw MIR debug map
        // to identify exactly this parameter. The raw map catches copy-prop
        // aliases that one last-write-wins local name cannot represent.
        let raw_is_unique_parameter = debug_name_locals.get(name).is_some_and(|locals| {
            let mut distinct = locals.clone();
            distinct.sort_unstable();
            distinct.dedup();
            distinct == [local.index]
        });
        if name_count.get(name).copied().unwrap_or(0) != 1 || !raw_is_unique_parameter {
            continue;
        }
        // Runtime source `<p>.len()` becomes `<p>_len`, then is rebound to the
        // one canonical `<p>__slice_len` term (INV-1: length-stable).
        if ty_is_runtime_slice_param(&local.ty) && slice_param_length_is_stable(body, local.index) {
            let canonical_name = format!("{name}__slice_len");
            canonical.insert(canonical_name.clone());
            source_rebindings.push((format!("{name}_len"), canonical_name));
        }
    }
    AdmissibleLengths { canonical, source_rebindings }
}

/// True for a parameter type whose length is a RUNTIME fat-pointer/slice length,
/// producing a `<name>__slice_len` var: `&[T]`, `&mut [T]`, `*const [T]`,
/// `*mut [T]`, or a bare `[T]` (unsized-place) parameter. Concrete `[T; N]` /
/// `&[T; N]` arrays are NOT here — their length is a compile-time constant, not
/// a `__slice_len` var — so they never contribute a runtime length symbol.
fn ty_is_runtime_slice_param(ty: &Ty) -> bool {
    match ty {
        Ty::Slice { .. } => true,
        Ty::Ref { inner, .. } => matches!(inner.as_ref(), Ty::Slice { .. }),
        Ty::RawPtr { pointee, .. } => matches!(pointee.as_ref(), Ty::Slice { .. }),
        _ => false,
    }
}

/// The const-generic array LENGTH symbol of a parameter type, if it is a
/// `SymArray` (`[T; N]`) or a reference/raw-pointer to one (`&[T; N]`). Mirrors
/// `slice_len_formula`'s SymArray arms. Concrete `Ty::Array` (statically-known
/// `u64` length) has no const-param symbol and returns None.
fn symarray_len_sym_of(ty: &Ty) -> Option<&trust_types::ConstLen> {
    match ty {
        Ty::SymArray { len_sym, .. } => Some(len_sym),
        Ty::Ref { inner, .. } => match inner.as_ref() {
            Ty::SymArray { len_sym, .. } => Some(len_sym),
            _ => None,
        },
        Ty::RawPtr { pointee, .. } => match pointee.as_ref() {
            Ty::SymArray { len_sym, .. } => Some(len_sym),
            _ => None,
        },
        _ => None,
    }
}

/// Trust (piece #8, INV-1): whether the slice PARAMETER `p` (local index) keeps
/// the SAME fat-pointer LENGTH view for the whole body, so `<p>__slice_len`
/// denotes the caller-supplied length at every read. This is the crate-local twin
/// of `trust_vcgen::place_source_is_stable` (the two crates share no dependency),
/// specialized to LENGTH stability — which is about the fat-pointer VALUE, not the
/// pointee ELEMENTS:
///   * NO whole-local reassign of the parameter (`arr = &arr[..k];`) — that
///     installs a shorter/different fat pointer, changing the length view.
///   * NO `&mut`/`&raw mut` reborrow of the WHOLE parameter fat pointer (the
///     channel a reslice-of-arr flows through: `let s = &mut arr; *s = &mut …`).
///   * NO projected store / borrow that overwrites the fat pointer VALUE itself
///     (a projection that does NOT go through `Deref` — e.g. a hypothetical
///     fat-pointer field write; exotic, rejected conservatively), and no
///     SetDiscriminant / Deinit / call-destination store of the whole local.
///
/// An ELEMENT write `arr[i] = v` (which lowers to a store through a DEREF-leading
/// projection `(*arr)[i]`) writes the POINTEE and leaves the fat pointer — and
/// thus the length — unchanged, so it is ALLOWED. Likewise a shared reborrow
/// `&arr[..]` cannot reslice-through-a-shared-ref-to-shorten the caller's view
/// (it borrows immutably), so it is allowed. Any length-changing channel returns
/// false → the length symbol is dropped from the whitelist → the precondition is
/// dropped (fail-closed). INTENTIONALLY conservative: it can only cost
/// completeness, never soundness.
fn slice_param_length_is_stable(body: &VerifiableBody, param_local: usize) -> bool {
    // A projection whose FIRST element is `Deref` addresses THROUGH the parameter's
    // fat pointer into the pointee — it can never overwrite the fat pointer value
    // itself (hence never change the length). Any other projected/whole store to
    // the parameter local writes the fat pointer.
    let writes_fat_pointer = |place: &trust_types::Place| -> bool {
        place.local == param_local
            && !matches!(place.projections.first(), Some(trust_types::Projection::Deref))
    };
    for block in &body.blocks {
        // A call-dest store to the parameter's fat pointer reseats it. A store
        // THROUGH a deref (`f(&mut (*arr)[i])`-style dest) writes the pointee and is
        // fine; a whole/non-deref dest overwrites the fat pointer.
        // (edition 2021 — no let-chains; nest the borrow check.)
        if let Terminator::Call { dest, .. } = &block.terminator {
            if writes_fat_pointer(dest) {
                return false;
            }
        }
        for stmt in &block.stmts {
            match stmt {
                Statement::Assign { place, rvalue, .. } => {
                    if writes_fat_pointer(place) {
                        return false;
                    }
                    // A mutable (re)borrow of the WHOLE parameter fat pointer
                    // (`&mut arr` / `&raw mut arr`, no leading deref) is the channel a
                    // reslice-of-arr flows through. A mutable borrow of the POINTEE or
                    // an ELEMENT (`&mut (*arr)[i]`, deref-leading) cannot change the
                    // fat pointer's length, so it is allowed.
                    if let Rvalue::Ref { mutable: true, place: borrowed }
                    | Rvalue::AddressOf(true, borrowed) = rvalue
                    {
                        if writes_fat_pointer(borrowed) {
                            return false;
                        }
                    }
                }
                Statement::SetDiscriminant { place, .. } | Statement::Deinit { place } => {
                    if place.local == param_local {
                        return false;
                    }
                }
                _ => {}
            }
        }
    }
    true
}

/// The v1 assumable fragment: boolean structure + integer/float comparisons and
/// linear-ish arithmetic over parameters and literals. Everything else —
/// division, bitvectors, quantifiers, function applications — is rejected
/// (the assumption is skipped, never the function).
///
/// A binary64 float literal (`FpConst`) is an admissible LEAF: it is a constant
/// operand of a magnitude-bound comparison (`self.0 <= 1.0e30`), exactly the
/// integer-literal case one sort over. Admitting it does not widen the soundness
/// surface — the assume-guarantee discipline (the referenced var must be an entry
/// parameter, the predicate must have a ground witness, no shadow) runs unchanged;
/// a float constant introduces no variable, no aliasing, no unsat channel. Without
/// this arm every float-magnitude precondition falls to `_ => false`
/// (UnsupportedSyntax) and is dropped, leaving the body's overflow VCs with no
/// input bound to discharge against.
fn in_assumable_fragment(formula: &Formula) -> bool {
    match formula {
        Formula::Bool(_) | Formula::Int(_) | Formula::UInt(_) => true,
        Formula::FpConst { .. } => true,
        Formula::Var(..) | Formula::SymVar(..) => true,
        Formula::Not(inner) | Formula::Neg(inner) => in_assumable_fragment(inner),
        Formula::And(items) | Formula::Or(items) => items.iter().all(in_assumable_fragment),
        Formula::Implies(a, b)
        | Formula::Eq(a, b)
        | Formula::Lt(a, b)
        | Formula::Le(a, b)
        | Formula::Gt(a, b)
        | Formula::Ge(a, b)
        | Formula::Add(a, b)
        | Formula::Sub(a, b)
        | Formula::Mul(a, b) => in_assumable_fragment(a) && in_assumable_fragment(b),
        _ => false,
    }
}

/// Search for a concrete ground model of `AND(preconditions)` by exact i128
/// evaluation over a small candidate set per variable: 0, ±1, every literal
/// occurring in the predicates, and each literal ±1. The cross-product is
/// capped; over cap (or no witness) we refuse the assumption. A returned
/// witness is a genuine model, so this check cannot admit an unsatisfiable
/// predicate.
fn has_ground_witness(
    preconditions: &[Formula],
    body: &VerifiableBody,
    length_symbols: &FxHashSet<String>,
) -> bool {
    const MAX_ASSIGNMENTS: usize = 4096;

    let mut var_set: FxHashSet<String> = FxHashSet::default();
    for f in preconditions {
        var_set.extend(f.free_variables());
    }
    let mut vars: Vec<String> = var_set.into_iter().collect();
    vars.sort();
    if vars.is_empty() {
        // Ground predicate: just evaluate it.
        let env = FxHashMap::default();
        return preconditions.iter().all(|f| eval_bool(f, &env) == Some(true));
    }

    let mut candidates: Vec<i128> = vec![0, 1, -1];
    for f in preconditions {
        collect_literals(f, &mut candidates);
    }
    let mut expanded = Vec::with_capacity(candidates.len() * 3);
    for &c in &candidates {
        expanded.push(c);
        if let Some(v) = c.checked_add(1) {
            expanded.push(v);
        }
        if let Some(v) = c.checked_sub(1) {
            expanded.push(v);
        }
    }
    expanded.sort_unstable();
    expanded.dedup();

    let domains = witness_domains(body, length_symbols, preconditions);

    // Fast accept: the all-zeros / all-false assignment. Per-field magnitude
    // preconditions (`|self.0| <= C && |self.1| <= C && …`, centered at 0) are
    // satisfied by it, and 0 is a representable value of every integer/float
    // type — so this IS a genuine ground model. It admits such conjunctions
    // WITHOUT the cross-product enumeration below, whose `MAX_ASSIGNMENTS` cap
    // would otherwise bail to a spurious "no witness" for 4+ independent field
    // variables (8^4 = 4096). SOUNDNESS: it accepts only on a concrete satisfying
    // assignment, so it can never admit an unsatisfiable predicate; and it only
    // ADDS accepts — a predicate the enumeration would reject at zero simply
    // evaluates to false here and falls through to the unchanged search.
    let zero_env: FxHashMap<&str, WitnessValue> = vars
        .iter()
        .map(|name| {
            let value = match domains.get(name) {
                Some(WitnessDomain::Bool) => WitnessValue::Bool(false),
                _ => WitnessValue::Int(0),
            };
            (name.as_str(), value)
        })
        .collect();
    if preconditions.iter().all(|f| eval_bool(f, &zero_env) == Some(true)) {
        return true;
    }

    let candidates_by_var: Vec<Vec<WitnessValue>> = vars
        .iter()
        .map(|name| match domains.get(name) {
            Some(WitnessDomain::Bool) => vec![WitnessValue::Bool(false), WitnessValue::Bool(true)],
            Some(WitnessDomain::Int { min, max }) => {
                let mut values = expanded
                    .iter()
                    .copied()
                    .filter(|value| value >= min && value <= max)
                    .collect::<Vec<_>>();
                values.extend([*min, *max]);
                values.sort_unstable();
                values.dedup();
                values.into_iter().map(WitnessValue::Int).collect()
            }
            None => expanded.iter().copied().map(WitnessValue::Int).collect(),
        })
        .collect();
    if candidates_by_var.iter().any(Vec::is_empty) {
        return false;
    }
    let total = candidates_by_var
        .iter()
        .try_fold(1usize, |product, candidates| product.checked_mul(candidates.len()))
        .unwrap_or(usize::MAX);
    if total > MAX_ASSIGNMENTS {
        return false;
    }

    let mut indices = vec![0usize; vars.len()];
    loop {
        let env: FxHashMap<&str, WitnessValue> = vars
            .iter()
            .zip(indices.iter())
            .enumerate()
            .map(|(position, (variable, &index))| {
                (variable.as_str(), candidates_by_var[position][index])
            })
            .collect();
        if preconditions.iter().all(|f| eval_bool(f, &env) == Some(true)) {
            return true;
        }
        // Odometer increment.
        let mut pos = 0;
        loop {
            if pos == indices.len() {
                return false;
            }
            indices[pos] += 1;
            if indices[pos] < candidates_by_var[pos].len() {
                break;
            }
            indices[pos] = 0;
            pos += 1;
        }
    }
}

#[derive(Debug, Clone, Copy)]
enum WitnessValue {
    Bool(bool),
    Int(i128),
}

#[derive(Debug, Clone, Copy)]
enum WitnessDomain {
    Bool,
    Int { min: i128, max: i128 },
}

fn witness_domains(
    body: &VerifiableBody,
    length_symbols: &FxHashSet<String>,
    preconditions: &[Formula],
) -> FxHashMap<String, WitnessDomain> {
    let mut domains = FxHashMap::default();
    for local in &body.locals {
        if local.index < 1 || local.index > body.arg_count {
            continue;
        }
        let Some(name) = local.name.as_ref() else { continue };
        if let Some(domain) = witness_domain_for_ty(&local.ty) {
            domains.insert(name.clone(), domain);
        }
        if let Ty::Ref { inner, .. } = &local.ty {
            if let Some(domain) = witness_domain_for_ty(inner) {
                domains.insert(format!("{name}*"), domain);
            }
        }
    }
    // Runtime slice lengths and const-generic array lengths are usize values.
    // Restricting to the current compiler target's representable usize subset
    // makes every found witness a real Rust value; an architecture mismatch can
    // only drop a satisfiable assumption (fail closed).
    let usize_max = usize::MAX as i128;
    for symbol in length_symbols {
        domains.insert(symbol.clone(), WitnessDomain::Int { min: 0, max: usize_max });
    }
    // Signature typing may have supplied Bool sorts even when a synthetic test
    // body lacks a precise Ty. Formula evidence can refine Int -> Bool, never
    // widen an exact integer range.
    for formula in preconditions {
        formula.visit(&mut |node| match node {
            Formula::Var(name, trust_types::Sort::Bool) => {
                domains.insert(name.clone(), WitnessDomain::Bool);
            }
            Formula::SymVar(symbol, trust_types::Sort::Bool) => {
                domains.insert(symbol.as_str().to_string(), WitnessDomain::Bool);
            }
            _ => {}
        });
    }
    domains
}

fn witness_domain_for_ty(ty: &Ty) -> Option<WitnessDomain> {
    match ty {
        Ty::Bool => Some(WitnessDomain::Bool),
        Ty::Int { width, signed } if *width > 0 && *width <= 128 => {
            let (min, max) = if *signed {
                if *width == 128 {
                    (i128::MIN, i128::MAX)
                } else {
                    (-(1i128 << (*width - 1)), (1i128 << (*width - 1)) - 1)
                }
            } else if *width >= 127 {
                // The evaluator is exact i128. Searching this representable
                // subset is safe: every returned witness is still a real value.
                (0, i128::MAX)
            } else {
                (0, (1i128 << *width) - 1)
            };
            Some(WitnessDomain::Int { min, max })
        }
        _ => None,
    }
}

fn collect_literals(formula: &Formula, out: &mut Vec<i128>) {
    match formula {
        Formula::Int(v) => out.push(*v),
        Formula::UInt(v) => {
            if let Ok(v) = i128::try_from(*v) {
                out.push(v);
            }
        }
        Formula::Bool(_) | Formula::Var(..) | Formula::SymVar(..) => {}
        Formula::Not(inner) | Formula::Neg(inner) => collect_literals(inner, out),
        Formula::And(items) | Formula::Or(items) => {
            for item in items {
                collect_literals(item, out);
            }
        }
        Formula::Implies(a, b)
        | Formula::Eq(a, b)
        | Formula::Lt(a, b)
        | Formula::Le(a, b)
        | Formula::Gt(a, b)
        | Formula::Ge(a, b)
        | Formula::Add(a, b)
        | Formula::Sub(a, b)
        | Formula::Mul(a, b) => {
            collect_literals(a, out);
            collect_literals(b, out);
        }
        _ => {}
    }
}

fn eval_bool(formula: &Formula, env: &FxHashMap<&str, WitnessValue>) -> Option<bool> {
    match formula {
        Formula::Bool(b) => Some(*b),
        Formula::Var(name, trust_types::Sort::Bool) => match env.get(name.as_str()) {
            Some(WitnessValue::Bool(value)) => Some(*value),
            _ => None,
        },
        Formula::SymVar(symbol, trust_types::Sort::Bool) => match env.get(symbol.as_str()) {
            Some(WitnessValue::Bool(value)) => Some(*value),
            _ => None,
        },
        Formula::Not(inner) => eval_bool(inner, env).map(|b| !b),
        Formula::And(items) => {
            let mut all = true;
            for item in items {
                all &= eval_bool(item, env)?;
            }
            Some(all)
        }
        Formula::Or(items) => {
            let mut any = false;
            for item in items {
                any |= eval_bool(item, env)?;
            }
            Some(any)
        }
        Formula::Implies(a, b) => Some(!eval_bool(a, env)? || eval_bool(b, env)?),
        Formula::Eq(a, b) => {
            // Boolean equality first, then integer.
            if let (Some(x), Some(y)) = (eval_bool_opt(a, env), eval_bool_opt(b, env)) {
                return Some(x == y);
            }
            Some(eval_int(a, env)? == eval_int(b, env)?)
        }
        // Float-sorted magnitude bounds (`self.0 <= 1.0e30`) evaluate with IEEE f64
        // semantics; a non-float comparison falls through to the exact-i128 path.
        Formula::Lt(a, b) => match (eval_float(a, env), eval_float(b, env)) {
            (Some(x), Some(y)) => Some(x < y),
            _ => Some(eval_int(a, env)? < eval_int(b, env)?),
        },
        Formula::Le(a, b) => match (eval_float(a, env), eval_float(b, env)) {
            (Some(x), Some(y)) => Some(x <= y),
            _ => Some(eval_int(a, env)? <= eval_int(b, env)?),
        },
        Formula::Gt(a, b) => match (eval_float(a, env), eval_float(b, env)) {
            (Some(x), Some(y)) => Some(x > y),
            _ => Some(eval_int(a, env)? > eval_int(b, env)?),
        },
        Formula::Ge(a, b) => match (eval_float(a, env), eval_float(b, env)) {
            (Some(x), Some(y)) => Some(x >= y),
            _ => Some(eval_int(a, env)? >= eval_int(b, env)?),
        },
        _ => None,
    }
}

/// Evaluate a float-sorted term to an f64 under a witness assignment, for the
/// magnitude-bound witness search. A witness value (an integer, e.g. the
/// all-zeros probe's `0`) stands in for the field's f64 value (`v as f64`); a
/// binary64 float literal contributes its exact value. `None` for any non-float
/// term, so a comparison with a non-float operand falls back to the exact-i128
/// evaluator. SOUND for the gate: it only ever CONFIRMS that a concrete
/// assignment satisfies a predicate (IEEE semantics), so it cannot admit an
/// unsatisfiable predicate; a satisfiable-only-off-the-integer-grid predicate is
/// simply not found by this search and is dropped (fail-closed).
///
/// Compound arms (Add/Sub/Mul/Neg) evaluate with plain IEEE f64 arithmetic over
/// recursively float-evaluated operands. That IS the check's semantics — the
/// predicate is an FP-sorted formula, so a concrete assignment satisfies it
/// exactly when the IEEE evaluation of the comparison holds. A NaN/±inf result
/// simply fails the comparison honestly (NaN compares false; an infinite
/// magnitude fails a finite bound), which can only miss a witness, never
/// fabricate one. Difference bounds (`(near) - (far) <= -1.0e-6`) reach the
/// gate Float-sorted at any depth (the retype map is recursive), so without
/// the Sub arm the whole precondition set would drop as NoSatisfiableWitness.
fn eval_float(formula: &Formula, env: &FxHashMap<&str, WitnessValue>) -> Option<f64> {
    match formula {
        Formula::FpConst { bits, eb: 11, sb: 53 } => {
            let v = f64::from_bits(*bits as u64);
            if v.is_finite() { Some(v) } else { None }
        }
        Formula::Var(name, trust_types::Sort::Float { .. }) => match env.get(name.as_str()) {
            Some(WitnessValue::Int(value)) => Some(*value as f64),
            _ => None,
        },
        Formula::SymVar(symbol, trust_types::Sort::Float { .. }) => {
            match env.get(symbol.as_str()) {
                Some(WitnessValue::Int(value)) => Some(*value as f64),
                _ => None,
            }
        }
        Formula::Add(a, b) => Some(eval_float(a, env)? + eval_float(b, env)?),
        Formula::Sub(a, b) => Some(eval_float(a, env)? - eval_float(b, env)?),
        Formula::Mul(a, b) => Some(eval_float(a, env)? * eval_float(b, env)?),
        // Negation over ANY float-evaluable operand (literal, var, or compound).
        Formula::Neg(inner) => Some(-eval_float(inner, env)?),
        _ => None,
    }
}

/// Like `eval_bool` but used only for the Eq disambiguation: returns None when
/// the node is not obviously boolean, without treating that as failure.
fn eval_bool_opt(formula: &Formula, env: &FxHashMap<&str, WitnessValue>) -> Option<bool> {
    match formula {
        Formula::Bool(_)
        | Formula::Not(_)
        | Formula::And(_)
        | Formula::Or(_)
        | Formula::Implies(..)
        | Formula::Lt(..)
        | Formula::Le(..)
        | Formula::Gt(..)
        | Formula::Ge(..)
        | Formula::Var(_, trust_types::Sort::Bool)
        | Formula::SymVar(_, trust_types::Sort::Bool) => eval_bool(formula, env),
        _ => None,
    }
}

fn eval_int(formula: &Formula, env: &FxHashMap<&str, WitnessValue>) -> Option<i128> {
    match formula {
        Formula::Int(v) => Some(*v),
        Formula::UInt(v) => i128::try_from(*v).ok(),
        Formula::Var(name, sort) if *sort != trust_types::Sort::Bool => {
            match env.get(name.as_str()) {
                Some(WitnessValue::Int(value)) => Some(*value),
                _ => None,
            }
        }
        Formula::SymVar(symbol, sort) if *sort != trust_types::Sort::Bool => {
            match env.get(symbol.as_str()) {
                Some(WitnessValue::Int(value)) => Some(*value),
                _ => None,
            }
        }
        Formula::Add(a, b) => eval_int(a, env)?.checked_add(eval_int(b, env)?),
        Formula::Sub(a, b) => eval_int(a, env)?.checked_sub(eval_int(b, env)?),
        Formula::Mul(a, b) => eval_int(a, env)?.checked_mul(eval_int(b, env)?),
        Formula::Neg(inner) => eval_int(inner, env)?.checked_neg(),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_types::Sort;

    fn var(name: &str) -> Formula {
        Formula::Var(name.to_string(), Sort::Int)
    }

    fn int(v: i128) -> Formula {
        Formula::Int(v)
    }

    fn body_with(locals: Vec<(usize, Option<&str>)>, arg_count: usize) -> VerifiableBody {
        VerifiableBody {
            locals: locals
                .into_iter()
                .map(|(index, name)| trust_types::LocalDecl {
                    index,
                    ty: trust_types::Ty::Int { width: 64, signed: true },
                    name: name.map(str::to_string),
                })
                .collect(),
            blocks: Vec::new(),
            arg_count,
            return_ty: trust_types::Ty::Int { width: 64, signed: true },
        }
    }

    fn body_with_param_ty(name: &str, ty: trust_types::Ty) -> VerifiableBody {
        VerifiableBody {
            locals: vec![
                trust_types::LocalDecl { index: 0, ty: trust_types::Ty::unit_ty(), name: None },
                trust_types::LocalDecl { index: 1, ty, name: Some(name.to_string()) },
            ],
            blocks: Vec::new(),
            arg_count: 1,
            return_ty: trust_types::Ty::unit_ty(),
        }
    }

    fn bounded(name: &str, lo: i128, hi: i128) -> Formula {
        Formula::And(vec![
            Formula::Ge(Box::new(var(name)), Box::new(int(lo))),
            Formula::Le(Box::new(var(name)), Box::new(int(hi))),
        ])
    }

    fn multimap(entries: &[(&str, &[usize])]) -> FxHashMap<String, Vec<usize>> {
        entries.iter().map(|(name, locals)| (name.to_string(), locals.to_vec())).collect()
    }

    #[test]
    fn honest_bound_passes() {
        let body = body_with(vec![(0, None), (1, Some("x")), (2, Some("tmp"))], 1);
        let names = multimap(&[("x", &[1]), ("tmp", &[2])]);
        let mut pres = vec![bounded("x", -262143, 262143)];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert!(reasons.is_empty(), "{reasons:?}");
        assert_eq!(pres.len(), 1);
    }

    #[test]
    fn shadowed_param_drops_assumption() {
        // local 2 (body-introduced) shares the debug name "x" with param 1.
        let body = body_with(vec![(0, None), (1, Some("x")), (2, Some("x"))], 1);
        let names = multimap(&[("x", &[1, 2])]);
        let mut pres = vec![bounded("x", 0, 10)];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert!(matches!(reasons.as_slice(), [AssumeSkipReason::ShadowedParamName(n)] if n == "x"));
        assert!(pres.is_empty());
    }

    #[test]
    fn copy_propagated_shadow_drops_assumption() {
        // Build #32 regression: optimized MIR copy-propagated `let x = z;` so
        // the shadow's debug entry landed on z's PARAM local (_2). Collapsed
        // per-local names show params (1:"x", 2:"x") — no body-indexed local —
        // but the raw multimap exposes "x" -> [1, 2].
        let body = body_with(vec![(0, None), (1, Some("x")), (2, Some("x"))], 2);
        let names = multimap(&[("x", &[1, 2]), ("z", &[2])]);
        let mut pres = vec![bounded("x", 0, 10)];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert!(
            reasons.iter().any(|r| matches!(r, AssumeSkipReason::ShadowedParamName(n) if n == "x")),
            "{reasons:?}"
        );
        assert!(pres.is_empty());
    }

    #[test]
    fn alias_on_param_local_drops_assumption() {
        // A non-referenced name ("w") aliasing the referenced param's local
        // makes the binding ambiguous — drop honestly instead of staying
        // silently inert.
        let body = body_with(vec![(0, None), (1, Some("w"))], 1);
        let names = multimap(&[("x", &[1]), ("w", &[1])]);
        let mut pres = vec![bounded("x", 0, 10)];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert!(
            reasons.iter().any(|r| matches!(r, AssumeSkipReason::ShadowedParamName(_))),
            "{reasons:?}"
        );
        assert!(pres.is_empty());
    }

    #[test]
    fn contradictory_predicate_drops_assumption() {
        let body = body_with(vec![(0, None), (1, Some("x"))], 1);
        let names = multimap(&[("x", &[1])]);
        let mut pres = vec![Formula::And(vec![
            Formula::Gt(Box::new(var("x")), Box::new(int(10))),
            Formula::Lt(Box::new(var("x")), Box::new(int(5))),
        ])];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert_eq!(reasons, vec![AssumeSkipReason::NoSatisfiableWitness]);
        assert!(pres.is_empty());
    }

    #[test]
    fn u8_out_of_range_witness_cannot_vacuously_discharge_body() {
        let body = body_with_param_ty("x", trust_types::Ty::Int { width: 8, signed: false });
        let names = multimap(&[("x", &[1])]);
        let mut pres = vec![Formula::Gt(Box::new(var("x")), Box::new(int(300)))];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert_eq!(reasons, vec![AssumeSkipReason::NoSatisfiableWitness]);
        assert!(pres.is_empty(), "the impossible hypothesis must not reach any body VC");
    }

    #[test]
    fn i8_out_of_range_witness_cannot_vacuously_discharge_body() {
        let body = body_with_param_ty("x", trust_types::Ty::Int { width: 8, signed: true });
        let names = multimap(&[("x", &[1])]);
        let mut pres = vec![Formula::Lt(Box::new(var("x")), Box::new(int(-128)))];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert_eq!(reasons, vec![AssumeSkipReason::NoSatisfiableWitness]);
        assert!(pres.is_empty());
    }

    #[test]
    fn typed_bool_requires_has_real_witness_and_contradiction_does_not() {
        let body = body_with_param_ty("flag", trust_types::Ty::Bool);
        let names = multimap(&[("flag", &[1])]);
        let flag = Formula::Var("flag".into(), trust_types::Sort::Bool);
        let mut honest = vec![Formula::Eq(Box::new(flag.clone()), Box::new(Formula::Bool(true)))];
        assert!(gate_contract_preconditions(&mut honest, &body, &names).is_empty());
        assert_eq!(honest.len(), 1);

        let mut impossible = vec![Formula::And(vec![flag.clone(), Formula::Not(Box::new(flag))])];
        assert_eq!(
            gate_contract_preconditions(&mut impossible, &body, &names),
            vec![AssumeSkipReason::NoSatisfiableWitness]
        );
        assert!(impossible.is_empty());
    }

    #[test]
    fn non_param_variable_drops_assumption() {
        let body = body_with(vec![(0, None), (1, Some("x"))], 1);
        let names = multimap(&[("x", &[1])]);
        let mut pres = vec![bounded("y", 0, 10)];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert!(
            reasons.iter().any(|r| matches!(r, AssumeSkipReason::NonParamVariable(n) if n == "y"))
        );
        assert!(pres.is_empty());
    }

    #[test]
    fn unsupported_syntax_drops_assumption() {
        let body = body_with(vec![(0, None), (1, Some("x"))], 1);
        let names = multimap(&[("x", &[1])]);
        let mut pres = vec![Formula::Eq(
            Box::new(Formula::Div(Box::new(var("x")), Box::new(int(2)))),
            Box::new(int(1)),
        )];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert_eq!(reasons, vec![AssumeSkipReason::UnsupportedSyntax]);
        assert!(pres.is_empty());
    }

    /// A binary64 float literal `1.0e30`.
    fn fp(v: f64) -> Formula {
        Formula::FpConst { bits: u128::from(v.to_bits()), eb: 11, sb: 53 }
    }

    /// A `Float`-sorted field-projection var (`self.0`), as the spec parser's
    /// `coerce_float_comparison_operands` produces for an f64 field bound.
    fn ffield(name: &str) -> Formula {
        Formula::Var(name.to_string(), Sort::Float { eb: 11, sb: 53 })
    }

    /// `-C <= name <= C` over an f64 field: the two-sided magnitude bound a3d-geom
    /// spells `self.x <= 1.0e30 && self.x >= -1.0e30`, lowered to field-index form.
    fn fbounded(name: &str, c: f64) -> Formula {
        Formula::And(vec![
            Formula::Le(Box::new(ffield(name)), Box::new(fp(c))),
            Formula::Ge(Box::new(ffield(name)), Box::new(fp(-c))),
        ])
    }

    #[test]
    fn float_field_magnitude_precondition_is_assumed() {
        // `dot(self: Vec3, o: Vec3)` with `#[requires(|self.i| <= 1e30 && |o.i| <=
        // 1e30)]`, lowered to field-index vars `self.0..self.2`, `o.0..o.2`. The
        // gate MUST assume it: without the `FpConst` arm in `in_assumable_fragment`
        // the whole set is dropped as UnsupportedSyntax and the body's `self.x*o.x`
        // overflow VCs have no input bound to discharge against (the a3d-geom
        // FloatOverflowToInfinity regression). `self`=local 1, `o`=local 2 are the
        // by-value struct params; the field vars normalize to those param bases.
        let body = body_with(vec![(0, None), (1, Some("self")), (2, Some("o"))], 2);
        let names = multimap(&[("self", &[1]), ("o", &[2])]);
        let mut pres = vec![Formula::And(vec![
            fbounded("self.0", 1.0e30),
            fbounded("self.1", 1.0e30),
            fbounded("self.2", 1.0e30),
            fbounded("o.0", 1.0e30),
            fbounded("o.1", 1.0e30),
            fbounded("o.2", 1.0e30),
        ])];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert!(reasons.is_empty(), "float field-magnitude precond must be assumed: {reasons:?}");
        assert_eq!(pres.len(), 1, "the precondition must survive the gate");
    }

    #[test]
    fn float_precondition_over_nonparam_field_still_dropped() {
        // Soundness guard: admitting FpConst must NOT relax the entry-parameter
        // discipline. A field bound over a NON-parameter base (`ghost.0`) is still
        // rejected — the float literal is fine, but `ghost` is not a param.
        let body = body_with(vec![(0, None), (1, Some("self"))], 1);
        let names = multimap(&[("self", &[1])]);
        let mut pres = vec![fbounded("ghost.0", 1.0e30)];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert!(
            reasons.iter().any(|r| matches!(r, AssumeSkipReason::NonParamVariable(_))),
            "a float bound over a non-param base must still drop: {reasons:?}"
        );
        assert!(pres.is_empty());
    }

    #[test]
    fn negative_literal_witness_found() {
        // Witness needs a negative candidate (-262143 occurs as a literal).
        let body = body_with(vec![(0, None), (1, Some("y"))], 1);
        let names = multimap(&[("y", &[1])]);
        let mut pres = vec![bounded("y", -262143, -262000)];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert!(reasons.is_empty(), "{reasons:?}");
    }

    /// A body with a single reference parameter `a` at local 1.
    fn ref_param_body(mutable: bool) -> VerifiableBody {
        VerifiableBody {
            locals: vec![
                trust_types::LocalDecl {
                    index: 0,
                    ty: trust_types::Ty::Int { width: 32, signed: false },
                    name: None,
                },
                trust_types::LocalDecl {
                    index: 1,
                    ty: trust_types::Ty::Ref {
                        mutable,
                        inner: Box::new(trust_types::Ty::Int { width: 32, signed: false }),
                    },
                    name: Some("a".to_string()),
                },
            ],
            blocks: Vec::new(),
            arg_count: 1,
            return_ty: trust_types::Ty::Int { width: 32, signed: false },
        }
    }

    #[test]
    fn shared_ref_deref_is_assumed() {
        // `#[requires(*a <= 100)]` on `a: &u32` — the pointee of a SHARED ref is
        // immutable, so the caller-proved entry fact is assume-guarantee sound.
        // The deref term `a*` must be recognized as caller-bound (audit #4).
        let body = ref_param_body(false);
        let names = multimap(&[("a", &[1])]);
        let mut pres = vec![Formula::Le(Box::new(var("a*")), Box::new(int(100)))];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert!(reasons.is_empty(), "shared-ref deref must be assumed: {reasons:?}");
        assert_eq!(pres.len(), 1, "the precondition must survive the gate");
    }

    #[test]
    fn mut_ref_deref_drops_assumption() {
        // `#[requires(*a <= 100)]` on `a: &mut u32` — the pointee CAN be mutated
        // in the body, so the entry fact may go stale. Assuming it is a false-
        // PROVE hazard, so the gate must drop it (fail-closed). The raw base `a`
        // aliases a parameter local, so the None-classification reports the
        // sharper ShadowedParamName diagnostic (the `aliases_param` branch);
        // either way the assumption set is dropped.
        let body = ref_param_body(true);
        let names = multimap(&[("a", &[1])]);
        let mut pres = vec![Formula::Le(Box::new(var("a*")), Box::new(int(100)))];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert!(
            reasons.iter().any(|r| matches!(r, AssumeSkipReason::ShadowedParamName(n) if n == "a")),
            "mut-ref deref must NOT be assumed: {reasons:?}"
        );
        assert!(pres.is_empty());
    }

    // ---- Trust: piece #8 — length-relationship precondition admissibility ----

    fn mut_slice_ty() -> trust_types::Ty {
        trust_types::Ty::Ref {
            mutable: true,
            inner: Box::new(trust_types::Ty::Slice {
                elem: Box::new(trust_types::Ty::Int { width: 32, signed: false }),
            }),
        }
    }

    /// A body `fn fill(arr: &mut [u32], n: usize)` — one slice param `arr` (local
    /// 1), one scalar param `n` (local 2), no reslice. `blocks` is empty, so the
    /// slice param is trivially length-stable.
    fn fill_body() -> VerifiableBody {
        VerifiableBody {
            locals: vec![
                trust_types::LocalDecl { index: 0, ty: trust_types::Ty::unit_ty(), name: None },
                trust_types::LocalDecl { index: 1, ty: mut_slice_ty(), name: Some("arr".into()) },
                trust_types::LocalDecl {
                    index: 2,
                    ty: trust_types::Ty::Int { width: 64, signed: false },
                    name: Some("n".into()),
                },
            ],
            blocks: Vec::new(),
            arg_count: 2,
            return_ty: trust_types::Ty::unit_ty(),
        }
    }

    fn resliced_fill_body() -> VerifiableBody {
        let mut body = fill_body();
        // Simulate a mutable reborrow of the WHOLE param fat pointer (`&mut arr`,
        // no leading deref) — the reslice channel.
        body.blocks = vec![trust_types::BasicBlock {
            id: trust_types::BlockId(0),
            stmts: vec![trust_types::Statement::Assign {
                place: trust_types::Place::local(3),
                rvalue: trust_types::Rvalue::Ref {
                    mutable: true,
                    place: trust_types::Place::local(1),
                },
                span: trust_types::SourceSpan::default(),
            }],
            terminator: trust_types::Terminator::Return,
        }];
        body
    }

    #[test]
    fn length_precond_of_slice_param_admitted() {
        // `P = n <= arr__slice_len` over a slice param `arr` + scalar param `n`.
        let body = fill_body();
        let names = multimap(&[("arr", &[1]), ("n", &[2])]);
        let mut pres = vec![Formula::Le(Box::new(var("n")), Box::new(var("arr__slice_len")))];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert!(reasons.is_empty(), "slice-param length precond must be admitted: {reasons:?}");
        assert_eq!(pres.len(), 1, "the precondition must survive the gate");
    }

    #[test]
    fn source_length_precond_normalizes_to_canonical_slice_symbol() {
        // Exact source `arr.len()` lowers to `arr_len`, but body bounds VCs and
        // modular σ summaries use `arr__slice_len`. Admission must rewrite to
        // that canonical leaf, never merely whitelist an independent variable.
        let body = fill_body();
        let names = multimap(&[("arr", &[1]), ("n", &[2])]);
        let mut pres = vec![Formula::Le(Box::new(var("n")), Box::new(var("arr_len")))];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert!(reasons.is_empty(), "source slice length must be admitted: {reasons:?}");
        assert_eq!(
            pres,
            vec![Formula::Le(Box::new(var("n")), Box::new(var("arr__slice_len")),)],
            "source and bounds formulas must share the canonical length leaf",
        );
        assert!(!pres[0].free_variables().contains("arr_len"));
    }

    #[test]
    fn negative_slice_length_witness_is_impossible_and_dropped() {
        let body = fill_body();
        let names = multimap(&[("arr", &[1]), ("n", &[2])]);
        let mut pres = vec![Formula::Lt(Box::new(var("arr__slice_len")), Box::new(int(0)))];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert_eq!(reasons, vec![AssumeSkipReason::NoSatisfiableWitness]);
        assert!(pres.is_empty());
    }

    #[test]
    fn length_of_nonslice_param_rejected() {
        // `x__slice_len` where `x` is a SCALAR param — not a slice, so its
        // `__slice_len` symbol is NOT admitted (NonParamVariable).
        let body = body_with(vec![(0, None), (1, Some("x"))], 1);
        let names = multimap(&[("x", &[1])]);
        let mut pres = vec![Formula::Le(Box::new(var("x")), Box::new(var("x__slice_len")))];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert!(
            reasons
                .iter()
                .any(|r| matches!(r, AssumeSkipReason::NonParamVariable(n) if n == "x__slice_len")),
            "scalar-param `__slice_len` must be rejected: {reasons:?}"
        );
        assert!(pres.is_empty());
    }

    #[test]
    fn length_of_resliced_slice_param_rejected() {
        // INV-1: the callee reslices `arr` (a mutable reborrow of the whole param
        // fat pointer), so `arr__slice_len` is NOT length-stable → dropped.
        let body = resliced_fill_body();
        let names = multimap(&[("arr", &[1]), ("n", &[2])]);
        let mut pres = vec![Formula::Le(Box::new(var("n")), Box::new(var("arr__slice_len")))];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert!(
            reasons.iter().any(
                |r| matches!(r, AssumeSkipReason::NonParamVariable(n) if n == "arr__slice_len")
            ),
            "resliced slice param length must be rejected (INV-1): {reasons:?}"
        );
        assert!(pres.is_empty());
    }

    #[test]
    fn source_length_of_resliced_slice_param_rejected() {
        let body = resliced_fill_body();
        let names = multimap(&[("arr", &[1]), ("n", &[2])]);
        let mut pres = vec![Formula::Le(Box::new(var("n")), Box::new(var("arr_len")))];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert!(
            reasons
                .iter()
                .any(|r| matches!(r, AssumeSkipReason::NonParamVariable(n) if n == "arr_len")),
            "unstable source length must not be rebound or admitted: {reasons:?}",
        );
        assert!(pres.is_empty());
    }

    #[test]
    fn element_write_keeps_slice_param_length_stable() {
        // `arr[i] = 0` lowers to a store THROUGH a deref (`(*arr)[i] = 0`), which
        // writes the pointee, not the fat pointer — the length stays stable, so the
        // length symbol is STILL admitted. (This is the `fill` body's actual shape.)
        let mut body = fill_body();
        body.blocks = vec![trust_types::BasicBlock {
            id: trust_types::BlockId(0),
            stmts: vec![trust_types::Statement::Assign {
                place: trust_types::Place {
                    local: 1,
                    projections: vec![
                        trust_types::Projection::Deref,
                        trust_types::Projection::Index(2),
                    ],
                },
                rvalue: trust_types::Rvalue::Use(trust_types::Operand::Constant(
                    trust_types::ConstValue::Int(0),
                )),
                span: trust_types::SourceSpan::default(),
            }],
            terminator: trust_types::Terminator::Return,
        }];
        let names = multimap(&[("arr", &[1]), ("n", &[2])]);
        let mut pres = vec![Formula::Le(Box::new(var("n")), Box::new(var("arr__slice_len")))];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert!(
            reasons.is_empty(),
            "element write must not disqualify the slice-param length: {reasons:?}"
        );
        assert_eq!(pres.len(), 1);
    }

    #[test]
    fn shadowed_slice_param_name_length_rejected() {
        // A body local shadows the param name `arr` — the `arr__slice_len` render
        // is ambiguous (could key on the shadow), so it is NOT admitted.
        let mut body = fill_body();
        body.locals.push(trust_types::LocalDecl {
            index: 3,
            ty: mut_slice_ty(),
            name: Some("arr".into()),
        });
        let names = multimap(&[("arr", &[1, 3]), ("n", &[2])]);
        let mut pres = vec![Formula::Le(Box::new(var("n")), Box::new(var("arr__slice_len")))];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert!(
            reasons.iter().any(
                |r| matches!(r, AssumeSkipReason::NonParamVariable(n) if n == "arr__slice_len")
            ),
            "shadowed slice-param length must be rejected: {reasons:?}"
        );
        assert!(pres.is_empty());
    }

    #[test]
    fn source_length_of_shadowed_slice_param_rejected() {
        let mut body = fill_body();
        body.locals.push(trust_types::LocalDecl {
            index: 3,
            ty: mut_slice_ty(),
            name: Some("arr".into()),
        });
        let names = multimap(&[("arr", &[1, 3]), ("n", &[2])]);
        let mut pres = vec![Formula::Le(Box::new(var("n")), Box::new(var("arr_len")))];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert!(
            reasons
                .iter()
                .any(|r| matches!(r, AssumeSkipReason::NonParamVariable(n) if n == "arr_len")),
            "shadowed source length must not be rebound or admitted: {reasons:?}",
        );
        assert!(pres.is_empty());
    }

    // ---- Trust: float field-magnitude precondition admissibility ----

    /// `|name| <= c`, the two-sided form a float magnitude `#[requires]` lowers to.
    fn field_bounded(name: &str, c: i128) -> Formula {
        Formula::And(vec![
            Formula::Le(Box::new(var(name)), Box::new(int(c))),
            Formula::Ge(Box::new(var(name)), Box::new(int(-c))),
        ])
    }

    #[test]
    fn byvalue_param_field_bound_admitted() {
        // `#[requires(|self.0|<=C && |self.1|<=C && |o.0|<=C && |o.1|<=C)]` on
        // `dot(self, o)` — by-value params, field-index vars → all survive.
        let body = body_with(vec![(0, None), (1, Some("self")), (2, Some("o"))], 2);
        let names = multimap(&[("self", &[1]), ("o", &[2])]);
        let mut pres = vec![
            field_bounded("self.0", 1_000_000),
            field_bounded("self.1", 1_000_000),
            field_bounded("o.0", 1_000_000),
            field_bounded("o.1", 1_000_000),
        ];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert!(reasons.is_empty(), "by-value param field bounds must survive: {reasons:?}");
        assert_eq!(pres.len(), 4);
    }

    #[test]
    fn many_field_bounds_admitted_via_all_zeros_witness() {
        // 8 independent field vars (Vec4::dot): the brute-force witness search caps
        // at MAX_ASSIGNMENTS (8^4 = 4096) and would bail to a spurious "no
        // witness"; the all-zeros fast-accept admits the conjunction.
        let body = body_with(vec![(0, None), (1, Some("self")), (2, Some("o"))], 2);
        let names = multimap(&[("self", &[1]), ("o", &[2])]);
        let mut pres: Vec<Formula> =
            ["self.0", "self.1", "self.2", "self.3", "o.0", "o.1", "o.2", "o.3"]
                .iter()
                .copied()
                .map(|n| field_bounded(n, 1_000_000_000))
                .collect();
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert!(reasons.is_empty(), "8 field bounds must be admitted (all-zeros): {reasons:?}");
        assert_eq!(pres.len(), 8);
    }

    #[test]
    fn shared_ref_param_field_bound_admitted() {
        // `(*self).2` on a `&T` param renders "a*.0" (Deref then Field). The
        // immutable pointee makes the entry fact assumable, like the `<p>*` case.
        let body = ref_param_body(false);
        let names = multimap(&[("a", &[1])]);
        let mut pres = vec![field_bounded("a*.0", 1_000_000)];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert!(reasons.is_empty(), "shared-ref param field must be admitted: {reasons:?}");
        assert_eq!(pres.len(), 1);
    }

    #[test]
    fn mut_ref_param_field_bound_rejected() {
        // A `&mut` pointee CAN be mutated → its field entry fact may go stale → NOT
        // admitted (fail-closed), matching the `<p>*` &mut rejection.
        let body = ref_param_body(true);
        let names = multimap(&[("a", &[1])]);
        let mut pres = vec![field_bounded("a*.0", 1_000_000)];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert!(
            reasons
                .iter()
                .any(|r| matches!(r, AssumeSkipReason::NonParamVariable(n) if n == "a*.0")),
            "mut-ref param field must be rejected: {reasons:?}"
        );
        assert!(pres.is_empty());
    }

    #[test]
    fn field_of_non_param_rejected() {
        // `tmp.0` where `tmp` is a BODY local, not a parameter → NonParamVariable.
        let body = body_with(vec![(0, None), (1, Some("self")), (2, Some("tmp"))], 1);
        let names = multimap(&[("self", &[1]), ("tmp", &[2])]);
        let mut pres = vec![field_bounded("tmp.0", 1_000_000)];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert!(
            reasons
                .iter()
                .any(|r| matches!(r, AssumeSkipReason::NonParamVariable(n) if n == "tmp.0")),
            "field of a non-parameter must be rejected: {reasons:?}"
        );
        assert!(pres.is_empty());
    }

    #[test]
    fn shadowed_base_field_bound_rejected() {
        // A body local shadows the param name `self` → the base "self" maps to two
        // locals → the field precondition's base is ambiguous → dropped (this is the
        // same false-PROVE guard that protects bare-param bounds).
        let body = body_with(vec![(0, None), (1, Some("self")), (2, Some("self"))], 1);
        let names = multimap(&[("self", &[1, 2])]);
        let mut pres = vec![field_bounded("self.0", 1_000_000)];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert!(
            reasons
                .iter()
                .any(|r| matches!(r, AssumeSkipReason::ShadowedParamName(n) if n == "self")),
            "shadowed field base must be rejected: {reasons:?}"
        );
        assert!(pres.is_empty());
    }

    #[test]
    fn contradictory_field_bound_still_dropped() {
        // The all-zeros probe must NOT paper over vacuity: `self.0 >= 5 && self.0 <= 3`
        // fails at zero and everywhere → still NoSatisfiableWitness.
        let body = body_with(vec![(0, None), (1, Some("self"))], 1);
        let names = multimap(&[("self", &[1])]);
        let mut pres = vec![Formula::And(vec![
            Formula::Ge(Box::new(var("self.0")), Box::new(int(5))),
            Formula::Le(Box::new(var("self.0")), Box::new(int(3))),
        ])];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert_eq!(reasons, vec![AssumeSkipReason::NoSatisfiableWitness]);
        assert!(pres.is_empty());
    }

    // ---- Trust: FLOAT-literal field magnitude preconditions ----

    /// An f64 float-sorted variable, as the retyped contract carries a field var
    /// compared against a float literal. (The float-literal helper `fp` is defined
    /// once, further up — a second copy here would be a duplicate definition.)
    fn float_var(name: &str) -> Formula {
        Formula::Var(name.to_string(), Sort::Float { eb: 11, sb: 53 })
    }
    /// `|name| <= c` with FLOAT-sorted var and float-literal bounds (the a3d shape).
    fn float_field_bounded(name: &str, c: f64) -> Formula {
        Formula::And(vec![
            Formula::Le(Box::new(float_var(name)), Box::new(fp(c))),
            Formula::Ge(Box::new(float_var(name)), Box::new(fp(-c))),
        ])
    }

    #[test]
    fn float_field_magnitude_bound_admitted() {
        // `#[requires(self.0 <= 1.0e30 && self.0 >= -1.0e30)]` — the float-sorted
        // field bound is satisfied by the all-zeros witness (0.0 ∈ [-1e30, 1e30]),
        // which the float-aware `eval_bool` now recognises. It must survive the gate.
        let body = body_with(vec![(0, None), (1, Some("self"))], 1);
        let names = multimap(&[("self", &[1])]);
        let mut pres = vec![float_field_bounded("self.0", 1.0e30)];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert!(reasons.is_empty(), "float field bound must be admitted: {reasons:?}");
        assert_eq!(pres.len(), 1);
    }

    #[test]
    fn contradictory_float_field_bound_dropped() {
        // SOUNDNESS: `self.0 >= 1e30 && self.0 <= -1e30` is UNSATISFIABLE — the
        // all-zeros probe fails (0.0 !>= 1e30) and no integer-grid witness satisfies
        // it, so it is dropped (fail-closed). The float eval must not false-accept.
        let body = body_with(vec![(0, None), (1, Some("self"))], 1);
        let names = multimap(&[("self", &[1])]);
        let mut pres = vec![Formula::And(vec![
            Formula::Ge(Box::new(float_var("self.0")), Box::new(fp(1.0e30))),
            Formula::Le(Box::new(float_var("self.0")), Box::new(fp(-1.0e30))),
        ])];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert_eq!(reasons, vec![AssumeSkipReason::NoSatisfiableWitness]);
        assert!(pres.is_empty());
    }

    // ---- Trust: full literal projection chains (F4 gate admission) ----

    #[test]
    fn byvalue_chain_with_array_index_admitted() {
        // `self.0[3].1 <= 1e30 && …` on a by-value param `self` (Mat4-style
        // `#[requires(self.cols[3].y <= 1.0e30)]` lowered to positional form).
        // The chain normalizes to base `self`; the full bracketed name never
        // enters the referenced set, and the all-zeros witness satisfies it.
        let body = body_with(vec![(0, None), (1, Some("self"))], 1);
        let names = multimap(&[("self", &[1])]);
        let mut pres = vec![float_field_bounded("self.0[3].1", 1.0e30)];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert!(
            reasons.is_empty(),
            "literal chain on by-value param must be admitted: {reasons:?}"
        );
        assert_eq!(pres.len(), 1);
    }

    #[test]
    fn shared_ref_chain_admitted() {
        // `a*.0.0` — a nested field of a SHARED-ref parameter's pointee
        // (`(*self).min.x` → `self*.0.0`, the Aabb shape). The immutable pointee
        // makes any depth of the chain an entry fact, like the `<p>*` case.
        let body = ref_param_body(false);
        let names = multimap(&[("a", &[1])]);
        let mut pres = vec![float_field_bounded("a*.0.0", 1.0e30)];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert!(reasons.is_empty(), "shared-ref nested chain must be admitted: {reasons:?}");
        assert_eq!(pres.len(), 1);
    }

    #[test]
    fn mut_ref_chain_rejected() {
        // SOUNDNESS twin: the SAME chain over a `&mut` param must NOT be assumed —
        // the pointee can be mutated, staling the entry fact (fail-closed).
        let body = ref_param_body(true);
        let names = multimap(&[("a", &[1])]);
        let mut pres = vec![float_field_bounded("a*.0.0", 1.0e30)];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert!(
            reasons
                .iter()
                .any(|r| matches!(r, AssumeSkipReason::NonParamVariable(n) if n == "a*.0.0")),
            "mut-ref chain must be rejected: {reasons:?}"
        );
        assert!(pres.is_empty());
    }

    #[test]
    fn chain_of_non_param_rejected() {
        // SOUNDNESS twin: a well-formed chain whose HEAD is not a parameter
        // (`ghost.0[1]`) is not caller-bound — still NonParamVariable.
        let body = body_with(vec![(0, None), (1, Some("self"))], 1);
        let names = multimap(&[("self", &[1])]);
        let mut pres = vec![float_field_bounded("ghost.0[1]", 1.0e30)];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert!(
            reasons
                .iter()
                .any(|r| matches!(r, AssumeSkipReason::NonParamVariable(n) if n == "ghost.0[1]")),
            "chain off a non-param head must be rejected: {reasons:?}"
        );
        assert!(pres.is_empty());
    }

    #[test]
    fn runtime_index_chain_rejected() {
        // SOUNDNESS twin: a NON-LITERAL index (`self.0[x].1`) is not
        // entry-determined. The spec parser cannot produce this name today;
        // the gate still rejects it on its own (defense in depth, fail-closed).
        let body = body_with(vec![(0, None), (1, Some("self"))], 1);
        let names = multimap(&[("self", &[1])]);
        let mut pres = vec![float_field_bounded("self.0[x].1", 1.0e30)];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert!(
            reasons
                .iter()
                .any(|r| matches!(r, AssumeSkipReason::NonParamVariable(n) if n == "self.0[x].1")),
            "runtime-index chain must be rejected: {reasons:?}"
        );
        assert!(pres.is_empty());
    }

    #[test]
    fn head_index_of_array_param_admitted() {
        // `p[0]` — a literal element of a parameter that IS an array. The head is
        // in param_names and the segment is a literal index, so the same
        // entry-value rationale as `p.0` applies (admission is name-disciplined;
        // the declared Ty is not consulted here).
        let body = body_with(vec![(0, None), (1, Some("p"))], 1);
        let names = multimap(&[("p", &[1])]);
        let mut pres = vec![float_field_bounded("p[0]", 1.0e30)];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert!(reasons.is_empty(), "literal head-index of a param must be admitted: {reasons:?}");
        assert_eq!(pres.len(), 1);
    }

    #[test]
    fn malformed_chains_rejected() {
        // Shapes the grammar must fall through to None on: a `*` not immediately
        // after the head, an unclosed bracket, an empty segment, digits-then-junk
        // inside a bracket. All fail-closed as NonParamVariable.
        let body = body_with(vec![(0, None), (1, Some("self"))], 1);
        let names = multimap(&[("self", &[1])]);
        for bad in ["self.0*.1", "self.0[3", "self.[0]", "self.0[3x]", "self..0"] {
            let mut pres = vec![float_field_bounded(bad, 1.0e30)];
            let reasons = gate_contract_preconditions(&mut pres, &body, &names);
            assert!(
                reasons
                    .iter()
                    .any(|r| matches!(r, AssumeSkipReason::NonParamVariable(n) if n == bad)),
                "malformed chain `{bad}` must be rejected: {reasons:?}"
            );
            assert!(pres.is_empty(), "malformed chain `{bad}` must drop the set");
        }
    }

    #[test]
    fn many_bracketed_chain_bounds_admitted_via_all_zeros() {
        // 16 independent bracketed-chain vars (Mat4: cols[0..3] × fields 0..3).
        // The cross-product enumeration would blow MAX_ASSIGNMENTS; the all-zeros
        // fast path must satisfy the pure magnitude conjunction (each var misses
        // `witness_domains`, reads Int(0), and evaluates as 0.0 in the float lane).
        let body = body_with(vec![(0, None), (1, Some("self"))], 1);
        let names = multimap(&[("self", &[1])]);
        let mut pres: Vec<Formula> = (0..4)
            .flat_map(|k| (0..4).map(move |f| format!("self.0[{k}].{f}")))
            .map(|n| float_field_bounded(&n, 1.0e30))
            .collect();
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert!(reasons.is_empty(), "16 chain bounds must be admitted (all-zeros): {reasons:?}");
        assert_eq!(pres.len(), 16);
    }

    // ---- Trust: compound float terms in the witness search ----

    /// A body whose params are genuine f64 locals (`Ty::Float` has no
    /// `witness_domain_for_ty` arm, so the vars take the unconstrained
    /// {0,±1,±2} candidate grid — the a3d difference-bound shape).
    fn f64_params_body(names: &[&str]) -> VerifiableBody {
        let mut locals =
            vec![trust_types::LocalDecl { index: 0, ty: trust_types::Ty::unit_ty(), name: None }];
        for (position, name) in names.iter().enumerate() {
            locals.push(trust_types::LocalDecl {
                index: position + 1,
                ty: trust_types::Ty::Float { width: 64 },
                name: Some((*name).to_string()),
            });
        }
        VerifiableBody {
            locals,
            blocks: Vec::new(),
            arg_count: names.len(),
            return_ty: trust_types::Ty::unit_ty(),
        }
    }

    #[test]
    fn difference_bound_witness_found() {
        // `(near) - (far) <= -1e-6` plus two-sided magnitude bounds — the
        // perspective_rh shape. The all-zeros probe fails (0-0 = 0 > -1e-6); the
        // odometer must find (near=0, far=1): Sub evaluates to -1.0 <= -1e-6 with
        // the new Sub arm. Without it the whole set dropped as NoSatisfiableWitness.
        let body = f64_params_body(&["near", "far"]);
        let names = multimap(&[("near", &[1]), ("far", &[2])]);
        let mut pres = vec![
            Formula::Le(
                Box::new(Formula::Sub(Box::new(float_var("near")), Box::new(float_var("far")))),
                Box::new(fp(-1.0e-6)),
            ),
            float_field_bounded("near", 1.0e15),
            float_field_bounded("far", 1.0e15),
        ];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert!(reasons.is_empty(), "difference bound must find a witness: {reasons:?}");
        assert_eq!(pres.len(), 3);
    }

    #[test]
    fn contradictory_difference_bound_dropped() {
        // SOUNDNESS twin: `(near) - (far) <= -1e-6 && near - far >= 1e-6` is
        // UNSATISFIABLE — the new Sub arm must not fabricate a witness; every
        // grid assignment fails one conjunct, so the set drops (fail-closed).
        let body = f64_params_body(&["near", "far"]);
        let names = multimap(&[("near", &[1]), ("far", &[2])]);
        let diff = || Formula::Sub(Box::new(float_var("near")), Box::new(float_var("far")));
        let mut pres = vec![Formula::And(vec![
            Formula::Le(Box::new(diff()), Box::new(fp(-1.0e-6))),
            Formula::Ge(Box::new(diff()), Box::new(fp(1.0e-6))),
        ])];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert_eq!(reasons, vec![AssumeSkipReason::NoSatisfiableWitness]);
        assert!(pres.is_empty());
    }

    #[test]
    fn unsat_float_predicate_still_dropped() {
        // SOUNDNESS twin (task-3c): `x <= -1.0 && x >= 1.0` has no model at all —
        // the widened float evaluator must still report NoSatisfiableWitness.
        let body = f64_params_body(&["x"]);
        let names = multimap(&[("x", &[1])]);
        let mut pres = vec![Formula::And(vec![
            Formula::Le(Box::new(float_var("x")), Box::new(fp(-1.0))),
            Formula::Ge(Box::new(float_var("x")), Box::new(fp(1.0))),
        ])];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert_eq!(reasons, vec![AssumeSkipReason::NoSatisfiableWitness]);
        assert!(pres.is_empty());
    }

    #[test]
    fn product_and_negated_difference_evaluate() {
        // Mul arm: `x * x >= 4.0` needs x = ±2 off the grid (zero fails).
        // Neg-over-compound: `-(near - far) >= 1e-6` is the mirrored difference
        // bound; Neg must recurse into the float-evaluated Sub.
        let body = f64_params_body(&["x"]);
        let names = multimap(&[("x", &[1])]);
        let mut pres = vec![Formula::Ge(
            Box::new(Formula::Mul(Box::new(float_var("x")), Box::new(float_var("x")))),
            Box::new(fp(4.0)),
        )];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert!(reasons.is_empty(), "x*x >= 4 must find x=±2: {reasons:?}");
        assert_eq!(pres.len(), 1);

        let body = f64_params_body(&["near", "far"]);
        let names = multimap(&[("near", &[1]), ("far", &[2])]);
        let mut pres = vec![Formula::Ge(
            Box::new(Formula::Neg(Box::new(Formula::Sub(
                Box::new(float_var("near")),
                Box::new(float_var("far")),
            )))),
            Box::new(fp(1.0e-6)),
        )];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert!(reasons.is_empty(), "-(near-far) >= 1e-6 must find a witness: {reasons:?}");
        assert_eq!(pres.len(), 1);
    }

    #[test]
    fn unsat_product_bound_dropped() {
        // SOUNDNESS twin: `x * x <= -1.0` — a real square is never negative; the
        // Mul arm must not fabricate a witness (NaN/rounding cannot help it).
        let body = f64_params_body(&["x"]);
        let names = multimap(&[("x", &[1])]);
        let mut pres = vec![Formula::Le(
            Box::new(Formula::Mul(Box::new(float_var("x")), Box::new(float_var("x")))),
            Box::new(fp(-1.0)),
        )];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert_eq!(reasons, vec![AssumeSkipReason::NoSatisfiableWitness]);
        assert!(pres.is_empty());
    }
}
