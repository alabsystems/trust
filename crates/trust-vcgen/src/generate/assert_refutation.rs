// Refutation of the assertion terminators rustc inserts, and of explicit
// `panic!` calls. The message text matters: a panic whose message matches a
// declared contract annotation is a contract obligation, not a stray panic.

use super::*;

/// Trust: locals whose value along any path is an UNCONSTRAINED function input,
/// so leaving them free in a path-feasibility formula is sound (no spurious SAT).
/// A local qualifies iff it is an ENTRY-STABLE parameter, or the result of the
/// narrow single-use payload-extractor admission below. A constant, a copy of an
/// input, or a discriminant is NOT independently free: its relationship to the
/// source value must be grounded by an exact definition. Otherwise a formula
/// mentioning both sides could choose inconsistent values and false-refute a safe
/// assertion. Any written/mutably escaped parameter is likewise excluded because
/// its post-write SSA versions no longer denote the bare entry input.
pub(super) struct LocalCounter {
    dense: Vec<usize>,
    overflow: FxHashMap<usize, usize>,
}

impl LocalCounter {
    #[inline]
    fn new(n_locals: usize) -> Self {
        Self { dense: vec![0; n_locals], overflow: Default::default() }
    }

    #[inline]
    fn inc(&mut self, local: usize) {
        if let Some(slot) = self.dense.get_mut(local) {
            *slot += 1;
        } else {
            *self.overflow.entry(local).or_insert(0) += 1;
        }
    }

    #[inline]
    fn get(&self, local: usize) -> usize {
        self.dense
            .get(local)
            .copied()
            .or_else(|| self.overflow.get(&local).copied())
            .unwrap_or(0)
    }

    fn for_each_nonzero(&self, mut f: impl FnMut(usize, usize)) {
        for (local, &count) in self.dense.iter().enumerate() {
            if count != 0 {
                f(local, count);
            }
        }
        for (&local, &count) in &self.overflow {
            if count != 0 {
                f(local, count);
            }
        }
    }
}

struct LocalFlagSet {
    dense: Vec<bool>,
    overflow: FxHashSet<usize>,
}

impl LocalFlagSet {
    #[inline]
    fn new(n_locals: usize) -> Self {
        Self { dense: vec![false; n_locals], overflow: Default::default() }
    }

    #[inline]
    fn insert(&mut self, local: usize) {
        if let Some(slot) = self.dense.get_mut(local) {
            *slot = true;
        } else {
            self.overflow.insert(local);
        }
    }

    #[inline]
    fn contains(&self, local: usize) -> bool {
        self.dense.get(local).copied().unwrap_or_else(|| self.overflow.contains(&local))
    }
}

pub(super) fn v2_input_free_locals(func: &VerifiableFunction) -> FxHashSet<usize> {
    // Entry-stable parameters (locals 1..=arg_count) are the base input-free set.
    // A parameter written anywhere in the body is NOT input-free under its base
    // name: the bare name denotes the entry value while a post-write `#s...`
    // version denotes the replacement. Treating every version as an arbitrary
    // input could make an opaque call destination spuriously SAT and false-refute
    // a safe assertion. Reuse the repository-wide exact collapse license, which
    // requires no statement/call-destination write and no mutable escape. The
    // payload-extractor lane below is the only additional admission.
    let mut safe: FxHashSet<usize> = (1..=func.body.arg_count)
        .filter(|&local| local_versions_collapse_to_bare(func, local))
        .collect();
    // Call-result-free admission requires at least one entry-stable parameter and
    // an empty `func.preconditions` list (see below). When either precondition fails,
    // no call destination can be admitted, so skip the whole-body read/borrow scan.
    if safe.is_empty()
        || !func.preconditions.is_empty()
        || !super::terminator_presence_for(func).has_bare_dest_call
    {
        return safe;
    }

    // First scan ONLY block terminators for allowlisted "free-payload extractor" calls
    // (`Try::branch(r)` / `<[T]>::get(s, i)`) and unanalyzable terminators (`Opaque` /
    // `Resume` / future variants). Most functions have no extractor calls and return
    // `safe` without walking statements.
    let mut payload_calls: Vec<(usize, Vec<usize>)> = Vec::new();
    for block in &func.body.blocks {
        match &block.terminator {
            Terminator::Call { func: callee, args, dest, .. } => {
                if dest.projections.is_empty() && !(1..=func.body.arg_count).contains(&dest.local) {
                    let tail = method_tail(callee);
                    let is_extractor = (tail == "branch" && callee.contains("Try"))
                        || (tail == "get" && callee.contains("slice"));
                    if is_extractor {
                        let arg_locals: Vec<usize> = args
                            .iter()
                            .filter_map(|a| match a {
                                Operand::Copy(p) | Operand::Move(p) => Some(p.local),
                                _ => None,
                            })
                            .collect();
                        payload_calls.push((dest.local, arg_locals));
                    }
                }
            }
            Terminator::SwitchInt { .. }
            | Terminator::Assert { .. }
            | Terminator::Drop { .. }
            | Terminator::Goto(_)
            | Terminator::Return
            | Terminator::Unreachable => {}
            // An `Opaque`/`Resume` (or any future) terminator may hide reads we cannot
            // see; if one is present we refuse all Call-result admission (conservative —
            // never undercount, which would be unsound).
            _ => return safe,
        }
    }
    if payload_calls.is_empty() {
        return safe;
    }

    // Read-count per local across EVERY operand/place position, to gate the
    // Call-result-free admission: an argument read ONLY in the allowlisted call
    // cannot decouple the call result from any other constraint.
    let n_locals = func.body.locals.len();
    let mut read_count = LocalCounter::new(n_locals);
    // Locals taken by `&mut` / `&raw` are NOT input-free: their value can be
    // reassigned through the borrow (`mem::swap(&mut a, ..)`, a setter, `*p = ..`)
    // WITHOUT a direct `Assign`, so a base-name input exemption could model a
    // STALE pre-mutation value and false-refute (the `&mut`/AddressOf
    // staleness class — see the hunt-5/7/8 lessons). Exclude their base locals.
    let mut mut_borrowed = LocalFlagSet::new(n_locals);
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            if let Statement::Assign { place, rvalue, .. } = stmt {
                if !place.projections.is_empty() {
                    // a projected store (`a.0 = ..`, `*a = ..`) mutates the base
                    // local's value WITHOUT a direct assign — exclude it from
                    // input-free outright (covers even a parameter, which the
                    // single-assignment rule would otherwise admit) so the
                    // post-mutation value is never modelled as a free leaf.
                    mut_borrowed.insert(place.local);
                }
                match rvalue {
                    // single operand or single place read (one local).
                    Rvalue::Use(Operand::Copy(p) | Operand::Move(p))
                    | Rvalue::UnaryOp(_, Operand::Copy(p) | Operand::Move(p))
                    | Rvalue::Cast(Operand::Copy(p) | Operand::Move(p), _)
                    | Rvalue::Repeat(Operand::Copy(p) | Operand::Move(p), _)
                    | Rvalue::Ref { mutable: false, place: p }
                    | Rvalue::Discriminant(p)
                    | Rvalue::Len(p)
                    | Rvalue::CopyForDeref(p) => read_count.inc(p.local),
                    // a `&mut` / raw `&raw` borrow READS and may MUTATE the base
                    // local through the borrow — exclude it from input-free.
                    Rvalue::Ref { mutable: true, place: p } | Rvalue::AddressOf(_, p) => {
                        read_count.inc(p.local);
                        mut_borrowed.insert(p.local);
                    }
                    Rvalue::BinaryOp(_, a, b)
                    | Rvalue::CheckedBinaryOp(_, a, b)
                    | Rvalue::UncheckedBinaryOp(_, a, b) => {
                        for op in [a, b] {
                            if let Operand::Copy(p) | Operand::Move(p) = op {
                                read_count.inc(p.local);
                            }
                        }
                    }
                    Rvalue::Aggregate(_, ops) => {
                        for op in ops {
                            if let Operand::Copy(p) | Operand::Move(p) = op {
                                read_count.inc(p.local);
                            }
                        }
                    }
                    // Constant/Symbolic/Unsupported operands read no tracked local.
                    _ => {}
                }
            }
        }
        match &block.terminator {
            Terminator::Call { args, .. } => {
                for op in args {
                    if let Operand::Copy(p) | Operand::Move(p) = op {
                        read_count.inc(p.local);
                    }
                }
            }
            Terminator::SwitchInt { discr, .. } => {
                if let Operand::Copy(p) | Operand::Move(p) = discr {
                    read_count.inc(p.local);
                }
            }
            Terminator::Assert { cond, .. } => {
                if let Operand::Copy(p) | Operand::Move(p) = cond {
                    read_count.inc(p.local);
                }
            }
            Terminator::Drop { place, .. } => read_count.inc(place.local),
            Terminator::Goto(_) | Terminator::Return | Terminator::Unreachable => {}
            _ => return safe,
        }
    }
    // Call-result-free admission: an allowlisted payload extractor whose every
    // arg is an input-free PARAMETER read ONLY in this call (so the result's
    // value is unconstrained elsewhere — no decoupling). A declared precondition
    // can constrain that otherwise-free argument without contributing a body
    // read (`requires(i < s.len())` before `s.get(i)`), in which case treating the
    // result as independent could manufacture a SAT witness. Decline the narrow
    // admission whenever any gated precondition is present; exact call/path
    // grounding remains available independently. Never re-admit a formal
    // parameter as its own post-call replacement; the versioned entry/replacement
    // relationship requires exact grounding, not a base-name exemption.
    for (dest, arg_locals) in &payload_calls {
        if (1..=func.body.arg_count).contains(dest)
            || !local_versions_collapse_to_bare(func, *dest)
            || safe.contains(dest)
            || mut_borrowed.contains(*dest)
        {
            continue;
        }
        let ok = !arg_locals.is_empty()
            && arg_locals.iter().all(|&a| {
                (1..=func.body.arg_count).contains(&a)
                    && safe.contains(&a)
                    && read_count.get(a) <= 1
            });
        if ok {
            safe.insert(*dest);
        }
    }
    safe
}

// ── EXACT PINS FOR A COMPONENT OF AN INPUT-FREE PLACE ────────────────────────
// `3d1446f4c7` ("ground constrained assert inputs") and `e6fae3f5be` ("require
// exact refutation path guards") deliberately stopped admitting a copy /
// constant / discriminant / payload read as INDEPENDENTLY free, and requisitioned
// an EXACT DEFINITION in its place. These three helpers plus
// `input_free_component_names` / `discriminant_pin_defs` supply exactly that for
// the two shapes the requisition left uncovered — an `@variant.field` projection
// of an entry-stable parameter, and the `Discriminant` temp of one — WITHOUT
// re-opening the base-name exemption those commits closed. Nothing here admits a
// COMPUTED value: every admission below is a *component of an unconstrained
// input*, which is what "input-free" has always meant.

/// Split a formula variable name into its place ROOT and its projection SEGMENTS.
///
/// `place_to_var_name` spells a place as `base ++ segments` and ENFORCES that
/// every segment begins with a [`crate::PROJECTION_SEGMENT_LEAD`] character while
/// no base contains one (see the base/segment-boundary invariant on that
/// function). The decode is therefore exact rather than a guess: the root is the
/// prefix up to the first lead character, and each segment runs from one lead
/// character to the next. The `#sN_M` reaching-def token is stripped first — it is
/// a version of the WHOLE name, appended after the segments by
/// `version_rename_at`.
#[derive(Clone, Copy)]
struct PlaceNameSegments<'a> {
    rest: &'a str,
}

impl<'a> PlaceNameSegments<'a> {
    fn is_empty(&self) -> bool {
        self.rest.is_empty()
    }
}

impl<'a> Iterator for PlaceNameSegments<'a> {
    type Item = &'a str;

    fn next(&mut self) -> Option<Self::Item> {
        let bytes = self.rest.as_bytes();
        if bytes.is_empty() {
            return None;
        }
        if let Some(rel) = bytes[1..].iter().copied().position(crate::is_projection_segment_lead) {
            let (seg, rem) = self.rest.split_at(1 + rel);
            self.rest = rem;
            return Some(seg);
        }
        let seg = self.rest;
        self.rest = "";
        Some(seg)
    }
}

fn place_name_root_and_segments(v: &str) -> (&str, PlaceNameSegments<'_>) {
    let bare = match v.as_bytes().iter().position(|&b| b == b'#') {
        Some(pos) => &v[..pos],
        None => v,
    };
    let Some(first) = bare.bytes().position(crate::is_projection_segment_lead) else {
        return (bare, PlaceNameSegments { rest: "" });
    };
    let (root, rest) = bare.split_at(first);
    (root, PlaceNameSegments { rest })
}

/// The place ROOT of a formula variable name — the local whose storage it names.
fn place_name_root(v: &str) -> &str {
    let bare = match v.as_bytes().iter().position(|&b| b == b'#') {
        Some(pos) => &v[..pos],
        None => v,
    };
    match bare.bytes().position(crate::is_projection_segment_lead) {
        Some(first) => &bare[..first],
        None => bare,
    }
}

/// A `.k` FIELD segment (`.0`, `.1`, …) — the ONLY segment spelling for which this
/// lane claims two differing siblings denote DISJOINT storage.
fn segment_is_field(segment: &str) -> bool {
    segment
        .strip_prefix('.')
        .is_some_and(|k| !k.is_empty() && k.bytes().all(|b| b.is_ascii_digit()))
}

/// The pseudo-segment a `Discriminant` carrier is re-spelled with for the alias
/// guard. It must be a spelling `place_to_var_name` can never mint, or a real
/// projection would be mistaken for a tag: the `@`-led segments that function
/// emits are `@<digits>` (`Downcast`), `@opaque_cast`, `@unwrap_unsafe_binder`
/// and the future-variant wildcard's `@unknown`, and the `__trust_` prefix is the
/// reserved generated-metadata boundary none of them can cross.
const DISCRIMINANT_PSEUDO_SEGMENT: &str = "@__trust_discr";

/// Do two DISTINCT formula variable names denote storage that can OVERLAP?
///
/// This is the guard that keeps `3d1446f4c7`'s closed false-refutation channel
/// closed. Two names that may denote overlapping storage must never BOTH be free
/// in one path-feasibility formula: a model could then choose inconsistent values
/// for one value's whole and its part (`o` = `None` while `o@1.0.0` = 5) and
/// SAT — a refutation of a program no input can drive to the panic.
///
/// It is deliberately NOT [`crate::generate::path_defs::place_names_overlap`]:
/// that predicate's descendant test admits only `.`, `[` and `*` as boundary
/// characters, so it reads `o` and `o@1.0` as UNRELATED. Here the whole
/// [`crate::PROJECTION_SEGMENT_LEAD`] set is a boundary, and every divergence
/// except a differing FIELD index counts as an overlap:
///
///   * a differing `@V` DOWNCAST — two variants of one enum share storage, so
///     `o@1.0` and `o@2.0` are the same bytes read two ways;
///   * a differing `[i]` INDEX — a symbolic index may equal another;
///   * a differing `*` / `@opaque_cast` / any future segment — unknown, refused.
///
/// Equal names are the SAME variable, not two, so they are not an overlap.
/// Distinct FIELD indices of one parent are disjoint storage — but ONLY because
/// `input_free_component_names` refuses to admit any component of a root whose
/// type tree contains a `union`, whose fields DO overlap. That gate and this arm
/// are the two halves of one argument; neither is sound without the other.
fn refutation_names_may_alias(a: &str, b: &str) -> bool {
    if a == b || place_name_root(a) != place_name_root(b) {
        return false;
    }
    let (_, mut a_segments) = place_name_root_and_segments(a);
    let (_, mut b_segments) = place_name_root_and_segments(b);
    loop {
        match (a_segments.next(), b_segments.next()) {
            (Some(a_segment), Some(b_segment)) => {
                if a_segment != b_segment {
                    // The TAG is a component of the enum value that no variant's payload
                    // contains, so a divergence into it is a divergence into disjoint
                    // storage — the one non-field spelling this predicate calls disjoint,
                    // and it is synthetic (see `DISCRIMINANT_PSEUDO_SEGMENT`), never a
                    // place spelling a body can read.
                    if a_segment == DISCRIMINANT_PSEUDO_SEGMENT
                        || b_segment == DISCRIMINANT_PSEUDO_SEGMENT
                    {
                        return false;
                    }
                    return !(segment_is_field(a_segment) && segment_is_field(b_segment));
                }
            }
            // One segment path is a proper prefix of the other: an ancestor and its
            // descendant, which always overlap. (Equal paths under equal roots cannot
            // reach here — the names would have been equal.)
            (Some(_), None) | (None, Some(_)) => return true,
            (None, None) => return false,
        }
    }
}

/// The name a `Discriminant` PIN speaks about, re-spelled as a projection of the
/// place it reads, so [`refutation_names_may_alias`] can judge it on the same
/// footing as a payload projection: `__trust_mir__discr_o` becomes
/// `o@__trust_discr`.
///
/// A tag and a payload are DISJOINT components of one enum value (the tag says
/// which payload is live; it is not part of it), so the carrier must not be
/// reported as aliasing `o@1.0`. It DOES alias the bare root `o`, which is the
/// case that matters — a model free to pick `o` and `discr(o)` independently is
/// exactly the inconsistency this guard exists to refuse.
fn discriminant_carrier_as_projection(v: &str) -> Option<String> {
    let bare = v.split('#').next().unwrap_or(v);
    let place = bare.strip_prefix("__trust_mir__discr_")?;
    Some(format!("{place}{DISCRIMINANT_PSEUDO_SEGMENT}"))
}

/// Whether `name` is a discriminant carrier or has a projection segment.
/// [`refutation_names_may_alias`] returns `false` whenever both operands have no
/// projection segments (after [`discriminant_carrier_as_projection`]), so a
/// conjunction containing no such name cannot contain an aliasing pair.
#[inline]
pub(super) fn refutation_name_has_projection_or_discr(name: &str) -> bool {
    name.starts_with("__trust_mir__discr_")
        || name
            .split('#')
            .next()
            .unwrap_or(name)
            .bytes()
            .any(crate::is_projection_segment_lead)
}

/// Collect the unique free variable names of `formula` into a `Vec<String>` in
/// deterministic traversal order without allocating an intermediate `HashSet`.
#[inline]
pub(super) fn formula_free_var_vec(formula: &Formula) -> Vec<String> {
    let mut out = Vec::new();
    trust_types::for_each_free_variable_name(formula, &mut |name| {
        if !out.iter().any(|s| s == name) {
            out.push(name.to_string());
        }
    });
    out
}

/// [`refutation_names_may_alias`] with both operands first re-spelled through
/// [`discriminant_carrier_as_projection`], so a discriminant carrier participates
/// in the guard as the TAG component of the place it reads.
fn refutation_names_may_alias_with_discriminants(a: &str, b: &str) -> bool {
    let a_spelled = discriminant_carrier_as_projection(a);
    let b_spelled = discriminant_carrier_as_projection(b);
    refutation_names_may_alias(a_spelled.as_deref().unwrap_or(a), b_spelled.as_deref().unwrap_or(b))
}

/// Does this type's (finite, extraction-flattened) tree contain a `union`?
///
/// A union's fields OVERLAP at byte offset 0 (`AdtKind::Union`'s own doc), so the
/// "distinct `.k` field indices are disjoint storage" arm of
/// [`refutation_names_may_alias`] is operationally FALSE inside one. `Ty::Adt`
/// erases the struct/union distinction unless `trust-mir-extract` stamped
/// `adt_kind`, so an ABSENT stamp is treated as a possible union — fail-closed,
/// exactly like the field-setter frame surface's G-STRUCT-KIND gate. The walk is
/// depth-bounded because a recursive ADT is cut to a by-name `Ty::Datatype`
/// marker at extraction; exhausting the budget also reads as "may contain a
/// union".
fn ty_tree_may_contain_union(ty: &Ty, depth: u32) -> bool {
    if depth == 0 {
        return true;
    }
    match ty {
        Ty::Adt { fields, variants, adt_kind, .. } => {
            if !matches!(adt_kind, Some(trust_types::AdtKind::Struct | trust_types::AdtKind::Enum))
            {
                return true;
            }
            fields.iter().any(|(_, field)| ty_tree_may_contain_union(field, depth - 1))
                || variants.iter().any(|variant| {
                    variant.fields.iter().any(|(_, f)| ty_tree_may_contain_union(f, depth - 1))
                })
        }
        Ty::Tuple(elements) => {
            elements.iter().any(|element| ty_tree_may_contain_union(element, depth - 1))
        }
        Ty::Array { elem, .. }
        | Ty::SymArray { elem, .. }
        | Ty::Slice { elem }
        | Ty::Seq { elem, .. } => ty_tree_may_contain_union(elem, depth - 1),
        // A reference/pointer LEAF is not walked through: no component name this
        // lane admits crosses a `Deref` (see `input_free_component_names`), so the
        // pointee's shape cannot reach the field-disjointness arm.
        Ty::Ref { .. } | Ty::RawPtr { .. } => false,
        // Scalars and by-name datatype back-references carry no field structure a
        // `.k` segment could name. A `Ty::Datatype` is a back-reference whose
        // definition is NOT in hand, so it is refused.
        Ty::Datatype { .. } => true,
        _ => false,
    }
}

/// The formula names of PLACE COMPONENTS of an input-free root — the first of the
/// two exact pins.
///
/// A projection of an entry-stable parameter IS that parameter's storage: the
/// parameter is an unconstrained input, so each of its components ranges freely
/// with it, and a SAT model that assigns the components describes a real argument
/// value. That is the SAME property `safe_names` asserts for the whole place, read
/// one component down; it is not the base-name exemption `3d1446f4c7` removed,
/// which admitted a COMPUTED local because its single defining read happened to
/// mention an input.
///
/// Admission is by PLACE OCCURRENCE, never by string shape: only a place that
/// literally appears in this body is admitted, and its name is minted by the one
/// canonical `place_to_var_name`. That mint is also why the ROOT is read back off
/// the minted NAME rather than from `place.local` — `canonicalize_place` rebases a
/// place onto the storage it aliases, so the temp `_3` holding `o`'s `Some`
/// payload spells `_3.0` as `o@1.0.0`, and it is the rebased root whose freedom
/// and whose type are the relevant facts.
///
/// Fail-closed gates, each of which drops a refutation and can never create one:
///
///  * the minted name's ROOT must be an input-free whole place (`safe_names`);
///  * the name must carry at least one projection segment — a whole place is
///    already `safe_names`' business;
///  * no segment may be a `*` DEREF: a pointee is reached through a reference and
///    two references may alias, so the "components of one value" argument does not
///    hold across one;
///  * the root's type tree must be union-free ([`ty_tree_may_contain_union`]), or
///    the sibling-field disjointness [`refutation_names_may_alias`] claims is
///    false. A root name that resolves to no unique local is refused outright.
fn input_free_component_names(
    func: &VerifiableFunction,
    input_free: &FxHashSet<usize>,
    safe_names: &FxHashSet<String>,
) -> FxHashSet<String> {
    if safe_names.is_empty() {
        return FxHashSet::default();
    }
    // Root NAME -> the input-free local it denotes, so the union gate can read the
    // root's declared type after canonicalization rebased the place. A name shared
    // by two input-free locals would be ambiguous; `place_to_var_name` already
    // demotes a shared source name to the unique `_<local>` spelling, but the map
    // is built fail-closed anyway (a duplicate poisons the entry).
    let mut root_local: FxHashMap<&str, Option<usize>> = FxHashMap::default();
    let mut root_names: Vec<(String, usize)> = Vec::with_capacity(input_free.len());
    for &local in input_free {
        if local < func.body.locals.len() {
            root_names.push((crate::place_to_var_name(func, &Place::local(local)), local));
        }
    }
    for (name, local) in &root_names {
        root_local.entry(name.as_str()).and_modify(|slot| *slot = None).or_insert(Some(*local));
    }
    let union_free_roots: FxHashSet<&str> = root_local
        .into_iter()
        .filter_map(|(root, local)| {
            let local = local?;
            let ty = crate::local_ty_ref(func, local)?;
            (!ty_tree_may_contain_union(ty, 8)).then_some(root)
        })
        .collect();
    if union_free_roots.is_empty() {
        return FxHashSet::default();
    }
    let mut admitted: FxHashSet<String> = FxHashSet::default();
    let consider = |place: &Place, admitted: &mut FxHashSet<String>| {
        if place.projections.is_empty() {
            return;
        }
        let name = crate::place_to_var_name(func, place);
        if safe_names.contains(&name) {
            return;
        }
        let (root, mut segments) = place_name_root_and_segments(&name);
        if segments.is_empty() || !safe_names.contains(root) || !union_free_roots.contains(root) {
            return;
        }
        if segments.any(|segment| segment.starts_with('*')) {
            return;
        }
        admitted.insert(name);
    };
    let visit_operand = |operand: &Operand, admitted: &mut FxHashSet<String>| {
        if let Operand::Copy(place) | Operand::Move(place) = operand {
            consider(place, admitted);
        }
    };
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            let Statement::Assign { rvalue, .. } = stmt else { continue };
            match rvalue {
                Rvalue::Use(op)
                | Rvalue::UnaryOp(_, op)
                | Rvalue::Cast(op, _)
                | Rvalue::Repeat(op, _) => visit_operand(op, &mut admitted),
                Rvalue::BinaryOp(_, a, b)
                | Rvalue::CheckedBinaryOp(_, a, b)
                | Rvalue::UncheckedBinaryOp(_, a, b) => {
                    visit_operand(a, &mut admitted);
                    visit_operand(b, &mut admitted);
                }
                Rvalue::Aggregate(_, ops) => {
                    for op in ops {
                        visit_operand(op, &mut admitted);
                    }
                }
                Rvalue::Ref { place, .. }
                | Rvalue::AddressOf(_, place)
                | Rvalue::Discriminant(place)
                | Rvalue::Len(place)
                | Rvalue::CopyForDeref(place) => consider(place, &mut admitted),
                _ => {}
            }
        }
        match &block.terminator {
            Terminator::Call { args, .. } => {
                for arg in args {
                    visit_operand(arg, &mut admitted);
                }
            }
            Terminator::SwitchInt { discr, .. } => visit_operand(discr, &mut admitted),
            Terminator::Assert { cond, .. } => visit_operand(cond, &mut admitted),
            _ => {}
        }
    }
    admitted
}

/// The second exact pin: `dest == __trust_mir__discr_<src>` for a `Discriminant`
/// read of an INPUT-FREE place, plus that carrier's own variant-tag membership.
///
/// `3d1446f4c7` correctly stopped calling the destination of a `Discriminant`
/// read independently free — the tag and the value it is read from must not float
/// apart — and said its relationship to the source "must be grounded by an exact
/// definition". This IS that definition. The carrier is minted by the ONE
/// canonical [`crate::discriminant_formula_var_name`], the same spelling the CHC
/// lowering and `build_discriminant_variant_range_facts` use, so the pin cannot
/// drift into a private name that silently binds nothing.
///
/// Why the carrier may be left FREE: `src` is an entry-stable, never-written
/// parameter (or an admitted payload-extractor result), so `discriminant(src)` is
/// a single value fixed by an unconstrained input — a COMPONENT of that input, in
/// exactly the sense [`input_free_component_names`] uses, not a computed value.
///
/// Why the range rides along: with the tag unconstrained a model could pick a
/// PHANTOM tag matching no variant and satisfy a path guard no execution can take
/// — a false refutation. The membership is the enum's own type invariant read
/// from its `VariantDef`s (the inhabited ones: `inhabited_enum_variant_tag_set`
/// drops a variant with an uninhabited payload, which rustc's own lowering has
/// already dropped from the switch), so it deletes only impossible models. It is
/// attached as a RANGE fact, so the fixpoint conjoins it exactly when it conjoins
/// the pin.
///
/// Fail-closed gates:
///
///  * `src` must be a WHOLE input-free place — a projected source would need the
///    component admission's own gates, and no fixture needs it;
///  * the tag set must be derivable and NON-EMPTY: an empty membership is `false`,
///    which would make every path vacuously UNSAT — the mirror-image accident
///    `build_discriminant_variant_range_facts` also refuses explicitly;
///  * `dest` must be a whole local that is SINGLE-ASSIGNMENT in the whole function
///    and not mutably escaped (`stable_dest_names`, which the caller builds with
///    exactly the `stmt_defs` discipline). That is what makes the use-point-
///    versioned equality a true function-wide fact rather than a claim about one
///    snapshot;
///  * every tag must DENOTE a value the read can produce in `dest`
///    (`value_facts::discriminant_tags_denote_dest_values`): a negative tag under an
///    unsigned `dest` is the lossy spelling of a `#[repr(u128)]` tag above
///    `i128::MAX` (REPR-U128-HIGH-TAG-1).
///
/// `pub(super)` only so `uninhabited_variant_tests` can pin the last gate.
pub(super) fn discriminant_pin_defs(
    func: &VerifiableFunction,
    input_free: &FxHashSet<usize>,
    stable_dest_names: &FxHashSet<String>,
) -> Vec<(Formula, Vec<Formula>, String)> {
    if input_free.is_empty() || stable_dest_names.is_empty() {
        return Vec::new();
    }
    let mut pins: Vec<(Formula, Vec<Formula>, String)> = Vec::new();
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            let Statement::Assign { place: dest, rvalue: Rvalue::Discriminant(src), .. } = stmt
            else {
                continue;
            };
            if !dest.projections.is_empty()
                || !src.projections.is_empty()
                || !input_free.contains(&src.local)
            {
                continue;
            }
            let dest_name = crate::place_to_var_name(func, dest);
            if !stable_dest_names.contains(&dest_name) {
                continue;
            }
            // Resolved through the datatype table, exactly as the global tag-set fact
            // is: a recursive enum's local is a bare by-name marker.
            let Some(src_ty) = crate::place_ty_resolved_cow(func, src) else { continue };
            let Some(tags) = super::value_facts::inhabited_enum_variant_tag_set(src_ty.as_ref())
            else {
                continue;
            };
            if tags.is_empty() {
                continue;
            }
            // Trust (REPR-U128-HIGH-TAG-1, defense in depth): no pin when a tag does
            // not denote a value this read can produce — a negative tag under an
            // unsigned `dest`, the lossy spelling of a `#[repr(u128)]` tag above
            // `i128::MAX` in a serialized or hand-built body. The membership would
            // delete the real tag (the switch label renders `u128::MAX`), and the pin
            // `dest == carrier` would carry that false range onto `dest`. Same rule,
            // same helper, as the global tag-set fact.
            if !super::value_facts::discriminant_tags_denote_dest_values(func, dest, &tags) {
                continue;
            }
            let carrier =
                crate::discriminant_formula_var_name(&crate::place_to_var_name(func, src));
            let carrier_var = Formula::Var(carrier.clone(), Sort::Int);
            let range = if let [tag] = tags.as_slice() {
                Formula::Eq(Box::new(carrier_var.clone()), Box::new(Formula::Int(*tag)))
            } else {
                Formula::Or(
                    tags.iter()
                        .map(|&tag| {
                            Formula::Eq(Box::new(carrier_var.clone()), Box::new(Formula::Int(tag)))
                        })
                        .collect(),
                )
            };
            pins.push((
                Formula::Eq(Box::new(Formula::Var(dest_name, Sort::Int)), Box::new(carrier_var)),
                vec![range],
                carrier,
            ));
        }
    }
    pins
}

/// Trust: `-full`-only, refute-only path-feasibility VCs for user `assert!` /
/// `panic!` failure sites.
///
/// For each panic-call terminator block, build the path-feasibility formula — the
/// conjunction of branch guards reaching that block, which (since the block is
/// entered exactly when the assertion FAILS) IS the violation condition. Emit it
/// ONLY when every free variable is INPUT-FREE (`v2_input_free_locals`): an
/// entry-stable parameter or a narrowly admitted single-use payload-extractor
/// result. Then an ay SAT verdict is a genuine
/// counterexample (a real input drives execution to the panic). A panic site
/// whose reachability depends on a COMPUTED intermediate (e.g. a `clamp` value
/// merged across blocks, or a `s.get(i)` call result) is EXCLUDED — its defining
/// computation is not threaded here, so leaving it free could be spuriously SAT
/// and false-refute a guarded-safe assert. Excluding it is sound (the obligation
/// simply stays runtime-checked), never a false refutation.
///
/// Returned SEPARATELY from `generate_vcs` and consumed ONLY by the strict
/// `-full` path (see `refute_full_assert_obligations`), so DEFAULT mode never
/// sees these: a reachable `assert!` panic is valid, drop-in Rust and must stay
/// runtime-checked by default. Refute-only: the caller acts on an ay `Failed`
/// (SAT) and discards everything else, so it can never turn into a proof.
/// Trust: model a defined-behavior `wrapping_{add,sub}` method Call as an EXACT
/// modular DEFINITION of its destination, so an `assert!` whose condition compares
/// the result can GROUND and be decided (otherwise the result temp — a
/// `Terminator::Call` dest, invisible to the statement-based block-definition
/// extractor — stays an unconstrained free var and the obligation is dropped as
/// ungrounded, falling back to runtime-checked).
///
/// Unlike `overflow_arith_call` (UB-on-overflow intrinsics that carry an
/// obligation), `wrapping_*` wraps by definition and needs no obligation. The
/// model is the single-`Ite` modular reduction at the operand width, kept in
/// Int/LIA so ay decides it directly:
///   `wrapping_add(a,b) == ite(a+b >= 2^w, a+b - 2^w, a+b)`
///   `wrapping_sub(a,b) == ite(a-b <  0,   a-b + 2^w, a-b)`
/// This is FAITHFUL: the unsound unbounded `a+b` would false-PROVE
/// `assert!(a.wrapping_add(1) > a)` at `a == MAX` (where the real result wraps to
/// 0). Returns `(Eq(dest, ite), operand-range facts)`; the caller conjoins the
/// ranges only when the def is used, so the refute direction cannot pick an
/// out-of-range operand and spuriously fail a valid assert. add/sub at width <= 64
/// (u8..=u64 / i8..=i64 / usize / isize), BOTH unsigned (single-Ite reduction) and
/// signed (two's-complement two-sided wrap); `mul` (full nonlinear mod) and wider
/// types (u128/i128) return `None`, leaving such asserts ungrounded (sound:
/// dropped, never mis-decided).
/// The bitvector op and carrier carried by an authenticated
/// `wrapping_{add,sub}` marker. Raw method suffixes are deliberately rejected:
/// they are source-spellable and therefore cannot establish call identity.
fn authenticated_wrapping_call(
    callee: &str,
) -> Option<(BinOp, trust_types::RustcWrappingRefutationCarrier)> {
    if callee.starts_with(trust_types::TRUST_RUSTC_TOTAL_PRIMITIVE_METHOD_PATH_PREFIX) {
        // TG14: signed E6 arithmetic uses this same authenticated marker.
        // Preserve its exact signed modular refutation model when extraction
        // selects the broader tree lane instead of the refutation-only stamp.
        let (op, ty) = trust_types::e6_expr::tree::wrapping_primitive(callee)?;
        let Ty::Int { width, signed } = ty else {
            return None;
        };
        return matches!(op, BinOp::Add | BinOp::Sub)
            .then_some((op, trust_types::RustcWrappingRefutationCarrier::Fixed { width, signed }));
    }
    let method = trust_types::RustcWrappingRefutationMethod::classify(callee)?;
    let op = match method.op {
        trust_types::RustcWrappingRefutationOp::Add => BinOp::Add,
        trust_types::RustcWrappingRefutationOp::Sub => BinOp::Sub,
        // Full nonlinear mod is outside this Int/LIA model — exactly the
        // `WrappingMul(_) => None` decision the total-marker arm above already
        // records. A mul-marked callee's destination stays ungrounded and the
        // obligation is dropped as such (sound: runtime-checked, never
        // mis-decided). The TrustIr bridge, not this lane, carries mul's
        // defining modular semantics.
        trust_types::RustcWrappingRefutationOp::Mul => return None,
    };
    Some((op, method.carrier))
}

pub(super) fn wrapping_call_tail_op(callee: &str) -> Option<BinOp> {
    authenticated_wrapping_call(callee).map(|(op, _)| op)
}

fn wrapping_carrier_destination(
    carrier: trust_types::RustcWrappingRefutationCarrier,
    destination: &Ty,
) -> Option<(u32, bool)> {
    match (carrier, destination) {
        (
            trust_types::RustcWrappingRefutationCarrier::Fixed {
                width: expected_width,
                signed: expected_signed,
            },
            Ty::Int { width, signed },
        ) if *width == expected_width && *signed == expected_signed => Some((*width, *signed)),
        (
            trust_types::RustcWrappingRefutationCarrier::PointerSized { signed: expected_signed },
            Ty::PtrSizedInt { signed },
        ) if *signed == expected_signed => Some((destination.int_width()?, *signed)),
        // The production verifier extraction lane still carries usize/isize as
        // its pinned 64-bit `Ty::Int` representation. The compiler-authenticated
        // marker retains the lost pointer-sized identity; accepting that one
        // legacy spelling preserves existing source precision. Fixed u64/i64
        // and pointer-sized arithmetic have identical modular semantics at this
        // width. Faithful serialized IR uses `PtrSizedInt` and is checked by the
        // exact arm above.
        (
            trust_types::RustcWrappingRefutationCarrier::PointerSized { signed: expected_signed },
            Ty::Int { width: 64, signed },
        ) if *signed == expected_signed => Some((64, *signed)),
        _ => None,
    }
}

/// Whether a width-less signed literal's `value` is representable at `width` bits.
/// Shared with `guards::bare_binop_machine_shape` (BARE-BINOP-LITERAL-LHS-WIDTH-1).
pub(crate) fn signed_constant_fits_width(value: i128, width: u32) -> bool {
    if width == 128 {
        return true;
    }
    if !(1..128).contains(&width) {
        return false;
    }
    let bound = 1i128 << (width - 1);
    (-bound..bound).contains(&value)
}

/// Whether an unsigned literal's `value` is representable at `width` bits.
/// Shared with `guards::bare_binop_machine_shape` (BARE-BINOP-LITERAL-LHS-WIDTH-1).
pub(crate) fn unsigned_constant_fits_width(value: u128, width: u32) -> bool {
    (1..=128).contains(&width) && (width == 128 || value < (1u128 << width))
}

fn wrapping_operand_matches_destination(
    func: &VerifiableFunction,
    operand: &Operand,
    destination: &Ty,
    width: u32,
    signed: bool,
) -> bool {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => {
            crate::place_ty_cow(func, place).is_some_and(|actual| actual.as_ref() == destination)
        }
        // MIR integer constants retain their value but signed constants do not
        // retain their narrow width, and legacy usize constants retain only the
        // pinned target width. Validate representability against the
        // authenticated destination rather than fabricating i64/u64 identity.
        Operand::Constant(ConstValue::Int(value)) if signed => {
            signed_constant_fits_width(*value, width)
        }
        Operand::Constant(ConstValue::Uint(value, encoded_width)) if !signed => {
            *encoded_width == width && unsigned_constant_fits_width(*value, width)
        }
        // Typed opaque/const-param values still carry exact type metadata.
        _ => crate::operand_ty_cow(func, operand)
            .is_some_and(|actual| actual.as_ref() == destination),
    }
}

/// Trust: THE wrapping-arithmetic value encoding — the modular reduction of a
/// machine `Add`/`Sub` at `width` bits, kept in Int/LIA so ay decides it
/// directly. This is the ONE constructor of that encoding; every lane that
/// models a wrapping op routes through it so the same operation can never be
/// encoded two ways in one solver query (which can manufacture or destroy
/// models):
///   * the marker-authenticated `wrapping_{add,sub}` CALL model
///     (`wrapping_call_assert_model`), and
///   * the bare `Rvalue::BinaryOp(Add|Sub)` STATEMENT model
///     (`guards::extract_block_definitions*`) — the form the MIR inliner
///     leaves at -O when it dissolves the call, and the form all user
///     arithmetic takes in an overflow-checks-off session. MIR defines the
///     plain integer binop as wrapping; the extractor keeps the checked
///     (`CheckedBinaryOp`) and UB (`UncheckedBinaryOp`) forms distinct
///     (`trust-mir-extract convert_supported_binop`), so a bare `BinaryOp`
///     IS the wrapping case with no session bit to consult.
///
/// Unsigned: single-Ite reduction (`ite(a+b >= 2^w, a+b - 2^w, a+b)` /
/// `ite(a-b < 0, a-b + 2^w, a-b)`). Signed: two's-complement two-sided wrap
/// (`ite(s > max, s - 2^w, ite(s < min, s + 2^w, s))` — the sum/difference of
/// two in-range values wraps AT MOST ONCE past either bound). Both are exact
/// on in-range operands; callers conjoin the operands' type-range facts so
/// the refute direction cannot pick an out-of-range operand.
///
/// Refusals (`None`, fail-closed — the value stays havocked/ungrounded,
/// never mis-modeled):
///   * `Mul` — a single Ite is WRONG for mul (it can wrap many times), and
///     the full nonlinear modular reduction is not decidable in this lane;
///     matches the call form's `WrappingMul => None` boundary.
///   * `width` outside `1..=64` — the modulus `1i128 << width` must stay
///     within i128; u128/i128 wrapping stays unhandled.
///   * every op other than `Add`/`Sub`.
pub(crate) fn wrapping_binop_modular_ite(
    op: BinOp,
    lhs_f: &Formula,
    rhs_f: &Formula,
    width: u32,
    signed: bool,
) -> Option<Formula> {
    if !(1..=64).contains(&width) {
        return None;
    }
    let modulus = Formula::Int(1i128 << width);
    let s = match op {
        BinOp::Add => Formula::Add(Box::new(lhs_f.clone()), Box::new(rhs_f.clone())),
        BinOp::Sub => Formula::Sub(Box::new(lhs_f.clone()), Box::new(rhs_f.clone())),
        _ => return None,
    };
    Some(if signed {
        // Two's-complement wrap into [min, max]: the sum/difference of two in-range
        // signed values lands in [2*min, 2*max] (add) / [min-max, max-min] (sub),
        // so it wraps AT MOST ONCE past either bound. `ite(s>max, s-2^w, ite(s<min,
        // s+2^w, s))` is faithful; range facts (signed) keep both operands in band.
        let max = crate::range::type_max_formula(width, true);
        let min = crate::range::type_min_formula(width, true);
        Formula::Ite(
            Box::new(Formula::Gt(Box::new(s.clone()), Box::new(max))),
            Box::new(Formula::Sub(Box::new(s.clone()), Box::new(modulus.clone()))),
            Box::new(Formula::Ite(
                Box::new(Formula::Lt(Box::new(s.clone()), Box::new(min))),
                Box::new(Formula::Add(Box::new(s.clone()), Box::new(modulus))),
                Box::new(s),
            )),
        )
    } else {
        // Unsigned single-Ite reduction at the operand width.
        match op {
            BinOp::Add => Formula::Ite(
                Box::new(Formula::Ge(Box::new(s.clone()), Box::new(modulus.clone()))),
                Box::new(Formula::Sub(Box::new(s.clone()), Box::new(modulus))),
                Box::new(s),
            ),
            // wrapping_sub unsigned: borrow when the difference goes negative.
            _ => Formula::Ite(
                Box::new(Formula::Lt(Box::new(s.clone()), Box::new(Formula::Int(0)))),
                Box::new(Formula::Add(Box::new(s.clone()), Box::new(modulus))),
                Box::new(s),
            ),
        }
    })
}

pub(super) fn wrapping_call_assert_model(
    func: &VerifiableFunction,
    callee: &str,
    args: &[Operand],
    dest: &Place,
    has_normal_return_target: bool,
    has_atomic_metadata: bool,
    is_foreign: bool,
    is_unsafe_sig: bool,
) -> Option<(Formula, Vec<Formula>)> {
    // The marker authenticates the selected DefId, not independently mutable
    // call-site metadata. A modular destination definition is valid only for
    // the ordinary safe Rust call shape that the compiler actually extracted.
    // `unwind` is deliberately not a gate: the authenticated method is total,
    // and this refutation CFG follows only the normal-return target; rustc may
    // retain an unreachable `Continue`/cleanup annotation on such a call.
    if !has_normal_return_target || has_atomic_metadata || is_foreign || is_unsafe_sig {
        return None;
    }
    let (op, carrier) = authenticated_wrapping_call(callee)?;
    if args.len() != 2 {
        return None;
    }
    let lhs = args.first()?;
    let rhs = args.get(1)?;
    let dest_ty = crate::place_ty_cow(func, dest)?;
    let (width, signed) = wrapping_carrier_destination(carrier, dest_ty.as_ref())?;
    if !wrapping_operand_matches_destination(func, lhs, dest_ty.as_ref(), width, signed)
        || !wrapping_operand_matches_destination(func, rhs, dest_ty.as_ref(), width, signed)
    {
        return None;
    }
    let lhs_f = operand_to_formula(func, lhs);
    let rhs_f = operand_to_formula(func, rhs);
    let dest_var = Formula::Var(crate::place_to_var_name(func, dest), Sort::Int);
    let ite = wrapping_binop_modular_ite(op, &lhs_f, &rhs_f, width, signed)?;
    let def = Formula::Eq(Box::new(dest_var), Box::new(ite));
    let ranges = vec![
        crate::range::input_range_constraint(&lhs_f, width, signed),
        crate::range::input_range_constraint(&rhs_f, width, signed),
    ];
    Some((def, ranges))
}

fn wrapping_result_local_is_stable(
    func: &VerifiableFunction,
    dest: &Place,
    call_def_count: usize,
) -> bool {
    dest.projections.is_empty()
        && call_def_count == 1
        // Counting call destinations alone is insufficient: a statement write
        // on another path or mutation through `&mut` can give the assertion's
        // reaching version a value unrelated to this wrapping call. The model
        // is renamed at the assertion use point, so admitting such a local can
        // manufacture a modular equation for the competing definition and a
        // false SAT counterexample.
        && !crate::guards::value_local_is_unstable(func, dest.local)
}

#[cfg_attr(not(test), allow(dead_code))]
fn call_destination_base_locals(func: &VerifiableFunction) -> FxHashSet<usize> {
    func.body
        .blocks
        .iter()
        .filter_map(|b| match &b.terminator {
            // A projected destination writes part of its base local and is just
            // as incompatible with a whole-local "stable definition" as a bare
            // destination. Exclude the base in both cases.
            Terminator::Call { dest, .. } => Some(dest.local),
            _ => None,
        })
        .collect()
}

/// Trust (Clean-origin definitional grounding, assert-refutation lane): the
/// Clean-origin definitional call model installed for `block`'s `Call`, when
/// the call carries a sealed identity that the active [`crate::VcgenContext`]
/// maps to one AND the terminator's rendered `func` equals the model's name.
///
/// The identity is the whole decision; the name equality is a belt. `None`
/// for a call with NO identity (an indirect call, a `dyn` dispatch, a generic
/// instantiation the extractor refused to fingerprint) — never a fall-back to
/// the string.
fn clean_origin_definitional_model_for_call(
    block: &trust_types::BasicBlock,
) -> Option<crate::modular::CleanOriginDefinitionalCallModel> {
    let Terminator::Call { func: callee, callee_identity: Some(identity), .. } = &block.terminator
    else {
        return None;
    };
    let model = crate::clean_origin_definitional_model_for(identity)?;
    (model.name() == callee.as_str()).then_some(model)
}

/// Trust (Clean-origin definitional grounding, assert-refutation lane): the
/// `(Eq(dest, rhs), range facts)` models of every `Terminator::Call` whose
/// callee is a Clean-origin def with a kernel-gated DEFINITIONAL summary
/// (`modular::CleanOriginDefinitionalCallModel`), plus the set of destination
/// locals those models define. Consumed by the candidate-resolution fixpoint
/// EXACTLY like `wrap_models` — one more source of exact call-result
/// definitions, versioned at each assert's use point.
///
/// # What this closes
///
/// A call destination is opaque to every other definition channel of this
/// lane (`call_destination_base_locals` deliberately keeps it out of the
/// statement-definition lane), so `let v = m::pick(41, 7); assert!(v == 41)`
/// declines as ungrounded and the whole-function panic-freedom aggregate stays
/// UNKNOWN even though the VC lane already closes the sibling Assertion row
/// KernelCertified from the same summary. With the model, `v == 41` is a
/// candidate definition whose rhs is ground, `_2 == (v == 41)` resolves through
/// it, the panic-path formula is UNSAT, and the per-block
/// `panic_calls_proven_unreachable` flag (every target block proved,
/// `AssertRefutationCoverage`) can exempt the assert's
/// `core::panicking::panic` edge in the compiler's call gate.
///
/// # Soundness — both verdict directions
///
/// The lane consumes SAT as a real counterexample and UNSAT as a real proof,
/// so an admitted definition must be TRUE of every execution (or UNSAT is a
/// false proof) and must DETERMINE the destination from the actuals (or SAT
/// is a false refutation). Each gate below supplies one half:
///
///  * **Truth** is the summary's own authority contract
///    (`FunctionSummary::with_definitional_postcondition`: the clause restates
///    the exact semantics of a body the compiler emitted from the
///    kernel-checked plan, and the faithfulness gate refuses compilation if
///    the emitted body disagrees). `CleanOriginDefinitionalCallModel::
///    from_clean_origin_summary` admits nothing but a pure definitional
///    summary — an ordinary contract postcondition never reaches here.
///  * **Identity** is the call's sealed `callee_identity` looked up in an
///    identity-keyed map (`clean_origin_definitional_model_for_call`), so a
///    model for a different callee — same rendered name or not — cannot
///    ground this destination; an absent identity admits nothing.
///  * **Rebinding** goes through the PRODUCTION injection path
///    (`callee_postcondition_is_injectable` + `rebind_callee_postconditions`:
///    arity, unprojected dest, `dest_fact_is_version_pinnable`, no actual
///    reads the dest, every clause rebindable, the machine-arithmetic filter
///    with its single modular-`Ite` exemption), so this lane and the VC lane
///    cannot encode the same call two ways — the `clean_origin_wrapping_
///    summary_tests` pin already holds that path byte-identical to the
///    extractor's own `wrapping_call_assert_model`.
///  * **Determination** is re-checked structurally on the REBOUND clause set:
///    exactly one `Eq(Var(dest), rhs)` with `rhs` not mentioning `dest`
///    (functional determination by the actuals); every other clause is a
///    range fact conjoined only when the definition is used. A summary whose
///    definition the rebinding filter dropped, or that states two definitions
///    of `dest`, refuses.
///  * **Stability at the use point** is `wrapping_result_local_is_stable`
///    (single `Call` def, unprojected, not `value_local_is_unstable`) — the
///    same argument `wrap_models` make: a use-point-versioned equality about a
///    single-assignment destination is the def-point equality, a true
///    function-wide fact. Every actual must be a constant or an unprojected
///    local that is input-free, a stable wrapping result, or a stable
///    Clean-origin result (chains bottom out in input-free leaves or the
///    grounding check fails, which is the fail-closed direction).
///
/// Fail-closed throughout: no identity, no model, any gate refused ⇒ nothing
/// is emitted for that call and the assert reading it stays ungrounded,
/// exactly as before this lane existed.
pub(super) fn clean_origin_definitional_call_models(
    func: &VerifiableFunction,
    input_free: &FxHashSet<usize>,
    wrap_dest_locals: &FxHashSet<usize>,
    call_def_count: &LocalCounter,
) -> (Vec<(Formula, Vec<Formula>)>, FxHashSet<usize>) {
    if !crate::has_any_clean_origin_definitional_models() {
        return (Vec::new(), FxHashSet::default());
    }
    static ASSERT_DEBUG: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    let debug =
        *ASSERT_DEBUG.get_or_init(|| crate::trust_vcgen_env_var_present("TRUST_ASSERT_DEBUG"));
    // Pass 1: collect candidate `(block, model)` pairs and the destination locals
    // they MAY define (identity + shape), checking the cheap call-shape and TLS
    // `clean_origin_definitional_model_for_call` lookup BEFORE `value_local_is_unstable`.
    let mut candidate_calls: Vec<(
        &trust_types::BasicBlock,
        crate::modular::CleanOriginDefinitionalCallModel,
    )> = Vec::new();
    let mut dest_locals: FxHashSet<usize> = FxHashSet::default();
    for b in &func.body.blocks {
        let Terminator::Call { dest, target, atomic, is_foreign, is_unsafe_sig, .. } =
            &b.terminator
        else {
            continue;
        };
        if target.is_none()
            || atomic.is_some()
            || *is_foreign
            || *is_unsafe_sig
            || !dest.projections.is_empty()
            || call_def_count.get(dest.local) != 1
        {
            continue;
        }
        let Some(model) = clean_origin_definitional_model_for_call(b) else {
            continue;
        };
        if !wrapping_result_local_is_stable(func, dest, 1) {
            continue;
        }
        dest_locals.insert(dest.local);
        candidate_calls.push((b, model));
    }
    if candidate_calls.is_empty() {
        return (Vec::new(), FxHashSet::default());
    }
    // Pass 2: the models themselves.
    let mut models: Vec<(Formula, Vec<Formula>)> = Vec::with_capacity(candidate_calls.len());
    let mut defined: FxHashSet<usize> = FxHashSet::default();
    for (block, model) in candidate_calls {
        let Terminator::Call { func: callee, args, dest, .. } = &block.terminator else {
            continue;
        };
        let operands_ok = args.iter().all(|a| match a {
            Operand::Constant(_) => true,
            Operand::Copy(p) | Operand::Move(p) => {
                p.projections.is_empty()
                    && (input_free.contains(&p.local)
                        || wrap_dest_locals.contains(&p.local)
                        || dest_locals.contains(&p.local))
            }
            // `Operand` is #[non_exhaustive]: an unrecognized operand is unsafe,
            // so the model is skipped (fail-closed).
            _ => false,
        });
        if !operands_ok {
            if debug {
                eprintln!(
                    "[ASSERT_CLEAN_ORIGIN] block={:?} callee={callee} declined: an actual is \
                     neither a constant nor a stable unprojected leaf",
                    block.id
                );
            }
            continue;
        }
        let summary = model.to_definitional_summary();
        if !callee_postcondition_is_injectable(func, dest, &summary, args) {
            if debug {
                eprintln!(
                    "[ASSERT_CLEAN_ORIGIN] block={:?} callee={callee} declined: the production \
                     injection gate refused the summary at this call site",
                    block.id
                );
            }
            continue;
        }
        let dest_name = crate::place_to_var_name(func, dest);
        let rebound = rebind_callee_postconditions(func, args, dest, &summary);
        // Determination: exactly one `dest == rhs` with `rhs` free of `dest`.
        let mut definition: Option<Formula> = None;
        let mut ranges: Vec<Formula> = Vec::new();
        let mut refused = false;
        for clause in rebound {
            match &clause {
                Formula::Eq(lhs, rhs)
                    if lhs.var_name() == Some(dest_name.as_str())
                        && !trust_types::any_free_variable_name(rhs, &mut |v| v == dest_name) =>
                {
                    if definition.replace(clause.clone()).is_some() {
                        refused = true;
                        break;
                    }
                }
                _ => {
                    // A range fact over the actuals (the wrapping shape's
                    // operand ranges). It must not mention the destination:
                    // a non-definitional bound on `dest` is a fact this lane
                    // has no argument for in the SAT direction.
                    if trust_types::any_free_variable_name(&clause, &mut |v| v == dest_name) {
                        refused = true;
                        break;
                    }
                    ranges.push(clause);
                }
            }
        }
        let (Some(definition), false) = (definition, refused) else {
            if debug {
                eprintln!(
                    "[ASSERT_CLEAN_ORIGIN] block={:?} callee={callee} declined: the rebound \
                     clause set is not exactly one determining `{dest_name} == rhs` plus \
                     range facts",
                    block.id
                );
            }
            continue;
        };
        if debug {
            eprintln!(
                "[ASSERT_CLEAN_ORIGIN] block={:?} callee={callee} defines {dest_name}: \
                 {definition:?} ranges={ranges:?}",
                block.id
            );
        }
        defined.insert(dest.local);
        models.push((definition, ranges));
    }
    (models, defined)
}

/// Trust (NEW-EXEMPT-SPLIT, 2026-09-27): the refutation lane's candidates
/// TOGETHER WITH the refutation-target block each one belongs to.
///
/// A bare candidate list cannot say which target blocks it covers, and two facts
/// about this lane make "count the candidates" the wrong question:
///
///   * a target block reached by several control-flow paths emits one candidate
///     PER PATH (`split_path_feasibility_disjuncts`), so one block can own
///     several candidates;
///   * a target block the lane cannot decide — no guard-path entry, a degraded
///     path set, a guard it cannot lower exactly, a formula it cannot ground, an
///     overlapping-place conflict, or a tripped work budget — emits NONE, and
///     nothing counts it as unknown.
///
/// So `#proved candidates == #target blocks` — the rule the compiler's
/// panic-callee exemption used to apply — can balance the two proved paths of
/// one block against a second block that was never a candidate at all. It did:
/// a `Certified` whole-function catch-all was minted over a reachable
/// `assert!` (docs/KNOWN_HAZARDS.md, "the panic-callee exemption counted
/// candidates, not blocks"). A consumer that needs "every target block is
/// proved unreachable" must decide it per block from
/// [`AssertRefutationCoverage`].
#[derive(Debug, Clone)]
pub struct AssertRefutationCandidates {
    vcs: Vec<VerificationCondition>,
    coverage: AssertRefutationCoverage,
}

impl AssertRefutationCandidates {
    /// The candidates, in emission order — exactly the list
    /// [`generate_full_assert_refutation_vcs`] returns.
    #[must_use]
    pub fn vcs(&self) -> &[VerificationCondition] {
        &self.vcs
    }

    /// Which target block each candidate belongs to.
    #[must_use]
    pub fn coverage(&self) -> &AssertRefutationCoverage {
        &self.coverage
    }

    /// Split into the candidates and their coverage record. Candidate `i` of the
    /// returned list is candidate `i` of the record.
    #[must_use]
    pub fn into_parts(self) -> (Vec<VerificationCondition>, AssertRefutationCoverage) {
        (self.vcs, self.coverage)
    }
}

/// Trust (NEW-EXEMPT-SPLIT): the per-target-block record of one run of the
/// refutation lane. See [`AssertRefutationCandidates`] for why it exists.
///
/// A target block is a block [`is_assert_refutation_target_block`] recognizes in
/// the body the lane walks — the tail-call projection
/// (`VerifiableFunction::with_tail_calls_expanded`), whose block identities are
/// the original body's plus one bookkeeping `Return` per tail call, so every
/// target block of the original body is one here under the same id.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct AssertRefutationCoverage {
    /// Parallel to the candidate list: the target block candidate `i` is a path
    /// part of. `None` for a candidate that belongs to no target block (the
    /// malformed-IR row, a T9 unused-`contract_panic`-annotation row).
    origins: Vec<Option<BlockId>>,
    /// Every target block, in body order, with the number of path parts the lane
    /// emitted for it — `0` when it declined the block.
    targets: Vec<(BlockId, usize)>,
}

impl AssertRefutationCoverage {
    /// How many candidates this record describes.
    #[must_use]
    pub fn candidate_count(&self) -> usize {
        self.origins.len()
    }

    /// The target block candidate `index` is a path part of, if any. `None` for
    /// an index past this record: a candidate some OTHER generator appended (the
    /// coroutine-sentinel lane's, say) belongs to no target block.
    #[must_use]
    pub fn candidate_target_block(&self, index: usize) -> Option<BlockId> {
        self.origins.get(index).copied().flatten()
    }

    /// Every target block of the walked body, in body order.
    pub fn target_blocks(&self) -> impl Iterator<Item = BlockId> + '_ {
        self.targets.iter().map(|(block, _)| *block)
    }

    /// The target blocks the lane emitted NO candidate for.
    #[must_use]
    pub fn declined_target_blocks(&self) -> Vec<BlockId> {
        self.targets.iter().filter(|(_, parts)| *parts == 0).map(|(block, _)| *block).collect()
    }

    /// Whether target `block` is proved UNREACHABLE: the lane emitted its path
    /// split (at least one part), every part it emitted is still in the
    /// candidate list, and `proved(i)` holds for each of them.
    ///
    /// `false` for a block this record does not list as a target, for a declined
    /// block, and for a block with even one unproved part: the parts are the
    /// disjuncts of the block's feasibility formula, so the block is unreachable
    /// only when EVERY one is UNSAT.
    pub fn target_block_proved(&self, block: BlockId, proved: impl Fn(usize) -> bool) -> bool {
        let Some(&(_, parts)) = self.targets.iter().find(|(target, _)| *target == block) else {
            return false;
        };
        let mut present = 0usize;
        for (index, origin) in self.origins.iter().enumerate() {
            if *origin != Some(block) {
                continue;
            }
            if !proved(index) {
                return false;
            }
            present += 1;
        }
        parts > 0 && present == parts
    }

    /// Whether EVERY target block is proved unreachable (see
    /// [`Self::target_block_proved`]). Vacuously `true` for a body with no
    /// target block. A candidate that belongs to no target block — however many
    /// of them are proved — covers nothing.
    pub fn every_target_block_proved(&self, proved: impl Fn(usize) -> bool) -> bool {
        self.targets.iter().all(|(block, _)| self.target_block_proved(*block, &proved))
    }

    /// A record built by hand, for the pins in `assert_refutation_coverage_tests`.
    #[cfg(test)]
    pub(super) fn for_test(origins: Vec<Option<BlockId>>, targets: Vec<(BlockId, usize)>) -> Self {
        Self { origins, targets }
    }

    /// A record in which the lane declined every target block of `func` (the
    /// tail-call projection) and emitted `candidates` candidates of no block.
    fn declining_every_target(func: &VerifiableFunction, candidates: usize) -> Self {
        let projection = func.with_tail_calls_expanded();
        Self {
            origins: vec![None; candidates],
            targets: projection
                .body
                .blocks
                .iter()
                .filter(|block| is_assert_refutation_target_block(block))
                .map(|block| (block.id, 0))
                .collect(),
        }
    }
}

pub fn generate_full_assert_refutation_vcs(
    func: &VerifiableFunction,
) -> Vec<VerificationCondition> {
    let context = crate::VcgenContext::for_function_inheriting_self_call_identity(&func.def_path);
    generate_full_assert_refutation_vcs_with_context(func, &context)
}

/// Generate full-mode assertion-refutation VCs under explicit function policy.
/// Contract-panic annotations are consumed only when `context` owns `func`.
///
/// Returns the candidates only. A caller that must know which target blocks
/// they cover — anything that reads "every `assert!`/`panic!` block is proved
/// unreachable" off the verdicts — uses
/// [`generate_full_assert_refutation_candidates_with_context`] instead.
pub fn generate_full_assert_refutation_vcs_with_context(
    func: &VerifiableFunction,
    context: &crate::VcgenContext,
) -> Vec<VerificationCondition> {
    generate_full_assert_refutation_candidates_with_context(func, context).into_parts().0
}

/// [`generate_full_assert_refutation_vcs_with_context`], together with the
/// target block each candidate belongs to and the target blocks it declined.
pub fn generate_full_assert_refutation_candidates_with_context(
    func: &VerifiableFunction,
    context: &crate::VcgenContext,
) -> AssertRefutationCandidates {
    crate::with_function_vcgen_context(&func.def_path, context, || {
        generate_full_assert_refutation_candidates_impl(func)
    })
}

/// [`generate_full_assert_refutation_candidates_with_context`] into the caller's context
/// `rows`, the body's (T3 C07p, design D-VC-1): every candidate is interned through the row
/// oracle, and the candidates and their coverage are returned as generated.
pub fn generate_full_assert_refutation_candidates_with_context_rows(
    func: &VerifiableFunction,
    context: &crate::VcgenContext,
    rows: &mut trust_types::vc_context::VcContext,
) -> AssertRefutationCandidates {
    let candidates = generate_full_assert_refutation_candidates_with_context(func, context);
    intern_eager_rows(rows, candidates.vcs());
    candidates
}

pub(super) fn generate_full_assert_refutation_candidates_impl(
    func: &VerifiableFunction,
) -> AssertRefutationCandidates {
    if let Err(error) = crate::validate_function(func) {
        return AssertRefutationCandidates {
            vcs: vec![malformed_trust_ir_vc(func, &error)],
            coverage: AssertRefutationCoverage::declining_every_target(func, 1),
        };
    }

    // This refutation lane is also a compiler-facing standalone API. Keep its
    // panic-site, path, and call-result analyses on the same exact TailCall
    // semantic projection as ordinary VC generation.
    let tail_call_expanded = func.with_tail_calls_expanded();
    let func = tail_call_expanded.as_ref();

    // verifier-perf: hold the mid-generation work-meter scope; this path materializes
    // declared types via owned place-type queries too (`place_to_var_name`, path
    // defs). Resets on the outermost entry. SOUNDNESS: DROP-ONLY (see the trip
    // check before the return).
    let _gen_work_scope = crate::gen_work_scope();
    // verifier-perf (whole-function gate): an over-budget recursive-datatype function
    // explodes `StmtVersionCtx::build` / path-def machinery below. Emit NO refutation
    // claims for it. SOUNDNESS: withholding a refutation is the fail-closed direction (it
    // can only DROP a refutation, never manufacture one) — DROP-ONLY. Every target
    // block is then DECLINED in the coverage record, never silently absent from it.
    if func_exceeds_vcgen_budget(func) {
        return AssertRefutationCandidates {
            vcs: Vec::new(),
            coverage: AssertRefutationCoverage::declining_every_target(func, 0),
        };
    }
    // This public lane can be invoked independently of `generate_vcs_impl`, so
    // sanitize its direct precondition consumption at its own boundary too.
    let arithmetic_safe_func = without_unmodeled_contract_arithmetic(func);
    let func = arithmetic_safe_func.as_ref();
    if super::cached_terminator_presence_for_body(&func.body).is_some_and(|tp| !tp.has_call)
        || !func.body.blocks.iter().any(is_assert_refutation_target_block)
    {
        let vcs = if crate::gen_work_tripped() {
            Vec::new()
        } else {
            contract_panic_unused_vcs(func)
        };
        let origins = vec![None; vcs.len()];
        return AssertRefutationCandidates {
            vcs,
            coverage: AssertRefutationCoverage { origins, targets: Vec::new() },
        };
    }
    // This compiler-facing entry can run without the ordinary generator's memo
    // frame. Bind its analyses to the final immutable semantic view, after both
    // projections. Join the existing work meter; do not reset its budget or hide
    // charges. The unchanged trip handling below still declines every target.
    let _entry_scope = super::EntryScope::enter(func);
    let sv = super::stmt_versions_for(func);
    // Refutations need more than the proof-facing path map: a collapsed map
    // contains an empty guard path that looks exactly like unconditional
    // reachability, and the ordinary guard lowering may weaken an unmodeled
    // condition to `true`.  Retain collapse provenance and use the exact
    // refutation-polarity lowering below; either loss declines the candidate.
    let guard_analysis = super::path_guard_analysis_for(func);
    let guard_paths_map = &*guard_analysis.paths;
    // The formula var names whose value is an UNCONSTRAINED function input, so it
    // is sound to leave them free in a path-feasibility formula (no spurious SAT):
    // entry-stable parameters plus the narrow single-use payload-extractor lane.
    // A copy, constant, discriminant, or other computed/merged intermediate is
    // excluded here and must instead acquire an exact constraining definition.
    let input_free = v2_input_free_locals(func);
    let safe_names: FxHashSet<String> = input_free
        .iter()
        .copied()
        .filter(|&local| local < func.body.locals.len())
        .map(|local| crate::place_to_var_name(func, &Place::local(local)))
        .collect();
    // EXACT PIN 1: the names of PLACE COMPONENTS of an input-free root that this
    // body actually reads (`o@1.0.0`, the `Some((a, b))` payload field of a
    // parameter `o`). A component of an unconstrained input is itself
    // unconstrained, so leaving it free is the same claim `safe_names` makes one
    // level up — NOT the base-name exemption `3d1446f4c7` removed. The
    // overlapping-name guard at the emission point is what keeps that channel
    // closed; see `input_free_component_names` / `refutation_names_may_alias`.
    let component_free_names = input_free_component_names(func, &input_free, &safe_names);
    // Per-block path-definition facts (branch-merge `x == Ite(..)` invariants,
    // enum/struct-payload definitions, `?`-Try payloads). Conjoining a relevant
    // one PINS an otherwise-free computed/merged value to an input-free expression,
    // so it is resolved rather than spuriously free. Monotone-sound (true equalities
    // only shrink the model set).
    // Diagnostic-only (`TRUST_ASSERT_DEBUG`): the admitted input-free set. When a
    // candidate declines with `grounded=false`, this is the first thing to read —
    // a shrunken `safe_names` and an unresolved free var together say the formula
    // needs an exact DEFINITION, not a wider exemption. Reads only; no verdict
    // depends on it.
    static ASSERT_SAFE_DEBUG: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    if *ASSERT_SAFE_DEBUG.get_or_init(|| crate::trust_vcgen_env_var_present("TRUST_ASSERT_DEBUG")) {
        let mut safe_sorted: Vec<&String> = safe_names.iter().collect();
        safe_sorted.sort();
        let mut free_sorted: Vec<&usize> = input_free.iter().collect();
        free_sorted.sort();
        let mut component_sorted: Vec<&String> = component_free_names.iter().collect();
        component_sorted.sort();
        eprintln!(
            "[ASSERT_SAFE] input_free_locals={free_sorted:?} safe_names={safe_sorted:?} \
             components={component_sorted:?}"
        );
    }
    // Trust: wrapping-call result DEFINITIONS — `(Eq(dest, modular-ite), operand
    // range facts)` for each `wrapping_{add,sub}` whose result temp is a
    // `Terminator::Call` dest (invisible to the statement/path-def extractors, so
    // without this the comparing assert is dropped as ungrounded). Sound ONLY when
    // the dest local is SINGLE-assignment (one Call def — else its value is
    // path-dependent) and every operand is an input-free leaf (so the modular
    // identity `dest == wrap(op(a,b))` holds at every reaching-def version). The
    // range facts are conjoined by the resolution loop only when the def is used,
    // keeping the refute direction from picking an out-of-range operand.
    let mut wrap_raw_blocks: Vec<&trust_types::BasicBlock> = Vec::new();
    let wrap_call_def_count = {
        let mut c = LocalCounter::new(func.body.locals.len());
        for b in &func.body.blocks {
            if let Terminator::Call {
                func: callee,
                dest,
                target,
                atomic,
                is_foreign,
                is_unsafe_sig,
                ..
            } = &b.terminator
            {
                c.inc(dest.local);
                if target.is_some()
                    && atomic.is_none()
                    && !*is_foreign
                    && !*is_unsafe_sig
                    && dest.projections.is_empty()
                    && wrapping_call_tail_op(callee).is_some()
                {
                    wrap_raw_blocks.push(b);
                }
            }
        }
        c
    };
    // Locals that are SINGLE-assignment `wrapping_{add,sub}` results. A wrap result
    // is defined once, so its value is fixed — it is a SAFE operand for an OUTER
    // wrapping op (CHAINED wrapping, e.g. `a.wrapping_add(b).wrapping_add(c)` or
    // `head.wrapping_add(n).wrapping_sub(n)`). The resolution fixpoint grounds the
    // inner model first, then the outer, bottoming out in input-free leaves; if a
    // chain does not bottom out the grounding check fails and the assert is dropped
    // (sound). The inner result's u32 range is conjoined by the outer model's
    // operand-range facts, so the single-Ite modular reduction stays faithful.
    let mut wrap_dest_locals: FxHashSet<usize> = FxHashSet::default();
    let mut wrap_candidate_blocks: Vec<&trust_types::BasicBlock> = Vec::new();
    for b in wrap_raw_blocks {
        let Terminator::Call { dest, .. } = &b.terminator else {
            continue;
        };
        if wrap_call_def_count.get(dest.local) == 1 && wrapping_result_local_is_stable(func, dest, 1)
        {
            wrap_dest_locals.insert(dest.local);
            wrap_candidate_blocks.push(b);
        }
    }
    let wrap_models: Vec<(Formula, Vec<Formula>)> = wrap_candidate_blocks
        .into_iter()
        .filter_map(|b| {
            let Terminator::Call {
                func: callee,
                args,
                dest,
                target,
                atomic,
                is_foreign,
                is_unsafe_sig,
                ..
            } = &b.terminator
            else {
                return None;
            };
            let operands_ok = args.iter().take(2).all(|a| match a {
                Operand::Constant(_) => true,
                // An operand is a SAFE (stable) leaf when it is an input-free read OR
                // itself a single-assignment wrapping result (chained wrapping).
                Operand::Copy(p) | Operand::Move(p) => {
                    p.projections.is_empty()
                        && (input_free.contains(&p.local) || wrap_dest_locals.contains(&p.local))
                }
                // `Operand` is #[non_exhaustive]: an unrecognized operand is treated
                // as unsafe, so the model is skipped (fail-closed).
                _ => false,
            });
            if !operands_ok {
                return None;
            }
            wrapping_call_assert_model(
                func,
                callee,
                args,
                dest,
                target.is_some(),
                atomic.is_some(),
                *is_foreign,
                *is_unsafe_sig,
            )
        })
        .collect();
    // Trust (Clean-origin definitional grounding): `(Eq(dest, rhs), range
    // facts)` for each `Terminator::Call` whose callee is a Clean-origin def
    // carrying a kernel-gated DEFINITIONAL summary in the active context —
    // identity-keyed, rebound through the production injection path, and
    // gated on the same single-assignment stability as `wrap_models`. See
    // `clean_origin_definitional_call_models` for the soundness argument in
    // both verdict directions. Empty (byte-identical behaviour) whenever the
    // context carries no such model.
    let (clean_origin_models, _clean_origin_dest_locals) = clean_origin_definitional_call_models(
        func,
        &input_free,
        &wrap_dest_locals,
        &wrap_call_def_count,
    );
    // STRAIGHT-LINE definition grounding (XOR / cast / checked-arith assert path).
    // The path-feasibility formula for a user `assert!` over computed bool/integer
    // intermediates (e.g. `r == (((a as u8) + ..) % 2 == 1)`) has free vars that are
    // NOT branch-merge Ites / enum payloads / wrapping-call models — they are the
    // ordinary straight-line statement results: bool `BitXor`/`Cast` defs and the
    // `CheckedBinaryOp` overflow flag `_N.1`. The checked result `_N.0` is
    // edge-sensitive: its unbounded mathematical equation is true only after the
    // no-overflow Assert succeeds, so it comes exclusively from `path_defs` above.
    // Without pinning the remaining straight-line values the
    // assert is dropped as ungrounded and the typed CHC/PDR route returns Unsupported
    // -> UNKNOWN. Collect each block's statement definitions (`extract_block_definitions`,
    // which already lowers bool `BitXor` to `dest == (l != r)` and bool->int casts to
    // `dest == Ite(b, 1, 0)`) PLUS the checked-add flag semantics
    // (`extract_overflow_flag_semantics` — the `.1` overflow-flag def the statement
    // extractor deliberately skips), gated to function-wide SINGLE-ASSIGNMENT vars.
    //
    // SOUNDNESS: each def is conjoined only after `version_rename_at` at the assert
    // use-point (below). For a var defined exactly once in the whole function its
    // reaching-def version is unique at EVERY program point, so the use-point-versioned
    // equality equals the def-point equality — a genuine function-wide true fact
    // (monotone: only shrinks the model set, so it can manufacture neither a spurious
    // UNSAT/false-prove nor a spurious SAT/false-refute). A def any of whose vars is NOT
    // single-assignment-or-input is DROPPED (fail-closed), so a value a later
    // reassignment could falsify never enters the conjunction. The relevance slice below
    // still conjoins only fv-reachable defs; the terminal discharge stays in
    // `refute_full_assert_obligations` -> `InProcessAyBackend` (Proved only on a
    // strict-checked ay UNSAT-of-negation artifact). This is the same soundness argument
    // as `wrap_models` / path-defs, restricted further by the single-assignment gate.
    // A normal call destination is not a stable definition merely because it is
    // written once: without an exact callee model its value is opaque. Keep every
    // call destination out of the generic statement-definition lane. Authenticated
    // wrapping calls are grounded independently through `wrap_models`, and the
    // narrow payload-extractor allowlist is represented explicitly in `safe_names`.
    let single_assign_names: FxHashSet<String> = {
        let mut count = LocalCounter::new(func.body.locals.len());
        for b in &func.body.blocks {
            for stmt in &b.stmts {
                if let Statement::Assign { place, .. } = stmt
                    && place.projections.is_empty()
                {
                    count.inc(place.local);
                }
            }
        }
        let mut names = FxHashSet::default();
        // Trust (P0 call-arg &mut staleness, assert-refute lane): a local with a
        // single DIRECT store can still be MUTATED through a `&mut`/`&raw mut`
        // borrow that escapes into a call (`set(&mut a, v)`, `mem::swap`), so its
        // single-assignment `Eq(a, init)` fact is STALE after the call. Treating
        // it as stable let the assert-refute grounder pin `a` to its pre-call
        // value (`let mut a = x; set(&mut a, v); assert!(a == v)` GROUNDED `a` to
        // `x`, refuting the always-true `a == v` — a false REFUTATION of valid
        // Rust). Exclude mutably-borrowed locals; `value_local_is_unstable` is the
        // SAME predicate the bounds/upper-bound staleness gates use, so the
        // refute lane and the proof lane agree on what is reassignable. SOUND:
        // dropping a fact only DROPS a refutation (fail-closed) — it can never
        // manufacture a refutation or a proof.
        count.for_each_nonzero(|local, c| {
            if c == 1
                && wrap_call_def_count.get(local) == 0
                && !crate::guards::value_local_is_unstable(func, local)
            {
                names.insert(crate::place_to_var_name(func, &Place::local(local)));
            }
        });
        names
    };
    // The base place name of a (possibly versioned / projected) formula var: strip
    // the `#sN_M` reaching-def token and EVERY projection segment, leaving the
    // place ROOT (`place_name_root_and_segments` decodes the one canonical
    // `base ++ segments` encoding, so this reaches `@variant.field` and `[idx]`
    // and `*` spellings too, not only a trailing numeric `.k`).
    //
    // This is a STABILITY question, never a freedom one: `var_stable` asks whether
    // a name denotes the same value at every program point, and a component of a
    // place is stable exactly when the place is. Both root predicates below
    // already require that — `safe_names` via `local_versions_collapse_to_bare`
    // (no statement write, no call-destination write, no mutable escape) and
    // `single_assign_names` via `value_local_is_unstable`, which counts a PROJECTED
    // store (`a.0 = ..`) against the base local. So widening the strip cannot
    // admit a definition about a value that changes; it only lets a true fact
    // about a stable component be collected. Widening the strip does NOT make a
    // component free — `is_free` is the separate, guarded admission below.
    fn def_base_name(v: &str) -> &str {
        place_name_root(v)
    }
    let var_stable = |v: &str| {
        safe_names.contains(v)
            || safe_names.contains(def_base_name(v))
            || single_assign_names.contains(def_base_name(v))
    };
    let def_stable = |d: &Formula| trust_types::all_free_variable_names(d, &mut |v| var_stable(v));
    // EXACT PIN 2: `dest == __trust_mir__discr_<src>` (+ the carrier's own variant
    // membership) for every `Discriminant` read of an input-free place whose
    // destination is function-wide single-assignment. `single_assign_names` is
    // exactly the "one direct store, not a call destination, not mutably escaped"
    // set the `stmt_defs` soundness note relies on, so reusing it makes the
    // use-point-versioned equality a true function-wide fact by the SAME argument.
    // UNVERSIONED here; renamed at each assert's use point with the other
    // candidates below.
    let discriminant_pins = discriminant_pin_defs(func, &input_free, &single_assign_names);
    // The carriers those pins introduce, which `is_free` admits (see
    // `discriminant_pin_defs` for why a tag of an unconstrained input is itself
    // unconstrained, and why its membership range must ride along).
    let discriminant_pin_carriers: FxHashSet<String> =
        discriminant_pins.iter().map(|(_, _, carrier)| carrier.clone()).collect();
    type LazyGroundingDefs = (
        std::rc::Rc<FxHashMap<BlockId, Vec<Formula>>>,
        Vec<(Formula, Vec<Formula>)>,
        Vec<(String, Vec<String>, Formula, Vec<Formula>)>,
        Vec<(Formula, Vec<(String, Option<String>)>)>,
    );
    let lazy_grounding_defs: std::cell::OnceCell<LazyGroundingDefs> = std::cell::OnceCell::new();
    let get_grounding_defs = || -> &LazyGroundingDefs {
        lazy_grounding_defs.get_or_init(|| {
            let path_defs = super::path_definition_map_for(func);
            // `(Eq-def, range-facts)` candidates, UNVERSIONED here (renamed per assert site).
            let mut stmt_defs: Vec<(Formula, Vec<Formula>)> = Vec::new();
            // The refutation path formula versions every branch guard at that guard's
            // SOURCE block.  A definition renamed only at the eventual panic block can
            // therefore carry a join token (`x#e_s2_0`) while the exact edge guard reads
            // the establishing token (`x#s2_0`).  Keep an establish-point-stamped copy of
            // each stable statement definition as well.  This is not an aliasing guess:
            // `version_block_def_at_establish` versions rhs reads immediately BEFORE the
            // defining write and the subject immediately AFTER it, so the equality is a
            // true fact about that exact snapshot (including self-updates).  Candidate
            // relevance below still requires an exact token match before consuming it.
            let mut stmt_defs_at_establish: Vec<(String, Vec<String>, Formula, Vec<Formula>)> =
                Vec::new();
            let push_establish_cand =
                |out: &mut Vec<(String, Vec<String>, Formula, Vec<Formula>)>,
                 vd: Formula,
                 vranges: Vec<Formula>| {
                    if let Formula::Eq(a, b) = &vd {
                        if let Some(v) = a.var_name() {
                            out.push((
                                v.to_string(),
                                formula_free_var_vec(b),
                                vd,
                                vranges,
                            ));
                        } else if let Some(v) = b.var_name() {
                            out.push((
                                v.to_string(),
                                formula_free_var_vec(a),
                                vd,
                                vranges,
                            ));
                        }
                    }
                };
            for b in &func.body.blocks {
                // Trust (2026-08-20, bare-BinaryOp wrapping): partition each block's
                // definitions into Eq defs and NON-Eq true-fact conjuncts (the bare
                // wrapping-binop model's operand type-range tautologies, shift/cast
                // result ranges, `x/c <= x`), attaching the facts to every Eq exactly
                // like the overflow-flag ranges below — conjoined only when the def is
                // used. Every non-Eq emission of `extract_block_definitions` is a
                // true-of-every-execution bound (each documents its own tautology
                // argument), so the attachment is monotone-sound in both directions;
                // for the wrapping def the ranges are LOAD-BEARING — without them the
                // refute direction could pick an out-of-range operand, cross the
                // modular Ite's branch boundary, and spuriously SAT a valid assert
                // (the same hazard the wrapping-CALL model's ranges guard against).
                // Trust: 2026-09-16 (round A11) — each def carries the index of the
                // statement that emitted it, which bounds its establish search below
                // (`own + 1`): the pin is the def's OWN write, never a later reseat of its
                // subject's ancestor.
                let block_defs = guards::extract_block_definitions_indexed(func, b);
                let mut bd_eqs: Vec<(usize, Formula)> = Vec::new();
                let mut raw_bd_facts: Vec<Formula> = Vec::new();
                for (own, f) in block_defs {
                    if matches!(f, Formula::Eq(..)) {
                        if def_stable(&f) {
                            bd_eqs.push((own, f));
                        }
                    } else {
                        raw_bd_facts.push(f);
                    }
                }
                if !bd_eqs.is_empty() {
                    let bd_facts: Vec<Formula> =
                        raw_bd_facts.into_iter().filter(|f| def_stable(f)).collect();
                    for (own, d) in bd_eqs {
                        let bound = (own + 1).min(b.stmts.len());
                        let established_ranges = block_def_subject(&d)
                            .and_then(|subject| def_subject_establish_stmt(func, b, subject, bound))
                            .map_or_else(
                                || bd_facts.clone(),
                                |k| {
                                    bd_facts
                                        .iter()
                                        .map(|range| version_rename_at(range, &sv, func, b.id, k))
                                        .collect()
                                },
                            );
                        push_establish_cand(
                            &mut stmt_defs_at_establish,
                            version_block_def_at_establish(&sv, func, b, bound, d.clone()),
                            established_ranges,
                        );
                        stmt_defs.push((d, bd_facts.clone()));
                    }
                }
                // `extract_overflow_flag_semantics` = `[_N.1 <=> overflow, lhs_range,
                // rhs_range]`. Keep the flag Eq, attaching the operand range facts so
                // they ride along when it is used. The success-only `_N.0 == lhs OP rhs`
                // equation must come from this assert site's edge-sensitive `path_defs`.
                let ofs = guards::extract_overflow_flag_semantics(func, b);
                let mut eqs: Vec<Formula> = Vec::new();
                let mut raw_ranges: Vec<Formula> = Vec::new();
                for f in ofs {
                    if matches!(f, Formula::Eq(..)) {
                        if def_stable(&f) {
                            eqs.push(f);
                        }
                    } else {
                        raw_ranges.push(f);
                    }
                }
                // The flag facts are about the asserted `CheckedBinaryOp`: bound the
                // establish search at that statement when it is located (round A11).
                if !eqs.is_empty() {
                    let ranges: Vec<Formula> =
                        raw_ranges.into_iter().filter(|f| def_stable(f)).collect();
                    let flag_bound =
                        assert_passed_establish_stmt(func, b).map_or(b.stmts.len(), |k| k + 1);
                    for d in eqs {
                        let established_ranges = block_def_subject(&d)
                            .and_then(|subject| {
                                def_subject_establish_stmt(func, b, subject, flag_bound)
                            })
                            .map_or_else(
                                || ranges.clone(),
                                |k| {
                                    ranges
                                        .iter()
                                        .map(|range| version_rename_at(range, &sv, func, b.id, k))
                                        .collect()
                                },
                            );
                        push_establish_cand(
                            &mut stmt_defs_at_establish,
                            version_block_def_at_establish(&sv, func, b, flag_bound, d.clone()),
                            established_ranges,
                        );
                        stmt_defs.push((d, ranges.clone()));
                    }
                }
            }
            // Trust (derived trivial-setter summary — the COMPLETENESS half of the P0
            // staleness fix documented on `single_assign_names` above): that fix
            // correctly excludes a mut-borrowed local from the stable-def channels, so
            // after `set(&mut a, v)` the grounder no longer pins `a` to its STALE
            // pre-call value — but it then knows NOTHING about `a`, so the always-true
            // `assert!(a == v)` stays ungrounded and demotes to runtime-checked. When
            // the callee is a RECOGNIZED trivial setter, the post-call value is exact:
            // conjoin `a#s{b}_t == v` (`trivial_setter_callsite_fact` — versioned at
            // the call terminator, name-disjoint from every pre-call/stale read), plus
            // the copy-chain links `dst == a` for whole-local copies OF THE SETTER
            // TARGET, each counted at an assert only while it is LIVE there (below), so
            // each is a TRUE per-snapshot fact — a copy reading the PRE-call value is not
            // live after the call, and is never falsely connected. Both polarities stay
            // sound: true facts cannot exclude a genuine counterexample snapshot (a
            // real refutation stays SAT) and UNSAT still means no execution reaches
            // the panic. Fail-closed: no recognized setter call ⇒ empty ⇒ unchanged.
            // UNVERSIONED derived-setter facts + copy-chain links, each with the versions its
            // names had where it was ESTABLISHED. Each is versioned at the ASSERT use-point
            // below (via `version_rename_at`, exactly like `stmt_defs`), so the target's
            // token unifies with the assert formula's own reaching-def token by
            // construction — robust to the trust-ir flip's re-versioning (the pre-pinned
            // terminator token did not survive it). A fact counts at a use point ONLY while
            // it is LIVE there: every name it mentions still carries its establish version
            // (the gate at the conjoin site). Trust (2026-09-30): without it the use-point
            // rename moved a fact taken before a later write onto the write's token, and an
            // audit PROVED seven programs that panic: `let old = x; set(&mut x, 5);
            // assert!(old == 5)`, two copies straddling the call compared equal, and an
            // earlier setter's value restamped onto a later call (the 2026-09-17 pack proves
            // them too; `tests/ui/trust/setter_fact_is_live_only_until_the_next_write_refused.rs`).
            // The comment this replaces said "a pre-call read versions to a different
            // reaching def and stays disjoint"; renamed at the use point, it did not.
            let setter_defs: Vec<(Formula, Vec<(String, Option<String>)>)> =
                if crate::has_any_callee_setter_summaries() {
                    let mut defs: Vec<(Formula, Vec<(String, Option<String>)>)> = Vec::new();
                    let mut targets: FxHashSet<usize> = FxHashSet::default();
                    for b in &func.body.blocks {
                        let Some((target, fact)) = trivial_setter_callsite_fact_unversioned(func, b)
                        else {
                            continue;
                        };
                        targets.insert(target);
                        // The target's version just past the call must BE the call's terminator
                        // version, which pins the fact to this write alone; a call whose return
                        // block joins other paths gives the target a join version instead, and
                        // the fact is withheld.
                        let target_name = crate::place_to_var_name(func, &Place::local(target));
                        let marker = Some(format!("s{}_t", b.id.0));
                        let Terminator::Call { target: Some(after), .. } = &b.terminator else {
                            continue;
                        };
                        if sv.version_token_at(func, *after, 0, &target_name) != marker {
                            continue;
                        }
                        let mut live = vec![(target_name.clone(), marker)];
                        let mut seen_fact_names: FxHashSet<String> = FxHashSet::default();
                        trust_types::for_each_free_variable_name(&fact, &mut |name| {
                            if name != target_name && seen_fact_names.insert(name.to_string()) {
                                let at_call = sv.version_token_at(func, b.id, b.stmts.len(), name);
                                live.push((name.to_string(), at_call));
                            }
                        });
                        defs.push((fact, live));
                    }
                    if !targets.is_empty() {
                        for cb in &func.body.blocks {
                            for (k, stmt) in cb.stmts.iter().enumerate() {
                                let Statement::Assign {
                                    place,
                                    rvalue: Rvalue::Use(Operand::Copy(src) | Operand::Move(src)),
                                    ..
                                } = stmt
                                else {
                                    continue;
                                };
                                if !place.projections.is_empty()
                                    || !src.projections.is_empty()
                                    || !targets.contains(&src.local)
                                {
                                    continue;
                                }
                                // Copy-chain link `dst == target`, live while `dst` still holds
                                // THIS copy and `target` still holds the value the copy read.
                                let dst = crate::place_to_var_name(func, place);
                                let target_name = crate::place_to_var_name(func, src);
                                let live = vec![
                                    (dst.clone(), Some(format!("s{}_{k}", cb.id.0))),
                                    (
                                        target_name.clone(),
                                        sv.version_token_at(func, cb.id, k, &target_name),
                                    ),
                                ];
                                defs.push((
                                    Formula::Eq(
                                        Box::new(Formula::Var(dst, Sort::Int)),
                                        Box::new(Formula::Var(target_name, Sort::Int)),
                                    ),
                                    live,
                                ));
                            }
                        }
                    }
                    defs
                } else {
                    Vec::new()
                };
            (path_defs, stmt_defs, stmt_defs_at_establish, setter_defs)
        })
    };
    // The DECLARED, extraction-gated preconditions this lane assumes at entry.
    // Hoisted out of the per-block loop because it is loop-invariant AND because
    // the overlapping-place guard below must judge the names it contributes: a
    // precondition really can constrain a place whose COMPONENT the grounding
    // admitted as free, and a model satisfying both need not describe an argument
    // the contract admits. (See the conjoin site below for the assume/prove
    // pairing that makes assuming them sound in the first place.)
    let safe_preconditions: Vec<Formula> = func
        .preconditions
        .iter()
        .filter(|pre| !contracts::formula_uses_unmodeled_machine_arithmetic_in_function(func, pre))
        .cloned()
        .collect();
    let mut precondition_names: FxHashSet<String> = FxHashSet::default();
    for pre in &safe_preconditions {
        trust_types::for_each_free_variable_name(pre, &mut |name| {
            if !precondition_names.contains(name) {
                precondition_names.insert(name.to_string());
            }
        });
    }
    let precondition_has_projected_or_discr = precondition_names
        .iter()
        .any(|n| refutation_name_has_projection_or_discr(n));
    static ASSERT_DEBUG: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    let debug =
        *ASSERT_DEBUG.get_or_init(|| crate::trust_vcgen_env_var_present("TRUST_ASSERT_DEBUG"));
    // Each candidate travels with the target block it is a path part of, so no
    // later filter can separate a candidate from its block (see
    // `AssertRefutationCoverage`).
    let mut out: Vec<(VerificationCondition, Option<BlockId>)> = Vec::new();
    // Every target block this loop visits, with the number of path parts it
    // emitted. Pushed with `0` BEFORE any decline, so a block the loop gives up
    // on is recorded as declined rather than silently missing.
    let mut targets: Vec<(BlockId, usize)> = Vec::new();
    for block in &func.body.blocks {
        // A user `assert!`/`panic!` failure site. Exclude the `unreachable!()`
        // sentinel ("entered unreachable code"): that is intentional dead-code
        // scaffolding handled by the Unreachable VC, not a refutable assert.
        // Trust (NEW-EXEMPT-SPLIT): the exported recognizer itself, so the
        // blocks this loop targets and the blocks the compiler's panic-callee
        // exemption may skip are one set by construction.
        if !is_assert_refutation_target_block(block) {
            continue;
        }
        let Terminator::Call { func: callee, args, span, .. } = &block.terminator else {
            continue;
        };
        let target_index = targets.len();
        targets.push((block.id, 0));
        let Some(paths) = guard_paths_map.get(&block.id) else { continue };
        if guard_analysis.degraded.contains(&block.id) {
            continue;
        }
        let Some(mut formula) =
            v2_formula_with_refutation_path_guards(func, &sv, block.id, paths, Formula::Bool(true))
        else {
            continue;
        };
        let fv = formula.free_variables();
        if !debug && fv.is_empty() {
            continue;
        }
        // A formula var is INPUT-FREE iff, once the `#sN_M` reaching-def version is
        // stripped, it is an input-free WHOLE place (`safe_names`), an admitted
        // COMPONENT of one (exact pin 1 — `input_free_component_names`), or the
        // `__trust_mir__discr_*` carrier an exact `Discriminant` pin introduced
        // (exact pin 2 — `discriminant_pin_defs`). Each of the three names a
        // component of an unconstrained function input; none names a computed
        // value. Two names that may denote OVERLAPPING storage must never both be
        // free at once, which the guard at the emission point below enforces over
        // the conjunction actually emitted.
        let is_free = |v: &str| {
            let bare = v.split('#').next().unwrap_or(v);
            safe_names.contains(bare)
                || component_free_names.contains(bare)
                || discriminant_pin_carriers.contains(bare)
        };
        let needs_grounding = debug || fv.iter().any(|v| !is_free(v));
        // Resolve computed/merged vars by PINNING them to input-free expressions
        // via this block's path-definition facts: select each `Eq(Var v, rhs)`
        // whose rhs is already resolved (fixpoint), marking `v` resolved and
        // conjoining the def. We only ever ADD defs whose rhs is resolved, so the
        // augmented formula introduces no new unresolved var.
        let mut resolved: FxHashSet<String> = FxHashSet::default();
        // Definitions are admitted only after all of their dependencies are
        // input-free or already resolved, so this is a topological order.  We
        // later substitute Boolean aliases in reverse order (`v -> w`, then
        // `w -> input`) to expose the exact branch predicate to AY without
        // weakening either verdict.  Integer/data definitions remain explicit
        // equalities so counterexample witnesses retain their program values.
        let mut resolution_order: Vec<String> = Vec::new();
        // For each resolved var, the candidate index in `[cand_head, cand_tail]` —
        // avoiding deep-cloning `(Formula, Vec<Formula>, Vec<String>)` for candidates
        // that never enter the relevance slice.
        let mut resolved_def: FxHashMap<String, usize> = FxHashMap::default();
        let end = block.stmts.len();
        // Candidate definitions to resolve computed temps: this block's propagated
        // path-defs (branch-merge `_7 == Ite(..)`, enum/struct payloads) PLUS the
        // function's wrapping-call result models — each versioned at this block's use
        // point so its `#sN_M` reaching-def tokens unify with the path-guard formula's
        // (otherwise the def is name-disjoint and inert). Each candidate carries any
        // range facts to conjoin when (and only when) the def is actually used.
        let mut cand_head: Vec<(String, Vec<String>, Formula, Vec<Formula>)> = Vec::new();
        let mut cand_tail: Vec<(String, Vec<String>, Formula, Vec<Formula>)> = Vec::new();
        if needs_grounding {
            let (path_defs, stmt_defs, stmt_defs_at_establish, setter_defs) =
                get_grounding_defs();
            if let Some(block_defs) = path_defs.get(&block.id) {
                for d in block_defs {
                    let vd = version_rename_at(d, &sv, func, block.id, end);
                    let entry = match &vd {
                        Formula::Eq(a, b) => a
                            .var_name()
                            .map(|v| (v.to_string(), formula_free_var_vec(b)))
                            .or_else(|| {
                                b.var_name()
                                    .map(|v| (v.to_string(), formula_free_var_vec(a)))
                            }),
                        _ => None,
                    };
                    if let Some((subject, rhs_fvs)) = entry {
                        cand_head.push((subject, rhs_fvs, vd, Vec::new()));
                    }
                }
            }
            for (def, ranges) in &wrap_models {
                let vd = version_rename_at(def, &sv, func, block.id, end);
                // The model is `Eq(dest_var, modular-ite)`: dest is the lhs, the rhs is
                // the modular expression whose free vars are the (input-free) operands.
                let entry = match &vd {
                    Formula::Eq(dest, rhs) => dest
                        .var_name()
                        .map(|v| (v.to_string(), formula_free_var_vec(rhs))),
                    _ => None,
                };
                if let Some((subject, rhs_fvs)) = entry {
                    let vranges: Vec<Formula> = ranges
                        .iter()
                        .map(|r| version_rename_at(r, &sv, func, block.id, end))
                        .collect();
                    cand_head.push((subject, rhs_fvs, vd, vranges));
                }
            }
            // Trust (Clean-origin definitional grounding): the Clean-origin call
            // result definitions, versioned at THIS assert's use point exactly like
            // `wrap_models` — for a single-assignment call destination the
            // use-point version IS the call's post-call version, so the renamed
            // equality is the def-point fact (the identical argument). The model
            // is `Eq(dest_var, rhs-over-actuals)`; the rhs free vars are the
            // actuals the fixpoint must already have grounded.
            for (def, ranges) in &clean_origin_models {
                let vd = version_rename_at(def, &sv, func, block.id, end);
                let entry = match &vd {
                    Formula::Eq(dest, rhs) => dest
                        .var_name()
                        .map(|v| (v.to_string(), formula_free_var_vec(rhs))),
                    _ => None,
                };
                if let Some((subject, rhs_fvs)) = entry {
                    let vranges: Vec<Formula> = ranges
                        .iter()
                        .map(|r| version_rename_at(r, &sv, func, block.id, end))
                        .collect();
                    cand_head.push((subject, rhs_fvs, vd, vranges));
                }
            }
            // Straight-line statement / checked-arith defs (collected + soundness-gated
            // above), versioned at THIS assert's use-point. For a single-assignment var the
            // use-point version equals the def-point version, so the renamed equality is a
            // true fact (see the soundness note at the `stmt_defs` construction).
            for (def, ranges) in stmt_defs {
                let vd = version_rename_at(def, &sv, func, block.id, end);
                let entry = match &vd {
                    Formula::Eq(a, b) => a
                        .var_name()
                        .map(|v| (v.to_string(), formula_free_var_vec(b)))
                        .or_else(|| {
                            b.var_name()
                                .map(|v| (v.to_string(), formula_free_var_vec(a)))
                        }),
                    _ => None,
                };
                if let Some((subject, rhs_fvs)) = entry {
                    let vranges: Vec<Formula> = ranges
                        .iter()
                        .map(|r| version_rename_at(r, &sv, func, block.id, end))
                        .collect();
                    cand_head.push((subject, rhs_fvs, vd, vranges));
                }
            }
            // Exact source-snapshot variants (`stmt_defs_at_establish`) sit logically
            // between `cand_head` and `cand_tail` and are borrowed in-place without
            // cloning per target block.
            // Trust (derived trivial-setter summary): the setter post-call facts and
            // their copy-chain links (see the `setter_defs` construction above). Emitted
            // UNVERSIONED and version-renamed HERE at the assert use-point — the same
            // reaching-def use-point versioning `stmt_defs` use above — so the target's
            // token unifies with the assert formula's own token by construction (robust
            // to the flip). Only a fact still LIVE here is renamed: every name keeps the
            // version it had where the fact was established, so the rename states the
            // same value the fact was about (2026-09-30).
            for (raw, live) in setter_defs {
                if !live
                    .iter()
                    .all(|(name, tok)| sv.version_token_at(func, block.id, end, name) == *tok)
                {
                    continue;
                }
                let vd = version_rename_at(raw, &sv, func, block.id, end);
                let entry = match &vd {
                    Formula::Eq(a, b) => a
                        .var_name()
                        .map(|v| (v.to_string(), formula_free_var_vec(b)))
                        .or_else(|| {
                            b.var_name()
                                .map(|v| (v.to_string(), formula_free_var_vec(a)))
                        }),
                    _ => None,
                };
                if let Some((subject, rhs_fvs)) = entry {
                    cand_tail.push((subject, rhs_fvs, vd, Vec::new()));
                }
            }
            // EXACT PIN 2, at this assert's use point. The pin's subject `dest` is
            // function-wide single-assignment, so its use-point version IS its
            // def-point version and the renamed equality is the same true fact
            // (identical argument to `stmt_defs` above). The carrier is bare and
            // version-free by construction — it names a place's discriminant, not a
            // local — so the rename leaves it alone and the two ends unify.
            for (def, ranges, carrier) in &discriminant_pins {
                let vd = version_rename_at(def, &sv, func, block.id, end);
                let subject = match &vd {
                    Formula::Eq(dest, _) => dest.var_name().map(str::to_string),
                    _ => None,
                };
                if let Some(subject) = subject {
                    cand_tail.push((subject, vec![carrier.clone()], vd, ranges.clone()));
                }
            }
            loop {
                let mut changed = false;
                for (cand_idx, (v, rhs, _, _)) in cand_head
                    .iter()
                    .chain(stmt_defs_at_establish.iter())
                    .chain(cand_tail.iter())
                    .enumerate()
                {
                    if is_free(v) || resolved.contains(v) {
                        continue;
                    }
                    if rhs.iter().all(|r| is_free(r) || resolved.contains(r)) {
                        resolved.insert(v.clone());
                        resolution_order.push(v.clone());
                        resolved_def.insert(v.clone(), cand_idx);
                        changed = true;
                    }
                }
                if !changed {
                    break;
                }
            }
        }
        let empty_establish: [(String, Vec<String>, Formula, Vec<Formula>); 0] = [];
        let stmt_defs_at_establish = lazy_grounding_defs
            .get()
            .map_or(empty_establish.as_slice(), |(_, _, est, _)| est.as_slice());
        let cand_at = |idx: usize| -> Option<&(String, Vec<String>, Formula, Vec<Formula>)> {
            let head_len = cand_head.len();
            if idx < head_len {
                return cand_head.get(idx);
            }
            let mid = idx - head_len;
            let est_len = stmt_defs_at_establish.len();
            if mid < est_len {
                stmt_defs_at_establish.get(mid)
            } else {
                cand_tail.get(mid - est_len)
            }
        };
        // BIDIRECTIONAL EXACTNESS: this formula is consumed in both directions —
        // UNSAT discharges the assertion and SAT reports a real counterexample. We
        // must therefore keep the complete panic-path violation. In particular,
        // dropping an ungrounded conjunct would weaken the formula: weaker-UNSAT is
        // sufficient for the proof direction, but weaker-SAT is not a witness for
        // the original formula and can false-refute a safe program. Decline the
        // whole candidate whenever even one free variable remains unresolved.
        // Grounded iff non-trivial AND every free var is input-free or exactly pinned.
        let grounded = !fv.is_empty()
            && (!needs_grounding || fv.iter().all(|v| is_free(v) || resolved.contains(v)));
        if !grounded && !debug {
            continue;
        }
        // RELEVANCE SLICE: conjoin ONLY the defs transitively reachable from the
        // formula's free vars. Walk fv -> its grounding def -> that def's rhs vars to
        // a fixpoint, keeping each visited var's def + range facts. An irrelevant
        // resolvable path-def (e.g. a leftover `_3 == (_4 == _5)` whose Bool subject
        // is not free) is EXCLUDED: a def of a var unreachable from fv cannot
        // constrain the path-feasibility formula, so dropping it is sound in BOTH
        // directions — yet conjoining it empirically trips ay's proof production
        // (UNSAT but no strict-checked artifact -> falls back to runtime-checked
        // instead of Proved).
        let mut relevant_resolved: FxHashSet<String> = FxHashSet::default();
        let mut used_defs: Vec<Formula> = Vec::new();
        let mut used_ranges: Vec<Formula> = Vec::new();
        if grounded && !resolved_def.is_empty() {
            let mut needed: Vec<String> = fv.iter().cloned().collect();
            let mut seen: FxHashSet<String> = needed.iter().cloned().collect();
            let mut qi = 0;
            while qi < needed.len() {
                let Some((_, rhs, df, ranges)) =
                    resolved_def.get(&needed[qi]).copied().and_then(cand_at)
                else {
                    qi += 1;
                    continue;
                };
                let v = needed[qi].clone();
                qi += 1;
                let subject_is_bool = match df {
                    Formula::Eq(lhs, rhs) => {
                        (lhs.var_name() == Some(v.as_str())
                            && lhs.var_sort() == Some(&Sort::Bool))
                            || (rhs.var_name() == Some(v.as_str())
                                && rhs.var_sort() == Some(&Sort::Bool))
                    }
                    _ => false,
                };
                relevant_resolved.insert(v);
                if !subject_is_bool {
                    used_defs.push(df.clone());
                }
                used_ranges.extend(ranges.iter().cloned());
                for r in rhs {
                    if seen.insert(r.clone()) {
                        needed.push(r.clone());
                    }
                }
            }
        }
        // OVERLAPPING-PLACE GUARD — the half of exact pin 1 that keeps the
        // false-refutation channel `3d1446f4c7` closed CLOSED.
        //
        // Admitting a component of an input-free root as free is sound only while
        // no OTHER name in the SAME conjunction denotes storage that component can
        // overlap. If `o` and `o@1.0.0` are both free, a model may pick them
        // inconsistently — `o` the `None` value and `o@1.0.0` some payload — and
        // report SAT for a path no input can take: a refutation of correct Rust,
        // which is strictly worse than the missing refutation this lane is
        // restoring. The same applies to an ancestor reached through a pin
        // (`p == o@1.0` alongside a free `o@1.0.0`), to two DOWNCASTS of one enum
        // (whose variants share storage), and to the `Discriminant` carrier against
        // its own bare root.
        //
        // The set judged is exactly the conjunction this site will emit: the path
        // formula's own free variables, every definition and range fact the
        // relevance slice selected, and the declared preconditions assumed at
        // entry. A candidate the slice dropped constrains nothing and cannot
        // connect two names. The only facts conjoined AFTER this point are the
        // three type-range reattachments, which are per-name interval bounds
        // (`0 <= v <= u32::MAX`) on names already present — they state no relation
        // between two places, so they cannot create the inconsistency this guard
        // looks for.
        //
        // Fail-closed in one direction only: a conflict DECLINES the candidate, so
        // the obligation stays an undischarged coverage gap exactly as it is today.
        let has_projected_or_discr_name = precondition_has_projected_or_discr
            || fv.iter().any(|n| refutation_name_has_projection_or_discr(n))
            || used_defs.iter().chain(used_ranges.iter()).any(|f| {
                trust_types::any_free_variable_name(f, &mut |name| {
                    refutation_name_has_projection_or_discr(name)
                })
            });
        let mut conjunction_names: Vec<String>;
        let aliasing_pair = if has_projected_or_discr_name {
            let mut conjunction_name_set: FxHashSet<String> = fv.iter().cloned().collect();
            conjunction_name_set.extend(precondition_names.iter().cloned());
            for f in used_defs.iter().chain(used_ranges.iter()) {
                trust_types::for_each_free_variable_name(f, &mut |name| {
                    if !conjunction_name_set.contains(name) {
                        conjunction_name_set.insert(name.to_string());
                    }
                });
            }
            if conjunction_name_set.len() > 1 {
                conjunction_names = conjunction_name_set.into_iter().collect();
                conjunction_names.sort_unstable();
                let conjunction_spelled: Vec<std::borrow::Cow<'_, str>> = conjunction_names
                    .iter()
                    .map(|name| {
                        discriminant_carrier_as_projection(name).map_or(
                            std::borrow::Cow::Borrowed(name.as_str()),
                            std::borrow::Cow::Owned,
                        )
                    })
                    .collect();
                let mut by_root: Vec<(&str, usize)> = conjunction_spelled
                    .iter()
                    .enumerate()
                    .map(|(idx, s)| (place_name_root(s), idx))
                    .collect();
                by_root.sort_unstable();
                let mut min_pair: Option<(usize, usize)> = None;
                for group in by_root.chunk_by(|a, b| a.0 == b.0) {
                    if group.len() < 2 {
                        continue;
                    }
                    for (pos, &(_, i)) in group.iter().enumerate() {
                        if min_pair.is_some_and(|(best_i, _)| i > best_i) {
                            break;
                        }
                        let a_spelled = conjunction_spelled[i].as_ref();
                        for &(_, j) in &group[pos + 1..] {
                            if min_pair.is_some_and(|best| (i, j) >= best) {
                                break;
                            }
                            if refutation_names_may_alias(a_spelled, conjunction_spelled[j].as_ref())
                            {
                                min_pair = Some((i, j));
                                break;
                            }
                        }
                    }
                }
                min_pair
                    .map(|(i, j)| (conjunction_names[i].as_str(), conjunction_names[j].as_str()))
            } else {
                None
            }
        } else {
            None
        };
        if debug {
            let mut fvs: Vec<&String> = fv.iter().collect();
            fvs.sort();
            eprintln!(
                "[ASSERT_REFUTE] block={:?} grounded={grounded} pinned={} alias={aliasing_pair:?} free={fvs:?}\n  formula={formula:?}",
                block.id,
                relevant_resolved.len(),
            );
            // The candidate definitions and what the fixpoint actually resolved.
            // `grounded=false` with a full candidate list and an EMPTY `resolved`
            // is the signature of a spelling the `is_free` strip does not reach
            // (measured 2026-09-10: the `@variant.field` payload projection of an
            // input-free parameter). Diagnostic-only; reads nothing back.
            for (subject, rhs, definition, _) in cand_head
                .iter()
                .chain(stmt_defs_at_establish.iter())
                .chain(cand_tail.iter())
            {
                eprintln!("[ASSERT_CAND]   {subject} <- rhs={rhs:?} def={definition:?}");
            }
            let mut resolved_sorted: Vec<&String> = resolved.iter().collect();
            resolved_sorted.sort();
            eprintln!("[ASSERT_CAND] block={:?} resolved={resolved_sorted:?}", block.id);
        }
        if !grounded {
            continue;
        }
        if aliasing_pair.is_some() {
            continue;
        }
        if !relevant_resolved.is_empty() {
            used_defs.extend(used_ranges);
            if !used_defs.is_empty() {
                used_defs.push(formula);
                formula = Formula::And(used_defs);
            }
            // A selected Boolean definition is an exact equality `v == rhs`
            // whose rhs was already grounded.  Existentially eliminating `v`
            // by capture-avoiding substitution is equisatisfiable with
            // conjoining that equality, but leaves AY the input-level branch
            // predicate instead of a chain of synthetic MIR Boolean aliases.
            // Preserve non-Boolean definitions above so diagnostic models keep
            // their program-value bindings.
            for v in resolution_order.iter().rev() {
                if !relevant_resolved.contains(v) {
                    continue;
                }
                let Some((_, _, definition, _)) = resolved_def.get(v).copied().and_then(cand_at)
                else {
                    continue;
                };
                let Formula::Eq(lhs, rhs) = definition else { continue };
                let replacement = if lhs.var_name() == Some(v.as_str())
                    && lhs.var_sort() == Some(&Sort::Bool)
                {
                    rhs.as_ref()
                } else if rhs.var_name() == Some(v.as_str()) && rhs.var_sort() == Some(&Sort::Bool)
                {
                    lhs.as_ref()
                } else {
                    continue;
                };
                formula = crate::quantifier_tiers::substitute(&formula, v, replacement);
            }
        }
        // Contract consumption (assume-at-entry): conjoin the function's
        // DECLARED, extraction-GATED preconditions (`func.preconditions` — the
        // gated set only; never re-parse contracts here) into the panic-path
        // feasibility formula. Without this, the refute lane freely violates
        // `#[trust::requires]` in its counterexamples (e.g. picking lo > hi
        // against requires(lo <= hi)) and REFUTES guards the contract already
        // excludes. SOUNDNESS, refute direction: SAT-with-requires is a
        // strictly STRONGER counterexample claim (the model also honors the
        // contract); conjoining can only turn SAT into UNSAT — i.e. drop
        // refutations of contract-violating inputs, exactly the intent.
        // UNSAT direction: "unreachable under the assumed requires" is sound
        // because every Trust-verified caller carries a `VcKind::Precondition`
        // PROVE obligation for the callee's full declared predicate (the
        // assume/prove pairing; see generate_callsite_precondition_vcs) — an
        // assumption is never free. Preconditions carry bare ENTRY-parameter
        // debug names (the S2c exemption keeps entry reads bare), so they bind
        // exactly the entry values; a precondition over a reassigned place is
        // name-disjoint from versioned reads and inert.
        if !safe_preconditions.is_empty() {
            let mut cs = Vec::with_capacity(safe_preconditions.len() + 1);
            cs.extend(safe_preconditions.iter().cloned());
            cs.push(formula);
            formula = Formula::And(cs);
        }
        // Reattach the Rust type invariants erased when fixed-width integers are
        // lowered to unbounded `Sort::Int`. This lane consumes SAT as a REAL
        // counterexample, so an out-of-range model is just as unsound as an
        // ungrounded computed value: without `0 <= value <= 255`, for example,
        // `assert!(value <= 255)` on a `u8` input is spuriously satisfiable at
        // `value = 256`. These are true facts at every reached Rust program
        // point, hence safe in both directions: they remove only impossible SAT
        // models and cannot hide an executable panic. Apply all three established
        // range reattachment lanes after preconditions/grounding so fields and
        // exact computed locals already present in the final formula are covered.
        formula = conjoin_arg_local_field_type_ranges(func, formula);
        // ── PER-PATH SPLIT OF THE PANIC-PATH FEASIBILITY FORMULA ─────────────
        // Emit ONE obligation PER CONTROL-FLOW PATH instead of one for the whole
        // `Or`. `split_path_feasibility_disjuncts` performs the exact
        // distributivity rewriting `And(C, Or(d…)) ≡ Or_i And(C, d_i)` (see its
        // doc comment for the two-verdict soundness argument: a part's model is
        // verbatim a model of the whole, and the whole is UNSAT iff every part
        // is). It DECLINES — returning the single input formula — whenever there
        // is no top-level `Or` to split, so every other shape keeps today's
        // exact behaviour.
        //
        // The consumer already requires a definite verdict on EVERY emitted VC
        // (`refute_full_assert_obligations`: `refuted == 0 && left_unknown == 0`),
        // which is exactly the "all parts proved" side condition the rewriting
        // needs; one unknown part leaves the assert undischarged, as it must.
        //
        // MEASURED (real MIR, `proved/cursor_clamp_assert.rs`, in-process ay):
        //
        //   combined `And(C, Or(d0,d1,d2))`  -> Unknown
        //                                       ("(incomplete self-check-rejected)":
        //                                        ay computes UNSAT and then REJECTS
        //                                        ITS OWN PROOF)
        //   split into 3 obligations         -> Proved, Proved, Proved
        //                                       (SmtBacked, each kernel-certified)
        //
        // The rejection is not about formula SIZE: handing ay the same predicate
        // pre-distributed as ONE obligation, `Or(And(C,d0), And(C,d1), And(C,d2))`,
        // was measured to be Unknown for the same reason. It is the separate
        // QUERIES that ay can certify, so a genuine per-VC split is what the lane
        // needs.
        //
        // The mutant still refutes: its 2 parts split 1 Failed / 1 Proved, so
        // `refuted > 0` keeps the whole-function catch-all open exactly as before.
        //
        // Trust (NEW-EXEMPT-SPLIT): the parts are the block's candidates, and
        // ONLY together do they decide it — the block is unreachable iff every
        // part is UNSAT. Each part carries its block, and the block records how
        // many parts it emitted, so a consumer can tell "every path of this block
        // proved" from "as many proofs as there are blocks".
        let parts = crate::guards::split_path_feasibility_disjuncts(&formula);
        targets[target_index].1 = parts.len();
        let fn_sym: trust_types::Symbol = func.name.as_str().into();
        let message = v2_panic_call_vc_message(func, callee, args);
        for part in parts {
            out.push((
                VerificationCondition {
                    kind: VcKind::Assertion {
                        message: message.clone(),
                    },
                    function: fn_sym,
                    location: span.clone(),
                    formula: part,
                    contract_metadata: None,
                    obligation: None,
                },
                Some(block.id),
            ));
        }
        // ── END PER-PATH SPLIT ───────────────────────────────────────────────
    }
    // verifier-perf (mid-generation work-bound): a function whose VC-gen tripped the work
    // budget gets NO refutation claims — emit an empty set so it can never produce a
    // SPURIOUS guaranteed-violation from leaf-degraded types. SOUNDNESS: withholding a
    // refutation is the fail-closed direction (it can only DROP a refutation, never
    // manufacture one). (The T9 unused-annotation rows below are also withheld here —
    // a budget-tripped function keeps unresolved obligations, so it can never reach a
    // green gate that an unused annotation would need to poison.) Every target block
    // it visited is then DECLINED in the coverage record.
    if crate::gen_work_tripped() {
        return AssertRefutationCandidates {
            vcs: Vec::new(),
            coverage: AssertRefutationCoverage {
                origins: Vec::new(),
                targets: targets.into_iter().map(|(block, _)| (block, 0)).collect(),
            },
        };
    }
    // FINAL pass: collapse SSA locals' version tokens to the bare name (see
    // `normalize_ssa_version_tokens`). In THIS lane SAT = refuted, and the
    // collapse only ADDS true identities — it removes spurious SAT (a model
    // assigning `h#s6_t` and bare `h` different values despite one write),
    // never a genuine refutation (real traces satisfy the identity).
    for (vc, _) in &mut out {
        vc.formula = normalize_ssa_version_tokens_owned(
            func,
            std::mem::replace(&mut vc.formula, Formula::Bool(true)),
        );
    }
    // Trust (T9 contract-panic): unused-annotation enforcement, end of per-fn VC
    // generation for the refute lane. A `contract_panic` annotation that matched
    // NO panic call in this function mints an always-SAT (`Bool(true)`) Assertion
    // VC — in THIS lane SAT = refuted, so it surfaces as a guaranteed FAILED row.
    // An annotation on panic-free code is an ERROR: it must never sit dormant
    // waiting to mask a panic a future edit introduces. It belongs to no target
    // block.
    out.extend(contract_panic_unused_vcs(func).into_iter().map(|vc| (vc, None)));
    let (vcs, origins) = out.into_iter().unzip();
    AssertRefutationCandidates { vcs, coverage: AssertRefutationCoverage { origins, targets } }
}

// Trust (W4/spine-derives-unreachable): moved to
// `trust_types::terminator_obligations::is_assertion_panic_call`; see the
// delegation note on `v2_is_unreachable_panic_call`.
pub(super) fn v2_is_assertion_panic_call(callee: &str) -> bool {
    trust_types::terminator_obligations::is_assertion_panic_call(callee)
}

/// Trust (interprocedural pf discharge — panic-callee exemption support): whether
/// `block` is a user `assert!`/`panic!` FAILURE block the `-full` refutation lane
/// (`generate_full_assert_refutation_vcs`) targets — the recognizer that lane's
/// candidate loop itself calls (assertion-panic entrypoint call, excluding the
/// `unreachable!()` sentinel). Exported so the compiler-side call gate can exempt
/// PRECISELY the blocks the refutation lane covers.
///
/// Recognizing a block as a target says nothing about whether the lane decided
/// it: a target block is split into one candidate per path, and one the lane
/// cannot ground emits none. Whether a target block is proved unreachable is a
/// per-block question — [`AssertRefutationCoverage::target_block_proved`] —
/// never a count of candidates (NEW-EXEMPT-SPLIT, docs/KNOWN_HAZARDS.md).
pub fn is_assert_refutation_target_block(block: &trust_types::BasicBlock) -> bool {
    let Terminator::Call { func: callee, args, .. } = &block.terminator else {
        return false;
    };
    (v2_is_assertion_panic_call(callee)
        || trust_types::terminator_obligations::is_bare_panic_call(callee))
        && !v2_is_unreachable_sentinel_panic(callee, args)
}

/// The bare panic intrinsic `core::panicking::panic` is the lowering of BOTH
/// `unreachable!()` and `assert!(cond)` / `panic!("static str")`, distinguished
/// only by the static message argument. We must emit a VC ONLY for the
/// `unreachable!()` sentinel: an `assert!`/`panic!` panic site is already covered
/// by the existing obligation path, and emitting a second (dataflow-starved)
/// terminator VC for it false-FAILs a provable assert (e.g. cursor_clamp_assert,
/// whose merged clamp definition does not reach a raw panic-terminator VC). The
/// `unreachable!()` panic, by contrast, has NO prior VC, so its modulo/path-guard
/// facts had no goal to discharge (modulo_unreachable fell back to runtime-checked).
/// Match the well-known sentinel "entered unreachable code"; if the wording ever
/// drifts this fails CLOSED (reverts to runtime-checked, never a false-prove).
// Trust (W4/spine-derives-unreachable): moved to
// `trust_types::terminator_obligations::is_unreachable_sentinel_panic`; see
// the delegation note on `v2_is_unreachable_panic_call`.
pub(super) fn v2_is_unreachable_sentinel_panic(callee: &str, args: &[Operand]) -> bool {
    trust_types::terminator_obligations::is_unreachable_sentinel_panic(callee, args)
}

/// The UTF-8 contents of a `&str` constant operand, if `op` is one.
pub(super) fn operand_str_constant(op: &Operand) -> Option<String> {
    match op {
        Operand::Constant(ConstValue::Str { bytes }) => {
            Some(String::from_utf8_lossy(bytes).into_owned())
        }
        _ => None,
    }
}

/// The raw BYTES of a `&str`/byte-array constant operand, if `op` is one.
/// T7 (fmt-template): unlike `operand_str_constant`, no lossy UTF-8
/// conversion — the `format_args!` TEMPLATE carries non-UTF-8 control bytes
/// (placeholder heads like `0xC0`) that must survive for the decoder to walk.
pub(super) fn operand_str_bytes(op: &Operand) -> Option<&[u8]> {
    match op {
        Operand::Constant(ConstValue::Str { bytes }) => Some(bytes),
        _ => None,
    }
}

/// T7 (fmt-template): is `callee` the template-based
/// `core::fmt::Arguments::new::<N, M>` ctor (spelled with the turbofish, e.g.
/// `core::fmt::Arguments::<'_>::new::<10, 1>`, or bare `…Arguments::new` in
/// synthetic MIR)? The `::new::<` / trailing-`::new` boundary check keeps the
/// sibling ctors from matching: `new_const`/`from_str` (const-message ctors,
/// harvested by their own arm) and `rt::Argument::new_display`/`new_debug`/…
/// (per-ARGUMENT ctors — also excluded by the `Arguments` [plural] substring).
/// Same name-shape laxness as the existing `from_str`/`new_const` gate.
pub(crate) fn is_arguments_template_new_call(callee: &str) -> bool {
    callee.contains("Arguments") && (callee.contains("::new::<") || callee.ends_with("::new"))
}

/// T7 (fmt-template): every `&str`/byte-array constant that can define `op` —
/// the operand itself, or (the real post-lowering shape,
/// `_9 = const b"…"; Arguments::new(move _9, copy _10)`) each whole-body
/// bare-local `Use` def of it. Mirrors the enclosing Arguments-ctor chase:
/// whole-body scan, bare locals only (a projected def is skipped, fail-closed),
/// and EVERY matching def is harvested rather than guessing which one flows.
pub(super) fn template_const_bytes_candidates<'f>(
    func: &'f VerifiableFunction,
    op: &'f Operand,
) -> Vec<&'f [u8]> {
    if let Some(bytes) = operand_str_bytes(op) {
        return vec![bytes];
    }
    let (Operand::Copy(p) | Operand::Move(p)) = op else { return Vec::new() };
    if !p.projections.is_empty() {
        return Vec::new();
    }
    let mut out = Vec::new();
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            if let Statement::Assign { place: dest, rvalue: Rvalue::Use(inner), .. } = stmt
                && dest.local == p.local
                && dest.projections.is_empty()
                && let Some(bytes) = operand_str_bytes(inner)
            {
                out.push(bytes);
            }
        }
    }
    out
}

/// T7 (contract-panic through panic_fmt): the concatenated LITERAL string
/// pieces of a `format_args!` TEMPLATE byte sequence, or `None` when `bytes`
/// is not a well-formed template.
///
/// The encoding is the one defined in library/core/src/fmt/mod.rs ("Internal
/// representation", representation 2 — this repo's vendored core is the source
/// of truth), decoded defensively:
///   * `0x00` — end of template. It must be the FINAL byte here: the template
///     constant is exactly the `[u8; N]` array `format_args!` emits, so
///     trailing bytes mean the shape is not what we think it is — fail closed;
///   * `0x01..=0x7F` — short literal piece: that many UTF-8 bytes follow;
///   * `0x80` — long literal piece: u16 LE length, then that many bytes;
///   * `0xC0..=0xFF` — placeholder: the head byte's low bits say which option
///     fields follow (flags 4B if bit0, width 2B if bit1, precision 2B if
///     bit2, arg_index 2B if bit3 — the exact skip arithmetic of
///     `Arguments::estimated_capacity`); the runtime VALUE is never in the
///     template, so a placeholder contributes NOTHING to the harvest;
///   * `0x81..=0xBF` — not a valid part start: fail closed.
/// EVERY malformed case returns `None` — the caller then records no message,
/// so a `contract_panic` annotation can only FAIL to match (surfacing the
/// original FAILED row / the unused-annotation error), never falsely match: a
/// decoder that guessed wrong could otherwise harvest option/length bytes as
/// "text" and message-match a payload the real literal pieces don't contain.
///
/// CONCATENATION semantics (the T7 task shape): pieces on both sides of a
/// placeholder are joined, so `message_contains = "expected got"` does match
/// `panic!("expected {} got {}", a, b)`'s pieces even though the formatted
/// message interleaves runtime values. This errs toward matching the
/// annotation — acceptable because the contract-panic marker only reclassifies
/// a FAILED row in an explicit survey lane (the strict default never
/// rewrites) — and keeps the unused-annotation check from
/// false-ERRORING on payloads that span a placeholder-split piece boundary.
pub(crate) fn fmt_template_literal_pieces(bytes: &[u8]) -> Option<String> {
    let mut out = String::new();
    let mut i = 0usize;
    loop {
        let head = *bytes.get(i)?;
        i += 1;
        match head {
            0 => {
                // End marker: must close the template exactly (see above).
                return (i == bytes.len()).then_some(out);
            }
            1..=0x7F => {
                let len = head as usize;
                out.push_str(core::str::from_utf8(bytes.get(i..i + len)?).ok()?);
                i += len;
            }
            0x80 => {
                let len = usize::from(u16::from_le_bytes([*bytes.get(i)?, *bytes.get(i + 1)?]));
                i += 2;
                out.push_str(core::str::from_utf8(bytes.get(i..i + len)?).ok()?);
                i += len;
            }
            0xC0..=0xFF => {
                let skip = usize::from(head & 1 != 0) * 4
                    + usize::from(head & 2 != 0) * 2
                    + usize::from(head & 4 != 0) * 2
                    + usize::from(head & 8 != 0) * 2;
                // The option fields must actually be present.
                bytes.get(i..i + skip)?;
                i += skip;
            }
            0x81..=0xBF => return None,
        }
    }
}

/// Trust (T9 contract-panic): the compile-time-constant `&str` messages of a
/// panic call with the given `callee` and `args` — the shared message harvest for the
/// site+message matcher and the unused-annotation check, so the two can never
/// drift.
///
/// Four shapes are recognized:
///   * an authenticated outlined default-message entrypoint in
///     `core::panicking`, whose fixed message is carried by its callee name
///     rather than an argument;
///   * a direct `&str` constant argument (`core::panicking::panic("msg")`,
///     `assert!`'s generated message) — `operand_str_constant`, the same
///     `ConstValue::Str` extraction `v2_is_unreachable_sentinel_panic` uses;
///   * the POST-INLINE lowering of `panic!("static msg")`, where the constant
///     sits one call behind the panic entry:
///     `_a = fmt::Arguments::from_str("static msg"); panic_fmt(move _a)` —
///     a bare `Move`/`Copy` argument local is chased (one level, whole-body)
///     to its defining `fmt::Arguments` `from_str`/`new_const` constructor
///     call and THAT call's `&str` constants are harvested;
///   * T7: the FORMATTED lowering `panic!("prefix {}", x)`, where the same
///     chase lands on the template-based ctor
///     `_a = fmt::Arguments::new::<N, M>(move _t, …)` with
///     `_t = const b"\x07prefix \xc0\x00"` one `Use` def further back
///     (`template_const_bytes_candidates`) — the template's literal pieces
///     are decoded (`fmt_template_literal_pieces`, fail-closed on any
///     malformed byte) and their CONCATENATION is one harvested message.
///     Previously formatted messages never matched at all, forcing
///     const-message rewrites in user code (the aterm-alloc evidence).
///
/// The runtime VALUES of a formatted message are never in the template, so
/// `message_contains` text that only occurs in a runtime value still cannot
/// match — fail-closed (the T9 annotation-surface contract). On OLDER
/// toolchains whose `format_args!` lowers to `Arguments::new_v1` with a
/// `&[&str; N]` pieces array, extraction lowers that pieces constant to the
/// content-free `OpaqueConst`, so those messages (soundly) remain unmatched.
pub(super) fn panic_call_const_str_messages(
    func: &VerifiableFunction,
    callee: &str,
    args: &[Operand],
) -> Vec<String> {
    let mut msgs: Vec<String> = args.iter().filter_map(operand_str_constant).collect();
    if let Some(message) = trust_types::terminator_obligations::default_msg_panic_message(callee) {
        msgs.push(message.to_string());
    }
    if !super::terminator_presence_for(func).has_bare_dest_call {
        return msgs;
    }
    for arg in args {
        let (Operand::Copy(p) | Operand::Move(p)) = arg else { continue };
        if !p.projections.is_empty() {
            continue;
        }
        for block in &func.body.blocks {
            if let Terminator::Call { func: callee, args: ctor_args, dest, .. } = &block.terminator
                && dest.local == p.local
                && dest.projections.is_empty()
                && callee.contains("Arguments")
            {
                if callee.contains("from_str") || callee.contains("new_const") {
                    msgs.extend(ctor_args.iter().filter_map(operand_str_constant));
                } else if is_arguments_template_new_call(callee)
                    && let Some(template_op) = ctor_args.first()
                {
                    for bytes in template_const_bytes_candidates(func, template_op) {
                        if let Some(concat) = fmt_template_literal_pieces(bytes) {
                            msgs.push(concat);
                        } else if let Ok(s) = std::str::from_utf8(bytes) {
                            // THIS toolchain's `Arguments::new(&[&str] pieces, args)` template: the
                            // extractor concatenates the literal pieces into a plain-UTF-8 `Str`
                            // (not the `\x07`-length byte-template `fmt_template_literal_pieces`
                            // decodes), so use the raw pieces string directly. This is what lets
                            // contract_panic see a FORMATTED panic's message.
                            msgs.push(s.to_string());
                        }
                    }
                }
            }
        }
    }
    msgs
}

/// Trust (T9 contract-panic): does any of the enclosing fn's
/// `contract_panic(message_contains = "...")` payloads occur as a substring of a
/// compile-time-constant `&str` message of this panic call
/// (`panic_call_const_str_messages`)? This is the site+message match: the
/// payload set is pinned to `func.def_path` (see
/// `contract_panic_annotations_for` — never a stale cross-function hint), and
/// a runtime-formatted message can never be message-matched, fail-closed.
/// Empty payloads never match (extraction already rejects them; belt+braces).
pub(super) fn contract_panic_annotation_matches(
    func: &VerifiableFunction,
    callee: &str,
    args: &[Operand],
) -> bool {
    let payloads = crate::contract_panic_annotations_for(&func.def_path);
    if payloads.is_empty() {
        return false;
    }
    panic_call_const_str_messages(func, callee, args)
        .iter()
        .any(|msg| payloads.iter().any(|p| !p.trim().is_empty() && msg.contains(p.as_str())))
}

/// Trust (T9 contract-panic): the Assertion message for a panic-call VC. When a
/// contract-panic annotation message-matches this exact call site, the message
/// is prefixed with `CONTRACT_PANIC_VC_MARKER`; the VC is still SOLVED normally
/// (the marker never changes a verdict). The compiler's verify pass reclassifies
/// a resulting FAILED transport row — in a survey lane only — into a visible
/// `contract-panic:` row; an Unknown/Proved row is left untouched, and the
/// strict default never rewrites at all.
pub(super) fn v2_panic_call_vc_message(
    func: &VerifiableFunction,
    callee: &str,
    args: &[Operand],
) -> String {
    if contract_panic_annotation_matches(func, callee, args) {
        format!("{}panic call: {callee}", trust_types::assumption::CONTRACT_PANIC_VC_MARKER)
    } else {
        format!("panic call: {callee}")
    }
}

/// Does `func` participate in a nested-body (closure/coroutine) relationship — i.e.
/// could a `contract_panic` annotation it holds legitimately match a panic that is not
/// visible in this body? True when `func` IS a synthetic nested body (its def_path names
/// a `{closure`/`{coroutine`, so it inherited the annotation from a parent) OR when it
/// CREATES one (an `Aggregate(Closure/Coroutine/CoroutineClosure)` rvalue, whose child
/// body may carry the matching panic). A leaf that does neither cannot host the panic
/// elsewhere, so a panic-free leaf's annotation is genuinely stale.
pub(super) fn func_participates_in_nested_body(func: &VerifiableFunction) -> bool {
    if func.def_path.contains("{closure") || func.def_path.contains("{coroutine") {
        return true;
    }
    func.body.blocks.iter().any(|b| {
        b.stmts.iter().any(|s| {
            matches!(
                s,
                Statement::Assign {
                    rvalue: Rvalue::Aggregate(
                        AggregateKind::Closure { .. }
                            | AggregateKind::Coroutine { .. }
                            | AggregateKind::CoroutineClosure { .. },
                        _,
                    ),
                    ..
                }
            )
        })
    })
}

/// Trust (T9 contract-panic): one always-refuted VC per `contract_panic`
/// annotation that matched NO panic call in `func` — the unused-annotation
/// ERROR. USED means: some `Terminator::Call` whose callee is a recognized
/// panic entry point (`v2_is_assertion_panic_call` or the bare `::panic`
/// intrinsic — the same recognizer set as the panic-call VC mint sites) carries
/// a constant message containing the payload, either in its arguments or its
/// authenticated outlined entrypoint. The check is SYNTACTIC
/// over the body (not over which lane happened to mint/solve a VC), so a
/// guarded-but-provably-unreachable panic still counts as used while a function
/// with no matching panic text at all always errors. The minted VC's formula is
/// `Bool(true)`: in the refute lane SAT = refuted, so it lands as a guaranteed
/// FAILED row (kind rewritten to `contract-panic-unused` by the verify pass —
/// which deliberately does NOT start with the `contract-panic:` prefix, so
/// targo counts it as a genuine failure, never a conditional pass).
pub(super) fn contract_panic_unused_vcs(func: &VerifiableFunction) -> Vec<VerificationCondition> {
    let payloads = crate::contract_panic_annotations_for(&func.def_path);
    if payloads.is_empty() {
        return Vec::new();
    }
    // Inheritance-aware gate (fixes the G1 contract_panic-inheritance interaction):
    // a `#[trust::contract_panic]` on a fn now propagates to that fn's nested bodies
    // (closures/coroutines) so their panics are excused. But the unused check runs
    // per-body and can only see THIS body's panic calls, so a body that HOLDS an
    // (inherited or declared) annotation whose matching panic lives in a DIFFERENT
    // body would be spuriously flagged "unused" — e.g. `successors` declares
    // `contract_panic("no action")` matched in its own body, yet its closure inherits
    // the annotation and, having no such panic, false-fails; and `require`'s panic
    // lives inside its `unwrap_or_else(|| panic!(...))` closure, so `require` itself
    // has no direct match.
    //
    // The excuse applies ONLY when this body participates in a nested-body
    // relationship — it either IS a synthetic nested body (its def_path names a
    // `{closure`/`{coroutine`, so it inherited the annotation from a parent whose
    // panic it need not carry) or it CREATES one (an `Aggregate(Closure/Coroutine/…)`
    // rvalue, so a matching panic may live in the child it spawned). A genuine LEAF
    // with no panic call and no nested body cannot host the matching panic anywhere,
    // so its annotation IS stale and must still mint the unused-marker VC (annotation
    // hygiene on panic-free code). Narrowing to this relationship — rather than
    // skipping every panic-call-free body — restores that stale-leaf signal while
    // keeping the G1 excuse. Soundness is unaffected either way: skipping the unused
    // check never manufactures a PROVE; an unexcused reachable panic in any body still
    // refutes at that body.
    let panic_calls: Vec<(&str, &[Operand])> = func
        .body
        .blocks
        .iter()
        .filter_map(|b| match &b.terminator {
            Terminator::Call { func: callee, args, .. }
                if v2_is_assertion_panic_call(callee)
                    || trust_types::terminator_obligations::is_bare_panic_call(callee) =>
            {
                Some((callee.as_str(), args.as_slice()))
            }
            _ => None,
        })
        .collect();
    if panic_calls.is_empty() && func_participates_in_nested_body(func) {
        return Vec::new();
    }
    let panic_call_msgs: Vec<Vec<String>> = panic_calls
        .iter()
        .map(|&(callee, args)| panic_call_const_str_messages(func, callee, args))
        .collect();
    let payload_used = |payload: &str| {
        !payload.trim().is_empty()
            && panic_call_msgs
                .iter()
                .any(|msgs| msgs.iter().any(|msg| msg.contains(payload)))
    };
    let fn_sym: trust_types::Symbol = func.name.as_str().into();
    payloads
        .iter()
        .filter(|p| !payload_used(p))
        .map(|payload| VerificationCondition {
            kind: VcKind::Assertion {
                message: format!(
                    "{}contract_panic(message_contains = \"{payload}\") matched no panic call in this function",
                    trust_types::assumption::CONTRACT_PANIC_UNUSED_VC_MARKER
                ),
            },
            function: fn_sym,
            location: func.span.clone(),
            formula: Formula::Bool(true),
            contract_metadata: None,
            obligation: None,
        })
        .collect()
}

// Trust (W4/spine-derives-unreachable): the four recognizers below MOVED to
// `trust_types::terminator_obligations` — one definition, two callers (this
// producer and the trust-ir spine), on the static_truth precedent. The bodies
// there are the verbatim moves; these wrappers keep every in-crate spelling.
pub(super) fn v2_is_unreachable_panic_call(callee: &str) -> bool {
    trust_types::terminator_obligations::is_unreachable_panic_call(callee)
}

pub(super) fn v2_is_unreachable_panic_chain(func: &VerifiableFunction, block_id: BlockId) -> bool {
    trust_types::terminator_obligations::is_unreachable_panic_chain(func, block_id)
}

// Trust: ungated — also used by the (ungated) `v2_may_reassigned_per_block`,
// which the hardened profile relies on for its precondition-staleness kill.
pub(crate) fn v2_terminator_targets(terminator: &Terminator) -> Vec<BlockId> {
    trust_types::terminator_obligations::terminator_targets(terminator)
}

pub(crate) fn for_each_v2_terminator_target(terminator: &Terminator, f: impl FnMut(BlockId)) {
    trust_types::terminator_obligations::for_each_terminator_target(terminator, f);
}

pub(crate) fn v2_terminator_has_target(terminator: &Terminator, needle: BlockId) -> bool {
    trust_types::terminator_obligations::terminator_has_target(terminator, needle)
}

#[cfg(test)]
mod wrapping_identity_tests {
    use trust_types::{BasicBlock, LocalDecl, SourceSpan, Ty, VerifiableBody, VerifiableFunction};

    use super::*;

    fn binary_func(ty: Ty) -> VerifiableFunction {
        let return_ty = ty.clone();
        VerifiableFunction {
            name: "wrap".into(),
            def_path: "crate::wrap".into(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: ty.clone(), name: None },
                    LocalDecl { index: 1, ty: ty.clone(), name: Some("a".into()) },
                    LocalDecl { index: 2, ty, name: Some("b".into()) },
                ],
                blocks: Vec::new(),
                arg_count: 2,
                return_ty,
                datatype_defs: Default::default(),
            },
            contracts: Vec::new(),
            preconditions: Vec::new(),
            postconditions: Vec::new(),
            spec: Default::default(),
            tuple_layouts: Default::default(),
        }
    }

    fn model(
        func: &VerifiableFunction,
        callee: &str,
        args: &[Operand],
        dest: &Place,
    ) -> Option<(Formula, Vec<Formula>)> {
        wrapping_call_assert_model(func, callee, args, dest, true, false, false, false)
    }

    #[test]
    fn wrapping_refutation_model_requires_closed_identity_and_exact_call_shape() {
        let func = binary_func(Ty::u64());
        let args = vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))];
        let marker = "@trust-rustc-total-primitive-method::core::num::<impl u64>::wrapping_add";
        assert!(model(&func, marker, &args, &Place::local(0)).is_some());
        // TG14: moving the authenticated signed method into the E6 marker
        // namespace must preserve its exact signed refutation semantics.
        for width in [8, 16, 32, 64] {
            let signed = binary_func(Ty::Int { width, signed: true });
            for method in ["wrapping_add", "wrapping_sub"] {
                let marked = format!(
                    "@trust-rustc-total-primitive-method::core::num::<impl i{width}>::{method}"
                );
                assert!(model(&signed, &marked, &args, &Place::local(0)).is_some());
                assert!(
                    model(&func, &marked, &args, &Place::local(0)).is_none(),
                    "signed marker at an unsigned destination"
                );
            }
        }

        assert!(
            model(&func, "attacker::wrapping_add", &args, &Place::local(0)).is_none(),
            "a source-spellable suffix must not receive modular semantics"
        );

        let mut extra_arg = args.clone();
        extra_arg.push(Operand::Copy(Place::local(1)));
        assert!(
            model(&func, marker, &extra_arg, &Place::local(0)).is_none(),
            "the authenticated method has exactly two operands"
        );
        for (has_target, has_atomic, is_foreign, is_unsafe_sig, label) in [
            (false, false, false, false, "missing normal-return target"),
            (true, true, false, false, "atomic metadata"),
            (true, false, true, false, "foreign metadata"),
            (true, false, false, true, "unsafe-signature metadata"),
        ] {
            assert!(
                wrapping_call_assert_model(
                    &func,
                    marker,
                    &args,
                    &Place::local(0),
                    has_target,
                    has_atomic,
                    is_foreign,
                    is_unsafe_sig,
                )
                .is_none(),
                "{label} must not inherit the authenticated modular call model"
            );
        }

        let signed = binary_func(Ty::Int { width: 32, signed: true });
        let signed_args = vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))];
        let signed_marker =
            "@trust-rustc-wrapping-refutation-method::core::num::<impl i32>::wrapping_sub";
        assert!(
            model(&signed, signed_marker, &signed_args, &Place::local(0)).is_some(),
            "the sealed refutation marker retains the prior signed lane"
        );
        let signed_literal_args =
            vec![Operand::Copy(Place::local(1)), Operand::Constant(ConstValue::Int(1))];
        assert!(
            model(&signed, signed_marker, &signed_literal_args, &Place::local(0)).is_some(),
            "a narrow signed literal is checked against the authenticated destination width"
        );
        assert!(
            model(&signed, marker, &signed_args, &Place::local(0)).is_none(),
            "marker carrier and extracted operand/destination types must agree"
        );

        let pointer = binary_func(Ty::PtrSizedInt { signed: false });
        let pointer_args =
            vec![Operand::Copy(Place::local(1)), Operand::Constant(ConstValue::Uint(1, 64))];
        let pointer_marker =
            "@trust-rustc-wrapping-refutation-method::core::num::<impl usize>::wrapping_add";
        assert!(
            model(&pointer, pointer_marker, &pointer_args, &Place::local(0)).is_some(),
            "a pointer-sized literal is checked against its authenticated destination carrier"
        );
        let legacy_pointer = binary_func(Ty::usize());
        let legacy_pointer_args =
            vec![Operand::Copy(Place::local(1)), Operand::Constant(ConstValue::Uint(1, 64))];
        assert!(
            model(&legacy_pointer, pointer_marker, &legacy_pointer_args, &Place::local(0))
                .is_some(),
            "the authenticated pointer marker restores identity lost by legacy verifier extraction"
        );
        assert!(
            model(&pointer, marker, &pointer_args, &Place::local(0)).is_none(),
            "a fixed-width marker must not authorize a faithful pointer-sized destination"
        );

        let fixed_u32 = binary_func(Ty::u32());
        let fixed_u32_args = vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))];
        assert!(
            model(&fixed_u32, pointer_marker, &fixed_u32_args, &Place::local(0)).is_none(),
            "a pointer-sized marker must not authorize an arbitrary fixed-width destination"
        );
    }

    #[test]
    fn wrapping_result_model_requires_a_whole_function_stable_destination() {
        let marker = "@trust-rustc-total-primitive-method::core::num::<impl u64>::wrapping_add";
        let mut func = binary_func(Ty::u64());
        func.body.blocks = vec![
            BasicBlock {
                id: BlockId(0),
                stmts: Vec::new(),
                terminator: Terminator::Call {
                    func: marker.into(),
                    args: vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))],
                    dest: Place::local(0),
                    target: Some(BlockId(1)),
                    span: SourceSpan::default(),
                    atomic: None,
                    is_foreign: false,
                    is_unsafe_sig: false,
                    callee_identity: None,
                    callee_key: crate::sep_engine::tests::fixture_key(&marker.to_string()),
                    unwind: trust_types::UnwindEdge::Continue,
                },
            },
            BasicBlock { id: BlockId(1), stmts: Vec::new(), terminator: Terminator::Return },
        ];
        assert!(
            wrapping_result_local_is_stable(&func, &Place::local(0), 1),
            "an exact single call destination remains modelable even when rustc retains an \
             unreachable unwind annotation"
        );

        func.body.blocks[0].stmts.push(Statement::Assign {
            place: Place::local(0),
            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 64))),
            span: SourceSpan::default(),
        });
        assert!(
            !wrapping_result_local_is_stable(&func, &Place::local(0), 1),
            "a competing statement definition must prevent use-point renaming from assigning \
             the wrapping equation to another reaching value"
        );
    }
}

#[cfg(test)]
mod bidirectional_grounding_tests {
    use trust_types::{
        BasicBlock, LocalDecl, SourceSpan, Ty, UnwindEdge, VerifiableBody, VerifiableFunction,
    };

    use super::*;

    /// A guarded `assert!(value == 10)` where `value` is either a real input or
    /// the result of an unmodeled call. The leading `gate` branch ensures the
    /// panic formula has one grounded and one potentially ungrounded conjunct —
    /// the exact shape on which dropping only the ungrounded conjunct used to
    /// manufacture a satisfiable, guard-only false refutation.
    fn guarded_assert_fixture(value_is_input: bool) -> VerifiableFunction {
        let span = SourceSpan::default();
        VerifiableFunction {
            name: "guarded_opaque_assert".into(),
            def_path: "test::guarded_opaque_assert".into(),
            span: span.clone(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Unit, name: None },
                    LocalDecl { index: 1, ty: Ty::Bool, name: Some("gate".into()) },
                    LocalDecl { index: 2, ty: Ty::u64(), name: Some("value".into()) },
                    LocalDecl { index: 3, ty: Ty::Bool, name: Some("ok".into()) },
                    LocalDecl { index: 4, ty: Ty::Unit, name: None },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: Vec::new(),
                        terminator: Terminator::SwitchInt {
                            discr: Operand::Copy(Place::local(1)),
                            targets: vec![(1, BlockId(1))],
                            otherwise: BlockId(4),
                            exhaustive_enum_unreachable: false,
                            span: span.clone(),
                        },
                    },
                    BasicBlock {
                        id: BlockId(1),
                        stmts: Vec::new(),
                        terminator: if value_is_input {
                            Terminator::Goto(BlockId(2))
                        } else {
                            Terminator::Call {
                                func: "external::opaque_u64".into(),
                                args: Vec::new(),
                                dest: Place::local(2),
                                target: Some(BlockId(2)),
                                span: span.clone(),
                                atomic: None,
                                is_foreign: false,
                                is_unsafe_sig: false,
                                callee_identity: None,
                                callee_key: crate::sep_engine::tests::fixture_key(
                                    "external::opaque_u64",
                                ),
                                unwind: UnwindEdge::Unreachable,
                            }
                        },
                    },
                    BasicBlock {
                        id: BlockId(2),
                        stmts: vec![Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Eq,
                                Operand::Copy(Place::local(2)),
                                Operand::Constant(ConstValue::Uint(10, 64)),
                            ),
                            span: span.clone(),
                        }],
                        terminator: Terminator::SwitchInt {
                            discr: Operand::Copy(Place::local(3)),
                            targets: vec![(0, BlockId(3))],
                            otherwise: BlockId(4),
                            exhaustive_enum_unreachable: false,
                            span: span.clone(),
                        },
                    },
                    BasicBlock {
                        id: BlockId(3),
                        stmts: Vec::new(),
                        terminator: Terminator::Call {
                            func: "core::panicking::assert_failed::<u64, u64>".into(),
                            args: Vec::new(),
                            dest: Place::local(4),
                            target: None,
                            span: span.clone(),
                            atomic: None,
                            is_foreign: false,
                            is_unsafe_sig: false,
                            callee_identity: None,
                            callee_key: crate::sep_engine::tests::fixture_key(
                                "core::panicking::assert_failed::<u64, u64>",
                            ),
                            unwind: UnwindEdge::Unreachable,
                        },
                    },
                    BasicBlock {
                        id: BlockId(4),
                        stmts: Vec::new(),
                        terminator: Terminator::Return,
                    },
                ],
                arg_count: if value_is_input { 2 } else { 1 },
                return_ty: Ty::Unit,
                datatype_defs: Default::default(),
            },
            contracts: Vec::new(),
            preconditions: Vec::new(),
            postconditions: Vec::new(),
            spec: Default::default(),
            tuple_layouts: Default::default(),
        }
    }

    #[test]
    fn unmodeled_call_result_declines_the_entire_bidirectional_candidate() {
        let func = guarded_assert_fixture(false);
        assert!(
            generate_full_assert_refutation_vcs(&func).is_empty(),
            "a grounded reachability guard cannot license a SAT query after the assertion's \
             opaque fail-condition conjunct is removed"
        );
    }

    #[test]
    fn otherwise_identical_input_grounded_assertion_remains_candidate() {
        let func = guarded_assert_fixture(true);
        let vcs = generate_full_assert_refutation_vcs(&func);
        assert!(!vcs.is_empty(), "the all-input dual must remain in the bidirectional lane");
        assert!(vcs.iter().all(|vc| {
            vc.formula
                .free_variables()
                .iter()
                .all(|v| matches!(v.split('#').next(), Some("gate" | "value")))
        }));
    }

    #[test]
    fn opaque_call_reassigned_parameter_is_not_an_input_free_version() {
        let mut func = guarded_assert_fixture(false);
        // `value` is now a formal parameter, but bb1 overwrites it with the
        // opaque call result before the assertion. The entry value therefore
        // cannot license the post-call SSA version as a free input.
        func.body.arg_count = 2;
        assert!(
            !v2_input_free_locals(&func).contains(&2),
            "a call-destination write must revoke parameter input-freedom"
        );
        assert!(
            generate_full_assert_refutation_vcs(&func).is_empty(),
            "the opaque post-call parameter version must decline, not false-refute"
        );
    }

    #[test]
    fn copied_input_alias_is_grounded_before_bidirectional_solver_use() {
        use trust_router::{InProcessAyBackend, VerificationBackend};

        let mut func = guarded_assert_fixture(true);
        func.body.locals.push(LocalDecl {
            index: 5,
            ty: Ty::u64(),
            name: Some("copied_value".into()),
        });
        func.body.blocks[1].stmts.push(Statement::Assign {
            place: Place::local(5),
            rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
            span: SourceSpan::default(),
        });
        let Statement::Assign { rvalue: Rvalue::BinaryOp(BinOp::Eq, lhs, rhs), .. } =
            &mut func.body.blocks[2].stmts[0]
        else {
            unreachable!()
        };
        *lhs = Operand::Copy(Place::local(5));
        *rhs = Operand::Copy(Place::local(2));

        assert!(v2_input_free_locals(&func).contains(&2));
        assert!(
            !v2_input_free_locals(&func).contains(&5),
            "the copy must not become an independent arbitrary input"
        );
        let vcs = generate_full_assert_refutation_vcs(&func);
        assert_eq!(vcs.len(), 1, "the exact alias definition should retain coverage");
        assert!(
            matches!(
                InProcessAyBackend::new().verify(&vcs[0]),
                trust_types::VerificationResult::Proved { .. }
            ),
            "the safe copy-equality violation must be UNSAT after exact grounding"
        );
    }

    #[test]
    fn fixed_width_input_ranges_exclude_impossible_assert_counterexamples() {
        use trust_router::{InProcessAyBackend, VerificationBackend};

        let mut func = guarded_assert_fixture(true);
        func.body.locals[2].ty = Ty::u8();
        func.body.blocks[2].stmts[0] = Statement::Assign {
            place: Place::local(3),
            rvalue: Rvalue::BinaryOp(
                BinOp::Le,
                Operand::Copy(Place::local(2)),
                Operand::Constant(ConstValue::Uint(255, 8)),
            ),
            span: SourceSpan::default(),
        };

        let vcs = generate_full_assert_refutation_vcs(&func);
        assert_eq!(vcs.len(), 1, "the directly input-grounded assertion remains covered");
        assert!(
            matches!(
                InProcessAyBackend::new().verify(&vcs[0]),
                trust_types::VerificationResult::Proved { .. }
            ),
            "a u8 can never witness the panic path `value > 255`; the generated formula must \
             carry its declared 0..=255 range"
        );
    }

    #[test]
    fn char_input_range_excludes_values_above_char_max() {
        use trust_router::{InProcessAyBackend, VerificationBackend};

        let mut func = guarded_assert_fixture(true);
        func.body.locals[2].ty = Ty::Char;
        func.body.blocks[2].stmts[0] = Statement::Assign {
            place: Place::local(3),
            rvalue: Rvalue::BinaryOp(
                BinOp::Le,
                Operand::Copy(Place::local(2)),
                Operand::Constant(ConstValue::Uint(char::MAX as u128, 32)),
            ),
            span: SourceSpan::default(),
        };

        let vcs = generate_full_assert_refutation_vcs(&func);
        assert!(!vcs.is_empty(), "the directly input-grounded char assertion remains covered");
        assert!(
            vcs.iter().all(|vc| matches!(
                InProcessAyBackend::new().verify(vc),
                trust_types::VerificationResult::Proved { .. }
            )),
            "a char can never exceed char::MAX; the generated formula must carry the exact \
             Unicode scalar range"
        );
    }

    #[test]
    fn char_input_range_excludes_surrogate_code_points() {
        use trust_router::{InProcessAyBackend, VerificationBackend};

        // Rust cannot spell a surrogate `char` literal, so exercise the exact
        // mathematical carrier directly. The preceding end-to-end test proves
        // this is the same helper the assertion lane attaches to an input.
        let value = Formula::Var("value".into(), trust_types::Sort::Int);
        let vc = VerificationCondition {
            kind: VcKind::Assertion { message: "surrogate carrier canary".into() },
            function: "char_carrier_canary".into(),
            location: SourceSpan::default(),
            formula: Formula::And(vec![
                crate::range::rust_type_range_constraint(&value, &Ty::Char)
                    .expect("char has an exact scalar carrier"),
                Formula::Eq(Box::new(value), Box::new(Formula::Int(0xD800))),
            ]),
            contract_metadata: None,
            obligation: None,
        };
        assert!(
            matches!(
                InProcessAyBackend::new().verify(&vc),
                trust_types::VerificationResult::Proved { .. }
            ),
            "a char can never equal a surrogate code point; the generated formula must exclude \
             the surrogate interval"
        );
    }

    #[test]
    fn projected_call_destination_excludes_its_whole_base_from_stability() {
        let mut func = guarded_assert_fixture(false);
        let Terminator::Call { dest, .. } = &mut func.body.blocks[1].terminator else {
            unreachable!()
        };
        *dest = Place::field(2, 0);
        assert!(
            call_destination_base_locals(&func).contains(&2),
            "a call write through `dest.0` must destabilize the whole `dest` base"
        );
    }
}

#[cfg(test)]
mod input_free_exactness_tests {
    use trust_types::{BasicBlock, LocalDecl, SourceSpan, Ty, VerifiableBody, VerifiableFunction};

    use super::*;

    fn single_assignment_fixture(destination: usize, rvalue: Rvalue) -> VerifiableFunction {
        VerifiableFunction {
            name: "input_free_exactness".into(),
            def_path: "test::input_free_exactness".into(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Unit, name: None },
                    LocalDecl { index: 1, ty: Ty::u64(), name: Some("input".into()) },
                    LocalDecl { index: 2, ty: Ty::u64(), name: Some("derived".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(destination),
                        rvalue,
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 1,
                return_ty: Ty::Unit,
                datatype_defs: Default::default(),
            },
            contracts: Vec::new(),
            preconditions: Vec::new(),
            postconditions: Vec::new(),
            spec: Default::default(),
            tuple_layouts: Default::default(),
        }
    }

    #[test]
    fn constant_local_requires_its_definition_instead_of_becoming_free() {
        let func =
            single_assignment_fixture(2, Rvalue::Use(Operand::Constant(ConstValue::Uint(10, 64))));
        let safe = v2_input_free_locals(&func);
        assert!(safe.contains(&1), "the unwritten formal remains a free input");
        assert!(
            !safe.contains(&2),
            "a constant is constrained and must be grounded by its equality"
        );
    }

    #[test]
    fn copied_input_requires_its_alias_definition_instead_of_decoupling() {
        let func = single_assignment_fixture(2, Rvalue::Use(Operand::Copy(Place::local(1))));
        let safe = v2_input_free_locals(&func);
        assert!(safe.contains(&1), "the unwritten formal remains a free input");
        assert!(!safe.contains(&2), "a copy cannot vary independently of the source input");
    }

    #[test]
    fn statement_reassigned_parameter_cannot_reenter_as_a_leaf() {
        let func =
            single_assignment_fixture(1, Rvalue::Use(Operand::Constant(ConstValue::Uint(10, 64))));
        assert!(
            !v2_input_free_locals(&func).contains(&1),
            "a body write makes every post-write version distinct from the entry input"
        );
    }

    #[test]
    fn non_assign_value_writes_revoke_static_assignment_authority() {
        for write in [
            Statement::SetDiscriminant { place: Place::local(2), variant_index: 1 },
            Statement::Deinit { place: Place::local(2) },
        ] {
            let mut func = single_assignment_fixture(
                2,
                Rvalue::Use(Operand::Constant(ConstValue::Uint(10, 64))),
            );
            func.body.blocks[0].stmts.push(write);
            assert!(
                !is_single_static_assignment(&func, 2),
                "a modeled non-Assign write must revoke global single-assignment identity"
            );
            assert!(
                crate::guards::value_local_is_unstable(&func, 2),
                "the shared staleness gate must count every modeled value-write channel"
            );
        }
    }
}

#[cfg(test)]
mod unchecked_read_count_tests {
    use trust_types::{
        BasicBlock, LocalDecl, SourceSpan, Ty, UnwindEdge, VerifiableBody, VerifiableFunction,
    };

    use super::*;

    #[test]
    fn unchecked_operands_count_as_reads_for_payload_admission() {
        let func = VerifiableFunction {
            name: "unchecked_read_count".into(),
            def_path: "test::unchecked_read_count".into(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Unit, name: None },
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("input".into()) },
                    LocalDecl { index: 2, ty: Ty::u32(), name: Some("rhs".into()) },
                    LocalDecl { index: 3, ty: Ty::u32(), name: Some("sum".into()) },
                    LocalDecl { index: 4, ty: Ty::u32(), name: Some("payload".into()) },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::UncheckedBinaryOp(
                                BinOp::Add,
                                Operand::Copy(Place::local(1)),
                                Operand::Copy(Place::local(2)),
                            ),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Call {
                            func: "<u32 as Try>::branch".into(),
                            args: vec![Operand::Copy(Place::local(1))],
                            dest: Place::local(4),
                            target: Some(BlockId(1)),
                            span: SourceSpan::default(),
                            atomic: None,
                            is_foreign: false,
                            is_unsafe_sig: false,
                            callee_identity: None,
                            callee_key: crate::sep_engine::tests::fixture_key(
                                "<u32 as Try>::branch",
                            ),
                            unwind: UnwindEdge::Unreachable,
                        },
                    },
                    BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
                ],
                arg_count: 2,
                return_ty: Ty::Unit,
                datatype_defs: Default::default(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
            tuple_layouts: Default::default(),
        };

        let mut control = func.clone();
        control.body.blocks[0].stmts.clear();
        assert!(
            v2_input_free_locals(&control).contains(&4),
            "the allowlisted single-use payload control must exercise admission"
        );
        assert!(
            !v2_input_free_locals(&func).contains(&4),
            "the extra unchecked read must prevent decoupling the payload from a reused input"
        );

        let mut constrained = control.clone();
        constrained.preconditions.push(Formula::Le(
            Box::new(Formula::Int(0)),
            Box::new(Formula::Var("input".into(), Sort::Int)),
        ));
        assert!(
            !v2_input_free_locals(&constrained).contains(&4),
            "a gated precondition can constrain the extractor input without a body read, so the \
             result may not be admitted as an independent free value"
        );

        let mut rewritten = control.clone();
        rewritten.body.blocks[1].stmts.push(Statement::Assign {
            place: Place::local(4),
            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 32))),
            span: SourceSpan::default(),
        });
        assert!(
            !v2_input_free_locals(&rewritten).contains(&4),
            "a later destination rewrite must revoke payload-result input-freedom"
        );
    }
}
