// trust-mir-extract/cell_threading.rs: TEST-ONLY feasibility transform for an
// interior-mutable, fuel-shaped CELL COUNTER. This is not the production
// clean-kernel heartbeat lowering: production still needs authenticated
// cluster/reference discovery and a u32-to-inductive-fuel refinement witness.
//
// THE GAP THIS MODELS IN A SYNTHETIC PROTOTYPE: the real kernel cluster
// (`infer_type <-> whnf <-> is_def_eq`) mediates its budget through a
// `Cell<u32>` field reached from `&self` — the counter is READ at entry
// (exhaustion check), WRITTEN back decremented, and silently carried through
// every sibling call; it never appears in any signature. The fuel lanes model
// that discipline as an EXPLICIT threaded parameter (fuel in, remainder out).
// This test module explores the candidate bridge: a state-passing transform (the standard
// state-monad-ification of `Cell` reads/writes) over the EXTRACTED
// `VerifiableFunction`s, so the lane input is derived from the literal MIR
// instead of being hand-modeled.
//
// INPUT SHAPE (fail-closed outside it): a cluster of extracted functions
//
//   fn m(holder: &H, e: &E) -> E          // H carries the cell field
//       (cell reads/writes ONLY through the recognized accessor calls
//        `get(&(*_1).<cell_field>)` / `set(&(*_1).<cell_field>, v)`;
//        `_1` otherwise appears ONLY as arg 0 of calls to cluster members)
//
// OUTPUT SHAPE (the threaded lane's grammar):
//
//   fn m(fuel: &Fuel, e: &E) -> Res       // Res = Mk(Fuel, E)
//
// with the cell state reconstructed by a forward symbolic pass:
//
//   * the ENTRY `get` result is substituted by the fuel parameter (sound
//     because no `set` precedes it — enforced by the pass ordering);
//   * `set(v)` advances the tracked cell state to `v`;
//   * a cluster call is rewritten to the threaded callee: its fuel argument
//     is a reborrow of the CURRENT cell state, its result becomes the
//     (remainder, payload) pair, the payload flows into the original
//     destination, and the tracked state advances to the returned REMAINDER
//     (`.0` of the pair) — the remainder-threading discipline;
//   * every `_0 = <payload>` return site is wrapped into
//     `_0 = Mk(<current cell state>, <payload>)`.
//
// The transform does NO branch classification: under the lane's own symbolic
// walk the fuel parameter resolves to `Z` in the exhaustion arm and to
// `S(k)` in the step arm, so emitting `copy (*fuel)` as the remainder of a
// pre-`set` return site is exactly the pinned exhaustion shape when (and only
// when) the arm really is the `Z` arm — a wrong shape is REJECTED downstream
// by the lane / kernel, never silently accepted.
//
// TYPE NORMALIZATION: the fixture datatypes lower as `Ty::Adt` enums (the
// native `Ty::Datatype` modeling in ty_convert is def-path-gated to the real
// kernel types). `adt_enum_to_datatype` converts them mechanically —
// variants in declaration order, positional discriminants required — which is
// derived entirely from the extracted type, never hand-declared.
//
// SOUNDNESS OF THE FIXTURE EXPERIMENT: this is not production pipeline
// plumbing or a compiler trust boundary. Its output is (a)
// drift-gated as a committed artifact (regenerated, never hand-edited), and
// (b) consumed by the threaded-budget lane whose bundle is discharged through
// the Clean kernel — a wrong transform yields fail-closed emission or kernel
// rejection, not a false certificate. It is compiled only under `cfg(test)`;
// no compiler verdict consumes it. Missing requirements for a literal
// kernel-scale application:
//   * accessor recognition is by callee name suffix — the real
//     `core::cell::Cell::<u32>::get/set` def-paths slot into the same
//     recognition point;
//   * the cell-state tracking is per-block straight-line (each CFG block is
//     reached with ONE consistent state; a join of distinct states fails
//     closed) — real kernel bodies with state-carrying joins would need the
//     dedicated current-fuel local generalization;
//   * the counter is fuel-shaped (`Z | S`) where the real heartbeat is `u32`
//     — the standing u32-as-nat modeling step of the fuel lanes.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use std::collections::BTreeMap;

use trust_types::{
    AggregateKind, BasicBlock, BlockId, LocalDecl, Operand, Place, Projection, Rvalue, SourceSpan,
    Statement, Terminator, Ty, VerifiableFunction,
};

/// Which functions the transform touches and how accessors are recognized.
pub struct CellThreadingSpec {
    /// Cluster member names (the cell-mediated model functions), keyed as in
    /// the extracted map; also the callee names their calls carry.
    pub members: Vec<String>,
    /// Hand-threaded reference functions (already in the lane shape); passed
    /// through with type normalization only. The result-pair datatype is
    /// derived from their return type.
    pub references: Vec<String>,
    /// The cell-read accessor callee name (e.g. `cell_get`; at kernel scale a
    /// def-path like `core::cell::Cell::<u32>::get`).
    pub get_fn: String,
    /// The cell-write accessor callee name.
    pub set_fn: String,
}

/// The symbolic cell state carried by the forward pass.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum CellState {
    /// The cell still holds the (entry) fuel parameter value.
    Entry,
    /// The cell holds the pointee of local `p` (`p: *const Fuel`, the written
    /// decrement).
    Ptr(usize),
    /// The cell holds the remainder returned by the cluster call whose pair
    /// landed in local `p` (`p: Res`; the remainder is field 0).
    Rem(usize),
}

/// Root place of the CURRENT cell value under `state` (the place whose value
/// IS the fuel currently in the cell).
fn state_value_place(state: CellState) -> Place {
    match state {
        CellState::Entry => Place { local: 1, projections: vec![Projection::Deref] },
        CellState::Ptr(p) => Place { local: p, projections: vec![Projection::Deref] },
        CellState::Rem(p) => Place { local: p, projections: vec![Projection::Field(0)] },
    }
}

/// Convert an extracted `Ty::Adt` ENUM into the native recursive
/// `Ty::Datatype` form the induction lanes consume. Fail-closed `None` unless
/// every variant's discriminant equals its declaration position (the
/// `SwitchInt` tags the lanes read are positional). Structs (no variants) and
/// non-ADTs are returned unchanged, recursing through `Ref`/`RawPtr`.
#[must_use]
pub fn normalize_ty(ty: &Ty) -> Option<Ty> {
    Some(match ty {
        Ty::Adt { name, variants, .. } if !variants.is_empty() => {
            let mut vs: Vec<(String, Vec<(String, Ty)>)> = Vec::with_capacity(variants.len());
            for (pos, v) in variants.iter().enumerate() {
                if v.discriminant != pos as i128 {
                    return None;
                }
                let mut fields = Vec::with_capacity(v.fields.len());
                for (fname, fty) in &v.fields {
                    fields.push((fname.clone(), normalize_ty(fty)?));
                }
                vs.push((v.name.clone(), fields));
            }
            Ty::Datatype { name: name.clone(), variants: vs }
        }
        Ty::Ref { mutable, inner } => {
            Ty::Ref { mutable: *mutable, inner: Box::new(normalize_ty(inner)?) }
        }
        Ty::RawPtr { mutable, pointee } => {
            Ty::RawPtr { mutable: *mutable, pointee: Box::new(normalize_ty(pointee)?) }
        }
        other => other.clone(),
    })
}

/// The defining occurrence of every datatype the cluster's signatures mention,
/// keyed by sort name.
type DatatypeDefs = BTreeMap<String, Vec<(String, Vec<(String, Ty)>)>>;

/// RC-1 (canonical recursive-type lowering): a recursive type that is a canonical
/// CUT POINT is emitted as a by-name `Ty::Datatype { variants: [] }` at every
/// occurrence except the one where it is the root of its own lowering walk. So
/// `Res = Mk(Fuel, E)` now carries by-name `Fuel`/`E` rather than a one-level
/// unrolling of each, and this transform — which reads the fuel's nat shape out
/// of that nested position — has to resolve the reference.
///
/// That is exactly the contract `Ty::Datatype` documents: "an empty `variants`
/// vector means a back-reference to the datatype named `name`, whose full
/// definition appears at its defining occurrence". The definitions are collected
/// from the cluster's own extracted signatures — a local declared `*const Fuel`
/// lowers `Fuel` at the root of its walk and therefore still carries the full
/// variant list — so nothing is invented here.
///
/// FAIL-CLOSED: if one sort name carries two DIFFERENT definitions, this returns
/// `None` rather than picking one. Two definitions under one name is the
/// generics-erased-name collision (`Foo<u8>` and `Foo<i32>` both printing
/// `Foo`); resolving it by guessing would merge two genuinely different types,
/// which is worse than declining.
fn cluster_datatype_definitions(functions: &BTreeMap<String, VerifiableFunction>) -> Option<DatatypeDefs> {
    let mut defs = DatatypeDefs::new();
    let mut conflict = false;
    for f in functions.values() {
        let tys = f.body.locals.iter().map(|l| &l.ty).chain(std::iter::once(&f.body.return_ty));
        for ty in tys {
            let Some(normalized) = normalize_ty(ty) else {
                continue;
            };
            collect_datatype_definitions(&normalized, &mut defs, &mut conflict);
        }
    }
    if conflict {
        return None;
    }
    Some(defs)
}

/// Record every DEFINING datatype occurrence (non-empty variant list) in `ty`.
/// Coverage mirrors `normalize_ty` exactly — the positions this transform reads.
fn collect_datatype_definitions(ty: &Ty, defs: &mut DatatypeDefs, conflict: &mut bool) {
    match ty {
        Ty::Datatype { name, variants } => {
            if !variants.is_empty() {
                match defs.get(name) {
                    Some(existing) if existing != variants => *conflict = true,
                    Some(_) => {}
                    None => {
                        defs.insert(name.clone(), variants.clone());
                    }
                }
            }
            for (_, fields) in variants {
                for (_, fty) in fields {
                    collect_datatype_definitions(fty, defs, conflict);
                }
            }
        }
        Ty::Ref { inner, .. } => collect_datatype_definitions(inner, defs, conflict),
        Ty::RawPtr { pointee, .. } => collect_datatype_definitions(pointee, defs, conflict),
        _ => {}
    }
}

/// Replace a by-name `Ty::Datatype` reference with its defining occurrence.
///
/// A name is bound AT MOST ONCE on any path (`expanding`): a recursive
/// datatype's own back-edge has to stay a by-name reference or the tree is not
/// finite. An unknown name is left exactly as it is — never invented.
///
/// IDEMPOTENT, which matters because the threading transform installs an
/// already-resolved type and then normalizes the whole body again: a datatype
/// occurrence that ALREADY carries its variant list binds the name for its own
/// subtree, so the back-edges inside it are left alone instead of being expanded
/// one level deeper on every pass.
fn resolve_datatype_refs(ty: &Ty, defs: &DatatypeDefs, expanding: &mut Vec<String>) -> Ty {
    match ty {
        Ty::Datatype { name, variants } => {
            let already_binding = expanding.iter().any(|n| n == name);
            let source = match defs.get(name) {
                Some(definition) if variants.is_empty() && !already_binding => definition,
                _ => variants,
            };
            let pushed = !source.is_empty() && !already_binding;
            if pushed {
                expanding.push(name.clone());
            }
            let resolved = source
                .iter()
                .map(|(ctor, fields)| {
                    let fields = fields
                        .iter()
                        .map(|(fname, fty)| {
                            (fname.clone(), resolve_datatype_refs(fty, defs, expanding))
                        })
                        .collect();
                    (ctor.clone(), fields)
                })
                .collect();
            if pushed {
                expanding.pop();
            }
            Ty::Datatype { name: name.clone(), variants: resolved }
        }
        Ty::Ref { mutable, inner } => Ty::Ref {
            mutable: *mutable,
            inner: Box::new(resolve_datatype_refs(inner, defs, expanding)),
        },
        Ty::RawPtr { mutable, pointee } => Ty::RawPtr {
            mutable: *mutable,
            pointee: Box::new(resolve_datatype_refs(pointee, defs, expanding)),
        },
        other => other.clone(),
    }
}

/// Normalize every local type and the return type of `f` in place, resolving the
/// RC-1 by-name datatype references against `defs` (see
/// `cluster_datatype_definitions`).
fn normalize_function_tys(f: &mut VerifiableFunction, defs: &DatatypeDefs) -> Option<()> {
    for l in &mut f.body.locals {
        l.ty = resolve_datatype_refs(&normalize_ty(&l.ty)?, defs, &mut Vec::new());
    }
    f.body.return_ty = resolve_datatype_refs(&normalize_ty(&f.body.return_ty)?, defs, &mut Vec::new());
    Some(())
}

/// Does `place` mention `local` anywhere (as root)?
fn place_uses_local(place: &Place, local: usize) -> bool {
    place.local == local
}

/// Does `place` BARE-use `local` — root it WITHOUT a leading `Deref`? After
/// get-read substitution the fuel parameter (`_1`) legitimately appears in
/// `(*_1)...` reads; a BARE `_1` (empty projections, or a non-`Deref` first
/// projection like a struct-field access) is instead the holder ESCAPING the
/// grammar and must fail closed.
fn place_bare_uses_local(place: &Place, local: usize) -> bool {
    place.local == local && place.projections.first() != Some(&Projection::Deref)
}

fn operand_place(op: &Operand) -> Option<&Place> {
    match op {
        Operand::Copy(p) | Operand::Move(p) => Some(p),
        _ => None,
    }
}

fn operand_uses_local(op: &Operand, local: usize) -> bool {
    operand_place(op).is_some_and(|p| place_uses_local(p, local))
}

fn operand_bare_uses_local(op: &Operand, local: usize) -> bool {
    operand_place(op).is_some_and(|p| place_bare_uses_local(p, local))
}

/// True iff `rv` BARE-uses `local` (see [`place_bare_uses_local`]). Unknown
/// rvalue forms fail closed (treated as a bare use).
fn rvalue_bare_uses_local(rv: &Rvalue, local: usize) -> bool {
    match rv {
        Rvalue::Use(op) | Rvalue::UnaryOp(_, op) | Rvalue::Repeat(op, _) => {
            operand_bare_uses_local(op, local)
        }
        Rvalue::BinaryOp(_, a, b) | Rvalue::CheckedBinaryOp(_, a, b) => {
            operand_bare_uses_local(a, local) || operand_bare_uses_local(b, local)
        }
        Rvalue::Ref { place, .. }
        | Rvalue::AddressOf(_, place)
        | Rvalue::Discriminant(place)
        | Rvalue::Len(place)
        | Rvalue::CopyForDeref(place) => place_bare_uses_local(place, local),
        Rvalue::Cast(op, _) => operand_bare_uses_local(op, local),
        Rvalue::Aggregate(_, ops) => ops.iter().any(|o| operand_bare_uses_local(o, local)),
        Rvalue::Unsupported { operands, .. } => {
            operands.iter().any(|o| operand_bare_uses_local(o, local))
        }
        _ => true, // unknown rvalue form: fail closed
    }
}

/// The cell-accessor argument idiom: `_a = &((*_1).<field>)`. Returns the
/// field index.
fn cell_ref_assign(stmt: &Statement) -> Option<(usize, usize)> {
    let Statement::Assign { place, rvalue, .. } = stmt else {
        return None;
    };
    if !place.projections.is_empty() {
        return None;
    }
    let Rvalue::Ref { mutable: false, place: src } = rvalue else {
        return None;
    };
    if src.local != 1 {
        return None;
    }
    let [Projection::Deref, Projection::Field(fidx)] = src.projections.as_slice() else {
        return None;
    };
    Some((place.local, *fidx))
}

/// Substitute get-result reads: a place `{d, [Deref, rest..]}` whose root `d`
/// is a get destination becomes the recorded cell-value place with `rest`
/// appended.
fn subst_get_reads(place: &mut Place, get_roots: &BTreeMap<usize, Place>) -> Option<()> {
    if let Some(root) = get_roots.get(&place.local) {
        let Some(Projection::Deref) = place.projections.first() else {
            // A get result used other than through a deref (e.g. stored or
            // compared as a raw address) is outside the grammar.
            return None;
        };
        let mut projections = root.projections.clone();
        projections.extend(place.projections[1..].iter().cloned());
        *place = Place { local: root.local, projections };
    }
    Some(())
}

fn subst_get_reads_operand(op: &mut Operand, get_roots: &BTreeMap<usize, Place>) -> Option<()> {
    match op {
        Operand::Copy(p) | Operand::Move(p) => subst_get_reads(p, get_roots),
        _ => Some(()),
    }
}

fn subst_get_reads_rvalue(rv: &mut Rvalue, get_roots: &BTreeMap<usize, Place>) -> Option<()> {
    match rv {
        Rvalue::Use(op) | Rvalue::UnaryOp(_, op) | Rvalue::Cast(op, _) | Rvalue::Repeat(op, _) => {
            subst_get_reads_operand(op, get_roots)
        }
        Rvalue::BinaryOp(_, a, b) | Rvalue::CheckedBinaryOp(_, a, b) => {
            subst_get_reads_operand(a, get_roots)?;
            subst_get_reads_operand(b, get_roots)
        }
        Rvalue::Ref { place, .. }
        | Rvalue::AddressOf(_, place)
        | Rvalue::Discriminant(place)
        | Rvalue::Len(place)
        | Rvalue::CopyForDeref(place) => subst_get_reads(place, get_roots),
        Rvalue::Aggregate(_, ops) => {
            for op in ops {
                subst_get_reads_operand(op, get_roots)?;
            }
            Some(())
        }
        Rvalue::Unsupported { operands, .. } => {
            for op in operands {
                subst_get_reads_operand(op, get_roots)?;
            }
            Some(())
        }
        _ => None,
    }
}

/// Per-function transform context.
struct Fx {
    blocks: Vec<BasicBlock>,
    locals: Vec<LocalDecl>,
    /// get-destination local -> the cell-value place captured at get time.
    get_roots: BTreeMap<usize, Place>,
    fuel_dt: Ty,
    payload_dt: Ty,
    res_dt: Ty,
    res_name: String,
}

impl Fx {
    fn fresh_local(&mut self, ty: Ty, name: &str) -> usize {
        let index = self.locals.len();
        self.locals.push(LocalDecl { index, ty, name: Some(name.to_string()) });
        index
    }

    fn fresh_block_id(&self) -> BlockId {
        BlockId(self.blocks.iter().map(|b| b.id.0).max().unwrap_or(0) + 1)
    }
}

fn assign(place: Place, rvalue: Rvalue) -> Statement {
    Statement::Assign { place, rvalue, span: SourceSpan::default() }
}

/// Match an extracted canonical callee (`crate_name::module::item`) against a
/// configured fixture name. Fully qualified configured names match exactly;
/// an unqualified fixture name may match only a complete final path segment.
fn callee_matches_configured(callee: &str, configured: &str) -> bool {
    callee == configured
        || (!configured.contains("::")
            && callee.strip_suffix(configured).is_some_and(|prefix| prefix.ends_with("::")))
}

/// Return the unique configured member named by `callee`. Ambiguous suffixes
/// fail closed even though the synthetic fixtures currently use unique leaf
/// names.
fn configured_member_for_callee<'a>(callee: &str, configured: &'a [String]) -> Option<&'a str> {
    let mut matches =
        configured.iter().filter(|candidate| callee_matches_configured(callee, candidate));
    let matched = matches.next()?;
    matches.next().is_none().then_some(matched.as_str())
}

/// Is `block`'s rewrite state-DEPENDENT? True iff it wraps a return
/// (`_0 = ..`) or its terminator is a cell accessor / cluster call — the only
/// operations whose lowering reads the tracked cell state. State-insensitive
/// blocks (a bare `Return`/`Unreachable` join, a pure `SwitchInt`) may be
/// reached by distinct states without ambiguity.
fn block_is_state_sensitive(block: &BasicBlock, spec: &CellThreadingSpec) -> bool {
    let writes_result = block.stmts.iter().any(|s| {
        matches!(s, Statement::Assign { place, .. }
            if place.local == 0 && place.projections.is_empty())
    });
    let call_sensitive = matches!(&block.terminator,
        Terminator::Call { func, .. }
            if callee_matches_configured(func, &spec.get_fn)
                || callee_matches_configured(func, &spec.set_fn)
                || configured_member_for_callee(func, &spec.members).is_some());
    writes_result || call_sensitive
}

/// Transform ONE cell-mediated member into the threaded shape. Fail-closed
/// `None` on anything outside the recognized grammar.
#[allow(clippy::too_many_lines)]
fn transform_member(
    func: &VerifiableFunction,
    spec: &CellThreadingSpec,
    fuel_dt: &Ty,
    payload_dt: &Ty,
    res_dt: &Ty,
    defs: &DatatypeDefs,
) -> Option<VerifiableFunction> {
    let mut f = func.clone();
    if f.body.arg_count != 2 {
        return None;
    }
    let Ty::Datatype { name: res_name, .. } = res_dt else {
        return None;
    };
    if !matches!(payload_dt, Ty::Datatype { .. }) {
        return None;
    }

    let mut fx = Fx {
        blocks: f.body.blocks.clone(),
        locals: f.body.locals.clone(),
        get_roots: BTreeMap::new(),
        fuel_dt: fuel_dt.clone(),
        payload_dt: payload_dt.clone(),
        res_dt: res_dt.clone(),
        res_name: res_name.clone(),
    };

    // The designated cell field: every accessor call argument must agree.
    let mut cell_field: Option<usize> = None;

    // Forward pass: worklist of (block, state). `states` doubles as the
    // processed-set (first-arrival state wins). A block reached again with a
    // DIFFERENT state fails closed ONLY if it is STATE-SENSITIVE (contains a
    // return-wrap `_0 = ..`, or a get/set/cluster-call terminator); the
    // state-insensitive join blocks (the shared `Return`, the exhaustive
    // switch's `Unreachable` otherwise) are reached by distinct states in a
    // well-formed cluster and their rewrite does not depend on the state.
    let mut states: BTreeMap<usize, CellState> = BTreeMap::new();
    let mut worklist: Vec<(BlockId, CellState)> = vec![(BlockId(0), CellState::Entry)];

    while let Some((bid, state_in)) = worklist.pop() {
        let bpos = fx.blocks.iter().position(|b| b.id == bid)?;
        if let Some(prev) = states.get(&bid.0) {
            if *prev != state_in && block_is_state_sensitive(&fx.blocks[bpos], spec) {
                return None;
            }
            continue;
        }
        states.insert(bid.0, state_in);
        let mut cur = state_in;
        let mut new_stmts: Vec<Statement> = Vec::new();
        // The accessor-argument temp defined in this block (if any), consumed
        // by this block's own accessor-call terminator.
        let mut pending_cell_ref: Option<(usize, usize)> = None;

        let stmts = fx.blocks[bpos].stmts.clone();
        for mut stmt in stmts {
            if let Some((tmp, fidx)) = cell_ref_assign(&stmt) {
                // `_a = &((*_1).<cell>)` — must feed THIS block's accessor
                // call terminator; recorded and dropped.
                if pending_cell_ref.is_some() {
                    return None;
                }
                if let Some(cf) = cell_field {
                    if cf != fidx {
                        return None;
                    }
                } else {
                    cell_field = Some(fidx);
                }
                pending_cell_ref = Some((tmp, fidx));
                continue;
            }
            // Substitute get-result reads through the captured cell-value
            // places, then audit: NO other statement may mention `_1`.
            match &mut stmt {
                Statement::Assign { place, rvalue, .. } => {
                    subst_get_reads(place, &fx.get_roots)?;
                    subst_get_reads_rvalue(rvalue, &fx.get_roots)?;
                    // A write INTO `_1`, or any BARE `_1` use (holder escape),
                    // fails closed; `(*_1)...` fuel reads are allowed.
                    if place_uses_local(place, 1) || rvalue_bare_uses_local(rvalue, 1) {
                        return None;
                    }
                    // Return-site wrap: `_0 = <payload rvalue>` becomes
                    // `_0 = Mk(<current cell value>, <payload>)`.
                    if place.local == 0 && place.projections.is_empty() {
                        let re = fx.fresh_local(fx.payload_dt.clone(), "__thread_payload");
                        let rz = fx.fresh_local(fx.fuel_dt.clone(), "__thread_rem");
                        new_stmts.push(assign(Place::local(re), rvalue.clone()));
                        new_stmts.push(assign(
                            Place::local(rz),
                            Rvalue::Use(Operand::Copy(state_value_place(cur))),
                        ));
                        new_stmts.push(assign(
                            Place::local(0),
                            Rvalue::Aggregate(
                                AggregateKind::Adt {
                                    name: fx.res_name.clone(),
                                    variant: 0,
                                    active_field: None,
                                    args: None,
                                },
                                vec![
                                    Operand::Move(Place::local(rz)),
                                    Operand::Move(Place::local(re)),
                                ],
                            ),
                        ));
                        continue;
                    }
                }
                Statement::StorageLive(_)
                | Statement::StorageDead(_)
                | Statement::Nop
                | Statement::Coverage
                | Statement::ConstEvalCounter => {}
                _ => return None,
            }
            new_stmts.push(stmt);
        }

        let mut terminator = fx.blocks[bpos].terminator.clone();
        match &mut terminator {
            Terminator::Call { func: callee, args, dest, target, .. } => {
                let target = (*target)?;
                if callee_matches_configured(callee, &spec.get_fn) {
                    // `d = get(&cell)` — record d's cell-value root, drop the
                    // call.
                    let [arg] = args.as_slice() else {
                        return None;
                    };
                    let (tmp, _) = pending_cell_ref.take()?;
                    if operand_place(arg).is_none_or(|p| p.local != tmp) {
                        return None;
                    }
                    if !dest.projections.is_empty() {
                        return None;
                    }
                    fx.get_roots.insert(dest.local, state_value_place(cur));
                    fx.blocks[bpos].stmts = new_stmts;
                    fx.blocks[bpos].terminator = Terminator::Goto(target);
                    worklist.push((target, cur));
                    continue;
                }
                if callee_matches_configured(callee, &spec.set_fn) {
                    // `set(&cell, v)` — advance the state to v, drop the call.
                    let [arg0, arg1] = args.as_slice() else {
                        return None;
                    };
                    let (tmp, _) = pending_cell_ref.take()?;
                    if operand_place(arg0).is_none_or(|p| p.local != tmp) {
                        return None;
                    }
                    let vplace = operand_place(arg1)?;
                    if !vplace.projections.is_empty() {
                        return None;
                    }
                    // The written local must be assigned exactly once in the
                    // whole body (its value is re-read later at threading
                    // sites).
                    let vassigns = fx
                        .blocks
                        .iter()
                        .flat_map(|b| &b.stmts)
                        .filter(|s| {
                            matches!(s, Statement::Assign { place, .. }
                            if place.local == vplace.local && place.projections.is_empty())
                        })
                        .count();
                    if vassigns != 1 {
                        return None;
                    }
                    cur = CellState::Ptr(vplace.local);
                    fx.blocks[bpos].stmts = new_stmts;
                    fx.blocks[bpos].terminator = Terminator::Goto(target);
                    worklist.push((target, cur));
                    continue;
                }
                if let Some(configured_callee) =
                    configured_member_for_callee(callee, &spec.members).map(str::to_owned)
                {
                    // Cluster call: thread the current cell state through.
                    if pending_cell_ref.is_some() {
                        return None;
                    }
                    let [arg0, arg1] = args.as_slice() else {
                        return None;
                    };
                    // Arg 0 must be the bare holder (`_1`).
                    if operand_place(arg0).is_none_or(|p| p.local != 1 || !p.projections.is_empty())
                    {
                        return None;
                    }
                    if operand_uses_local(arg1, 1) || !dest.projections.is_empty() {
                        return None;
                    }
                    let fa = fx.fresh_local(
                        Ty::Ref { mutable: false, inner: Box::new(fx.fuel_dt.clone()) },
                        "__thread_fuel_arg",
                    );
                    match cur {
                        CellState::Entry | CellState::Ptr(_) => {
                            new_stmts.push(assign(
                                Place::local(fa),
                                Rvalue::Ref { mutable: false, place: state_value_place(cur) },
                            ));
                        }
                        CellState::Rem(rp) => {
                            // Read the remainder by value, then borrow it —
                            // the pair-field place is not a stable referent.
                            let rl = fx.fresh_local(fx.fuel_dt.clone(), "__thread_rem_val");
                            new_stmts.push(assign(
                                Place::local(rl),
                                Rvalue::Use(Operand::Copy(Place {
                                    local: rp,
                                    projections: vec![Projection::Field(0)],
                                })),
                            ));
                            new_stmts.push(assign(
                                Place::local(fa),
                                Rvalue::Ref { mutable: false, place: Place::local(rl) },
                            ));
                        }
                    }
                    let rp = fx.fresh_local(fx.res_dt.clone(), "__thread_pair");
                    // Continuation block: unpack the payload into the original
                    // destination, then resume.
                    let nb = fx.fresh_block_id();
                    let orig_dest = dest.clone();
                    fx.blocks.push(BasicBlock {
                        id: nb,
                        stmts: vec![assign(
                            orig_dest,
                            Rvalue::Use(Operand::Copy(Place {
                                local: rp,
                                projections: vec![Projection::Field(1)],
                            })),
                        )],
                        terminator: Terminator::Goto(target),
                    });
                    let next_state = CellState::Rem(rp);
                    // Rewrite the call in place.
                    let Terminator::Call { func, args, dest, target: tgt, .. } =
                        &mut fx.blocks[bpos].terminator
                    else {
                        return None;
                    };
                    // Keep calls aligned with the configured map keys. The
                    // input may carry a crate-qualified canonical def path,
                    // while this synthetic lane intentionally keys its SCC by
                    // the concise fixture member names.
                    *func = configured_callee;
                    args[0] = Operand::Move(Place::local(fa));
                    args[1] = arg1.clone();
                    *dest = Place::local(rp);
                    *tgt = Some(nb);
                    fx.blocks[bpos].stmts = new_stmts;
                    // Seed the continuation's state (it is fully built inline)
                    // so nothing reprocesses it, then resume at the real target.
                    states.insert(nb.0, next_state);
                    worklist.push((target, next_state));
                    continue;
                }
                // Any other callee: `_1` (and the cell) has escaped the
                // grammar — fail closed.
                return None;
            }
            Terminator::SwitchInt { discr, targets, otherwise, .. } => {
                if pending_cell_ref.is_some() {
                    return None;
                }
                subst_get_reads_operand(discr, &fx.get_roots)?;
                if operand_uses_local(discr, 1)
                    && operand_place(discr)
                        .is_some_and(|p| p.projections.first() != Some(&Projection::Deref))
                {
                    return None;
                }
                for (_, t) in targets.iter() {
                    worklist.push((*t, cur));
                }
                worklist.push((*otherwise, cur));
            }
            Terminator::Goto(t) => {
                if pending_cell_ref.is_some() {
                    return None;
                }
                worklist.push((*t, cur));
            }
            Terminator::Return | Terminator::Unreachable => {
                if pending_cell_ref.is_some() {
                    return None;
                }
            }
            _ => return None,
        }
        fx.blocks[bpos].stmts = new_stmts;
        fx.blocks[bpos].terminator = terminator;
    }

    // The cluster must actually touch the cell (a cell-free "member" is not
    // this shape).
    cell_field?;

    // Re-signature: `_1` becomes the fuel parameter, `_0` the result pair.
    fx.locals.get_mut(1)?.ty = Ty::Ref { mutable: false, inner: Box::new(fx.fuel_dt.clone()) };
    fx.locals.get_mut(1)?.name = Some("fuel".to_string());
    fx.locals.first_mut()?.ty = fx.res_dt.clone();
    f.body.return_ty = fx.res_dt.clone();
    f.body.blocks = fx.blocks;
    f.body.locals = fx.locals;
    normalize_function_tys(&mut f, defs)?;

    // Final audit: `_1` may remain only as a Deref-rooted READ (the fuel
    // parameter) — never an assignment destination.
    for b in &f.body.blocks {
        for s in &b.stmts {
            if let Statement::Assign { place, .. } = s {
                if place.local == 1 {
                    return None;
                }
            }
        }
    }
    Some(f)
}

/// Lower a cell-mediated cluster into the threaded lane shape.
///
/// Returns the transformed members plus the type-normalized references, or
/// fail-closed `None` if any member falls outside the recognized grammar.
#[must_use]
pub fn thread_cell_state(
    functions: &BTreeMap<String, VerifiableFunction>,
    spec: &CellThreadingSpec,
) -> Option<BTreeMap<String, VerifiableFunction>> {
    // Derive the canonical datatypes from the FIRST reference's signature —
    // extraction-derived, never hand-declared. RC-1: the nested `Fuel`/`E` inside
    // the result pair now arrive as by-name references, so resolve them against
    // their defining occurrences elsewhere in the same cluster before reading
    // their variant shape (see `cluster_datatype_definitions`).
    let defs = cluster_datatype_definitions(functions)?;
    let first_ref = functions.get(spec.references.first()?)?;
    let res_dt =
        resolve_datatype_refs(&normalize_ty(&first_ref.body.return_ty)?, &defs, &mut Vec::new());
    let Ty::Datatype { variants, .. } = &res_dt else {
        return None;
    };
    let [(_, pair_fields)] = variants.as_slice() else {
        return None;
    };
    let [(_, fuel_dt), (_, payload_dt)] = pair_fields.as_slice() else {
        return None;
    };
    let (fuel_dt, payload_dt) = (fuel_dt.clone(), payload_dt.clone());

    let mut out = BTreeMap::new();
    for name in &spec.members {
        let f = functions.get(name)?;
        out.insert(name.clone(), transform_member(f, spec, &fuel_dt, &payload_dt, &res_dt, &defs)?);
    }
    for name in &spec.references {
        let mut f = functions.get(name)?.clone();
        if f.body.arg_count != 2 {
            return None;
        }
        normalize_function_tys(&mut f, &defs)?;
        out.insert(name.clone(), f);
    }
    Some(out)
}
