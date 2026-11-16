// trust-vcgen/src/generate/range_bound_use.rs: a slice range-index bound named by its
// SSA VERSION at the statement that reads it INTO THE RANGE.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0
//
// Trust: 2026-10-02 (class 10, false refutation) — THE GAP THIS CLOSES.
//
// `iterator_yield::resolve_range_bound_formula` answers a GLOBAL question: a formula
// that names the bound's value at EVERY program point, because its other callers
// inline the answer into facts keyed on other names (a range payload's `i < end`).
// Since round A5 it therefore refuses any bound whose root local has a second write:
// the bare name is no longer a name of one value. The slice range-index lane
// (`panic_calls`, `SliceMethodPanic::RangeIndex`) then emitted the always-violated
// `Bool(true)` as a REFUTABLE `SliceBoundsCheck`, and every correct program whose range
// bound is a loop-mutated local FAILED with an arbitrary model:
//
//   * `while let Some(ch) = it.next() { if size + len > 23 { return } buf[len..]; len
//     += size }` (the smol_str `lib.rs:156` shape) — `len` read under the guard;
//   * `while len > 8 { len -= 1 } out[..len]` (the aterm-grid `presentation.rs:294`
//     shape) — `len` read on the loop exit edge.
//
// WHY NOT THE SEAL'S ANSWER. The seal resolved such a bound to its BARE name. The `1e`
// arm of `generate::safety` version-renames the violation at the INDEX CALL, so the
// bare name lands on the version the CALL reads, not the one the range was built from.
// Rewrite and guard the local in between and the guard discharges a violation about a
// value the range does not hold: `let r = ..len; len = n & 3; if len > 8 { return }
// buf[r]` (`buf: [u8; 8]`) was PROVED and clean-kernel certified on the seal and
// panics at `n = 9` (`stale_guard_bug`, `stale_guard_from_bug`, `stale_guard_loop_bug`
// and `stale_*` — the `class10_*` rows of `tests/slice_range_bound_at_call.rs`).
//
// WHAT IS SPELLED HERE INSTEAD. The bound local `L` at the statement `p` that READS IT
// INTO THE RANGE, versioned there: `L#<token at p>`, the same spelling the version
// rename gives every other read of `L` at `p` (`StmtVersionCtx::version_token_at`). An
// already-versioned name passes through the call-point rename untouched
// (`path_defs::version_rename_at`). A token names a reaching-definition SET, not a
// value, so a CONDITIONAL write to `L` between `p` and the call can leave a later guard
// on `L` spelled exactly like `p`'s read while it reads another value — the review's
// `joined_*_bug` probes PROVED that way. The bound is therefore named only when `L`'s
// SSA value (`version_ssa::ValueId`) at `p` IS its value at the call, under the same
// token (`same_value_at_call`): the violation then states what an ordinary index at the
// call states, and a write in between declines it. The chain at `-Copt-level=0` is
//
//   p: _18 = copy L            (a single-assignment temp; zero or more such hops)
//   a: _17 = RangeFrom { start: move _18 }
//   q: index(.., move _17)     (the terminator of the call block)
//
// and optimized MIR drops the temp (`a` reads `copy L` itself, and `p` is `a`). An
// inclusive range `L0..=L` below `-Copt-level=2` has no aggregate: `a` is then the
// terminator of `_17 = RangeInclusive::new(.., move _18)`, whose return writes the
// range (2026-10-14, `range_inclusive_new_at`; the BTree and VecDeque range lanes ask
// this module too, through `panic_calls::range_bound_at_call_formula`). Each hop
// is the definition the read SEES (`StmtVersionCtx::value_id_at`), or, where the oracle
// cannot name the read, the one definition of a local that has exactly one
// (`local_defs::unique_defining_block`).
//
// SOUNDNESS. Each hop reads a local whose definition at the read is a whole-local
// `Assign` `(c, j)`, re-checked here to DOMINATE the read (`point_dominates`): by the
// `version_ssa::ValueId` contract (or, on the fallback, because `(c, j)` is the local's
// only write) the local holds, at the read, the value that statement wrote on its LAST
// visit. So the range the call
// receives was built by the last visit of `a` before the call. `p` dominates `a`, so no
// path from `p` to the call avoids `a` (prefixed with the `a`-free path from the entry
// to `p`'s first visit, it would reach the call without `a`): the last `p` before the
// call precedes that last `a`, and it is the `p` whose temp `a` read. The temp therefore
// holds `L` as read at that `p`, and the version token at `p` is the name the encoding
// gives exactly that read.
//
// A local takes part only when the write index behind the oracle sees every write to
// it: it is stable, or every write is a whole-local write with a located destination
// (an `Assign` or a `Call` destination — `local_defs::every_write_is_whole_located`).
// An ENTRY-valued read (no token at `p`) is spelled bare only when NO point of the
// function versions the name (`StmtVersionCtx::ever_versioned`), so no rename anywhere
// can move it; otherwise it declines. Anything that declines (`None`) makes the lane
// emit its fail-closed `UnsupportedMir` row: Unknown, never a proof, never a refutation.
//
// WHAT IS NOT DONE. A hop through a single-assignment local whose definition is not a
// whole-local copy (`n = PtrMetadata(s)` with `s` reseatable, a call result) is the
// global resolver's own decision and is not overridden; a by-reference range is
// declined. The yield-fact lane (`iterator_yield::build_range_yield_guard_map`) is
// untouched: it inlines its bound into a fact keyed on the PAYLOAD, which no
// single-point version can serve, and keeps declining a multiply-assigned bound.
//
// Trust: 2026-10-08 (H1, STALE-BOUND-CALL-RENAME). A PROJECTED bound (`..*z`,
// `..(*s).len`) is named here too, by the same rule: its FOLDED name (`len`, `s*.len`)
// versioned at the read into the range, when that is its value at the call
// (`projected_read_name` says which storage qualifies). The global resolver used to
// answer it with the bare name on the pointer's licence alone, re-stamped at the CALL
// (`iterator_yield::projected_bound_names_one_value` now refuses that), and a write to
// the pointee between the range and the call proved panicking programs.

use trust_types::{
    BasicBlock, BlockId, Formula, Operand, Place, Rvalue, Statement, VerifiableFunction,
};

use super::StmtVersionCtx;
use super::version_ssa::ValueId;

/// Hops followed in total (range-local copies plus bound-temp copies). Debug MIR needs
/// one of each; the cap only bounds pathological copy chains.
const HOP_FUEL: u32 = 8;

/// A program point: `(block, i)` is the read by statement `i` of `block`, and
/// `(block, stmts.len())` the read by its terminator.
type Point = (BlockId, usize);

/// A value identity is only as good as the write index behind it, which records
/// statement and terminator destinations, not writes through an escaped `&mut`: a local
/// takes part when it is stable, or every write to it is a whole-local write with a
/// located destination (`local_defs::every_write_is_whole_located` — a named `Assign`
/// or a `Call` destination, both def sites of the SSA oracle). This is
/// `dominating_facts`' gate with the `Call` destination admitted, which the loop-carried
/// `let mut len = bands.len().min(16)` needs and the oracle stamps (`s{b}_t`).
fn admits(func: &VerifiableFunction, local: usize) -> bool {
    !crate::guards::value_local_is_unstable(func, local)
        || crate::local_defs::every_write_is_whole_located(func, local)
}

/// `def` runs before `read` on every execution reaching `read`: an earlier statement of
/// the same block, or a statement of a block that strictly dominates `read`'s.
fn point_dominates(sv: &StmtVersionCtx, def: Point, read: Point) -> bool {
    if def.0 == read.0 {
        return def.1 < read.1;
    }
    let cfg = sv.cfg();
    def.0.0 < cfg.n_blocks()
        && read.0.0 < cfg.n_blocks()
        && cfg.dom().dominates(def.0.0 as u32, read.0.0 as u32)
}

/// The whole-local `Assign` that wrote the value `local` holds when read at `at`, and
/// where it is — `None` for an entry value, a join, a terminator (call) definition, an
/// unnameable read, or a defining statement that does not dominate the read.
///
/// The definition is the one the read SEES (`StmtVersionCtx::value_id_at`). Where the
/// oracle cannot name it — a whole read of a local whose FIELD names are tracked too
/// (`let r = ..len;` is read whole at the call while `r.0` / `r@0.0` rebind it, and a
/// read rebound by two tracked names has no single identity) — a local with exactly one
/// value channel (`local_defs::unique_defining_block`: one whole write, not a
/// parameter, no partial or aliased write) has one definition, and every read it
/// dominates sees it.
fn defining_assign<'f>(
    func: &'f VerifiableFunction,
    sv: &StmtVersionCtx,
    local: usize,
    at: Point,
) -> Option<(Point, &'f Rvalue)> {
    let name = crate::place_to_var_name(func, &Place::local(local));
    let (block, stmt) = match sv.value_id_at(func, at.0, at.1, &name) {
        Some(ValueId::Def { block, stmt }) if stmt != u32::MAX => (block as usize, stmt as usize),
        Some(_) => return None,
        None if crate::local_defs::is_parameter(func, local) => return None,
        None => {
            let block = crate::local_defs::unique_defining_block(func, local)?;
            let stmt = func.body.blocks.get(block)?.stmts.iter().position(|s| {
                matches!(s, Statement::Assign { place, .. }
                    if place.local == local && place.projections.is_empty())
            })?;
            (block, stmt)
        }
    };
    let blk = func.body.blocks.get(block).filter(|b| b.id.0 == block)?;
    let def_at = (blk.id, stmt);
    if !point_dominates(sv, def_at, at) {
        return None;
    }
    match blk.stmts.get(stmt)? {
        Statement::Assign { place, rvalue, .. }
            if place.local == local && place.projections.is_empty() =>
        {
            Some((def_at, rvalue))
        }
        _ => None,
    }
}

/// Trust: 2026-10-14 — the point at which the call `RangeInclusive::new(..)` whose return
/// is `local`'s ONE value reads its arguments (its block's terminator), when `bound` is
/// one of those arguments (by identity, as for an aggregate operand) and that block
/// dominates `at`. `None` otherwise.
///
/// `a..=b` is not an aggregate below `-Copt-level=2`: it is `_r = RangeInclusive::new(a,
/// b)`, and the `BTreeMap::range` / slice `[a..=b]` call receives `_r`. The definition
/// question goes through the seam: `local_defs::unique_value_call` answers only for a
/// local whose ONE value is that call's return (never a parameter, a second write, a
/// partial or an aliased write), and `local_defs::unique_defining_block` names its
/// block. That block dominates `at`, so every path to `at` crosses the call's last
/// visit before `at`, and the range `at` reads holds the arguments that visit read: the
/// aggregate `a` of the module banner with `a` the call's terminator, and the bound walk
/// continues from it unchanged. The callee is std's own constructor
/// (`alloc_vcs::is_range_inclusive_new_call`, the identity the BTree and slice lanes
/// already read `new`'s arguments through), which stores `start` and `end` as given.
fn range_inclusive_new_at(
    func: &VerifiableFunction,
    sv: &StmtVersionCtx,
    local: usize,
    at: Point,
    bound: &Operand,
) -> Option<Point> {
    if crate::local_defs::is_parameter(func, local)
        || !super::terminator_presence_for(func).has_bare_dest_call
    {
        return None;
    }
    let call = crate::local_defs::unique_value_call(func, local)?;
    let trust_types::Terminator::Call { func: callee, args, .. } = call else { return None };
    if !super::alloc_vcs::is_range_inclusive_new_call(callee)
        || !args.iter().any(|arg| std::ptr::eq(arg, bound))
    {
        return None;
    }
    let block = crate::local_defs::unique_defining_block(func, local)?;
    let blk = func.body.blocks.get(block).filter(|b| b.id.0 == block)?;
    if !std::ptr::eq(&blk.terminator, call) {
        return None;
    }
    let read = (blk.id, blk.stmts.len());
    (read.0 != at.0 && point_dominates(sv, read, at)).then_some(read)
}

/// The bound operand `bound` of the range aggregate that `range_operand` carries into
/// the index call terminating `call_block`, spelled as its root local VERSIONED AT THE
/// STATEMENT THAT READS IT INTO THE RANGE (see the module banner). `None` declines.
///
/// `bound` must be one of the aggregate's own operands (it is located by identity,
/// `std::ptr::eq`, so the caller's tracer and this walk agree on the aggregate).
pub(super) fn range_bound_at_call(
    func: &VerifiableFunction,
    range_operand: &Operand,
    bound: &Operand,
    call_block: &BasicBlock,
) -> Option<Formula> {
    let (Operand::Copy(range_place) | Operand::Move(range_place)) = range_operand else {
        return None;
    };
    let (Operand::Copy(bound_place) | Operand::Move(bound_place)) = bound else {
        // A constant resolves globally; nothing else reaches here.
        return None;
    };
    // A PROJECTED bound (`copy (*z)` read straight into the aggregate at `-O1`) is
    // named below by `projected_read_name` (2026-10-08, H1).
    if !range_place.projections.is_empty()
        || crate::local_defs::is_parameter(func, range_place.local)
        || !admits(func, range_place.local)
    {
        return None;
    }
    let sv = super::stmt_versions_for(func);
    let call = (call_block.id, call_block.stmts.len());
    let mut fuel = HOP_FUEL;

    // The aggregate statement `a` whose value the call receives, through whole-local
    // copies of the range local.
    let mut local = range_place.local;
    let mut at = call;
    let aggregate = loop {
        if fuel == 0
            || (local != range_place.local
                && (crate::local_defs::is_parameter(func, local) || !admits(func, local)))
        {
            return None;
        }
        fuel -= 1;
        // Trust: 2026-10-14 — or the `RangeInclusive::new(a, b)` call that builds `a..=b`
        // at `-Copt-level=0` and `1`, where no aggregate is emitted: its terminator reads
        // the bound, and its return writes the range (`range_inclusive_new_at`).
        if let Some(new_at) = range_inclusive_new_at(func, &sv, local, at, bound) {
            break new_at;
        }
        let (def_at, rvalue) = defining_assign(func, &sv, local, at)?;
        match rvalue {
            Rvalue::Aggregate(_, operands) if operands.iter().any(|o| std::ptr::eq(o, bound)) => {
                break def_at;
            }
            Rvalue::Use(Operand::Copy(src) | Operand::Move(src)) if src.projections.is_empty() => {
                local = src.local;
                at = def_at;
            }
            _ => return None,
        }
    };

    // The bound read at `a`, through single-assignment whole-local copies (the `-O0`
    // temp) — the hop `resolve_range_bound_formula` takes — to the place `P` read into
    // the range: the root local `L`, or a projected place (`(*z)`, `(*s).len`).
    let mut read: &Place = bound_place;
    let mut at = aggregate;
    while read.projections.is_empty()
        && crate::local_defs::is_single_static_assignment(func, read.local)
    {
        if fuel == 0 || !admits(func, read.local) {
            return None;
        }
        fuel -= 1;
        match defining_assign(func, &sv, read.local, at)? {
            (def_at, Rvalue::Use(Operand::Copy(src) | Operand::Move(src))) => {
                read = src;
                at = def_at;
            }
            // A single-valued root the global resolver declined (an unlicensed
            // `PtrMetadata`/`Len`) — its decision, not overridden here.
            _ => return None,
        }
    }
    // `at` is the statement that reads `P` into the range (directly, or into the temp
    // the range is built from): name `P` by its version THERE.
    let (name, sort) = if read.projections.is_empty() {
        if !admits(func, read.local) {
            return None;
        }
        let bare = crate::operand_to_formula(func, &Operand::Copy(Place::local(read.local)));
        let Formula::Var(name, sort) = bare else { return None };
        (name, sort)
    } else {
        projected_read_name(func, read)?
    };
    let token = same_value_at_call(func, &sv, &name, at, call)?;
    match token {
        Some(token) => Some(Formula::Var(format!("{name}#{token}"), sort)),
        // The entry value at `p`: bare is a name of it only if no rename can move it.
        None => (!sv.ever_versioned(func, &name)).then_some(Formula::Var(name, sort)),
    }
}

/// Trust: 2026-10-08 (H1 of the ploss adversarial pass, STALE-BOUND-CALL-RENAME —
/// FALSE PROOF) — the name of a PROJECTED place `P` read into the range (`(*z)`,
/// `(*s).len`, `st.len`), when every write to the storage it denotes is a write the
/// version oracle records under that name. `range_bound_at_call` then names it by its
/// version at the read, exactly as it names a local, and only when that is its value
/// at the call (`same_value_at_call`).
///
/// The name is the FOLDED one (`place_to_var_name`, whose storage is
/// `crate::canonical_place`): `*z` with `z = &len` is `len`, and `*z` with `z = &s.len`
/// is `s*.len`. The global resolver used to hand that bare name back on the POINTER's
/// licence alone, and the call-point rename bound it to whatever the pointee held at
/// the CALL. A write to `len` between the range and the call, plus a guard on the new
/// value, then proved a panicking index (`iterator_yield::projected_bound_names_one_value`
/// has the reproducers). Here the storage itself is licensed:
///  * the pointer `P` reads through holds one value, is never written through a
///    projection, and its index locals hold one value (the global resolver's pointer
///    licence: the name denotes one storage at every point);
///  * the body's OWN storage (no `Deref` after the fold) is rooted at a local the
///    oracle sees every write to (`admits`: no `&mut`/raw alias, no partial write);
///  * memory behind a pointer is admitted only one `Deref` deep from a never-written
///    PARAMETER that is never written through a projection. Its entry value addresses
///    the caller's memory, which no write to this body's own storage can reach. Every
///    remaining write to it is a store through some other pointer or a callee's write,
///    and the oracle versions the name at both (the alias havoc of `path_defs`). That is
///    the same oracle an ordinary read of the place at the call relies on.
/// Anything else declines: never a proof, never a refutation.
fn projected_read_name(
    func: &VerifiableFunction,
    place: &Place,
) -> Option<(String, trust_types::Sort)> {
    use trust_types::Projection;
    let ssa = |local| crate::local_defs::is_single_static_assignment(func, local);
    let index_locals_ssa =
        |p: &Place| crate::local_defs::place_index_locals_are_single_static_assignment(func, p);
    if !(ssa(place.local)
        && index_locals_ssa(place)
        && !super::iterator_yield::local_has_projected_write(func, place.local))
    {
        return None;
    }
    let referent = crate::canonical_place(func, place);
    let derefs = referent.projections.iter().filter(|q| matches!(q, Projection::Deref)).count();
    let tracked = index_locals_ssa(&referent)
        && match derefs {
            0 => admits(func, referent.local),
            1 => {
                matches!(referent.projections.first(), Some(Projection::Deref))
                    && crate::local_defs::is_parameter(func, referent.local)
                    && ssa(referent.local)
                    && !super::iterator_yield::local_has_projected_write(func, referent.local)
            }
            _ => false,
        };
    if !tracked {
        return None;
    }
    match crate::operand_to_formula(func, &Operand::Copy(place.clone())) {
        Formula::Var(name, sort) => Some((name, sort)),
        _ => None,
    }
}

/// Trust: 2026-10-02 (class-10 review, FALSE PROOF) — `L` holds at the index call
/// `call` the very value the range read at `read`, and the two points SPELL it alike.
///
/// A version token is the spelling of a reaching-definition SET, not of a value
/// (`version_ssa::ValueId`). The read into the range and a guard after a CONDITIONAL
/// write of `L` can see the same set while reading different values:
///
/// ```text
/// for &c in xs { let r = ..len; if c { len = n; } if len > 8 { return acc; } buf[r] }
/// ```
///
/// (`buf: &[u8; 8]`): `len` reaches the read and the guard as `{init, D}`, both spelled
/// `len#s0_0_s7_0`, so the guard's `!(len#.. > 8)` contradicted the violation
/// `len#.. > 8` and the row PROVED with a clean-kernel certificate — and panics at
/// `xs = [true], m = 100, n = 0` (`class10_joined_after_bug` and its exit/pair twins in
/// `tests/slice_range_bound_at_call.rs`). Such a guard reads `L` at a point the call's
/// value reaches; requiring the read's `ValueId` to BE the call's makes the violation a
/// statement about the value `L` has at the call, which is what an ordinary
/// `buf[..len]` at the call states, under the same name.
///
/// `read` dominates `call` (each hop's definition dominates its read, and the aggregate
/// dominates the call), so by the `ValueId` contract equal ids mean equal values. The
/// two tokens are required equal too, so the name is the call's own spelling; an
/// unnameable read at either point declines. A range read whose value is rewritten
/// before the call (the `stale_*` probes) therefore declines to the Unknown
/// `slice-range-bounds-unresolved` row: never a proof, never a refutation.
fn same_value_at_call(
    func: &VerifiableFunction,
    sv: &StmtVersionCtx,
    name: &str,
    read: Point,
    call: Point,
) -> Option<Option<String>> {
    if !point_dominates(sv, read, call) {
        return None;
    }
    let at_read = sv.value_id_at(func, read.0, read.1, name)?;
    if sv.value_id_at(func, call.0, call.1, name) != Some(at_read) {
        return None;
    }
    let token_at_read = sv.version_token_at(func, read.0, read.1, name);
    (token_at_read.as_deref() == sv.version_token_at(func, call.0, call.1, name).as_deref())
        .then_some(token_at_read)
}
