//! How many times can a block run? Execution bounds over a function's
//! natural-loop nest, shared by trust-vcgen's accumulator lane
//! (`generate::loop_bounds`) and the trust-ir-bridge's native port of it, which
//! does not link trust-vcgen. Both mint `acc <= init + K * per_max` from the `K`
//! this returns, so they must agree on it: one definition, two callers.
//!
//! WHY PER BLOCK (Trust, 2026-09-29). Both lanes used to take `K` as the product
//! of the trip counts of every loop in the function, and read it as a bound on
//! every self-add. It is not one. Measured on stage 1, each of these panics with
//! `attempt to add with overflow` (`c: u8`) and was proved, kernel-certified
//! under `certify`:
//!
//! * `loop { let mut r = 0..10; match r.next() { Some(_) => c += 1, None => break } }`
//!   builds a new iterator every iteration, so its trip count bounds nothing;
//! * `loop { if flag { c += 1; continue; } match r.next() { … } }` has a cycle
//!   that never calls `next`;
//! * `for _ in 0..0 {} for _ in 0..300 { c += 1 }` multiplied by the EMPTY
//!   sibling loop's trip count, 0;
//! * `loop { match r.next() { Some(_) => {}, None => c += 1 } }` adds on the
//!   `None` arm, which repeats forever once the range is exhausted;
//! * `loop { c += 1; if i >= 10 { break } i += 1 }` runs the add 11 times, once
//!   more than the loop's 10 continuing iterations.
//!
//! THE ARGUMENT. A bound on block `b` is a product over the loops that CONTAIN
//! `b`, innermost first. Each needs a DRIVER ([`LoopDriver`]): an edge every
//! iteration that returns to the header crosses, and a bound `trip` on how often
//! one entry of the loop can cross it — a `next` call's `Some` edge, or a counter
//! test's continue edge; the callers decide which and supply `trip`. Then:
//!
//! * an entry of the loop runs at most `trip + 1` iterations: each one that
//!   returns crossed the edge, and one more may exit;
//! * a block in the loop but in no loop nested in it runs at most once per
//!   iteration — twice would be a cycle inside the iteration, i.e. a nested loop;
//! * so it runs at most `trip` times per entry when it sits BEHIND the edge (no
//!   path from the header reaches it without crossing the edge), and `trip + 1`
//!   otherwise;
//! * a nested loop is entered at most once per iteration of the loop around it,
//!   and a loop no other loop contains is entered at most once. Both hold in a
//!   REDUCIBLE CFG with loops merged per header: a second entry within one
//!   iteration would be a cycle through the nested loop's header that leaves its
//!   body, which puts that cycle's blocks in the body. [`LoopNest::of`] refuses an
//!   irreducible CFG and loops that do not nest.
//!
//! So `K(b)` = the product, over `b`'s containing loops, of `trip` or `trip + 1`
//! as the block (and then each nested loop's header) sits behind that loop's
//! driver edge or not. A sibling loop is not a factor, and a zero trip count
//! makes `K = 0` only for blocks that sit behind that edge — which then never run.

use crate::fx::{FxHashMap, FxHashSet};
use crate::structural_termination::for_each_terminator_successor;
use crate::{
    LocalWrite, Operand, Place, Projection, Rvalue, Statement, Terminator, VerifiableBody,
};

/// A natural loop: its header, and every block that reaches one of its back
/// edges without passing through the header, merged over all back edges into
/// that header.
#[derive(Debug)]
pub struct NaturalLoop {
    header: usize,
    body: FxHashSet<usize>,
}

impl NaturalLoop {
    /// The header block's id.
    #[must_use]
    pub fn header(&self) -> usize {
        self.header
    }

    /// True iff `block` is in the loop's body (the header included).
    #[must_use]
    pub fn contains(&self, block: usize) -> bool {
        self.body.contains(&block)
    }
}

/// What bounds the iterations of one loop: an edge `(from, to)` every iteration
/// that returns to the header crosses, and an upper bound on how many times one
/// entry of the loop can cross it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LoopDriver {
    pub edge: (usize, usize),
    pub trip: i128,
}

/// The loops of one function body, with its successor relation.
#[derive(Debug)]
pub struct LoopNest {
    loops: Vec<NaturalLoop>,
    succ: FxHashMap<usize, Vec<usize>>,
}

impl LoopNest {
    /// The body's natural loops, or `None` when the CFG is irreducible or the
    /// loops do not nest. A loop with a second entry has no header that every
    /// iteration passes, so nothing is claimed about it.
    #[must_use]
    pub fn of(body: &VerifiableBody) -> Option<Self> {
        let mut succ: FxHashMap<usize, Vec<usize>> =
            FxHashMap::with_capacity_and_hasher(body.blocks.len(), Default::default());
        for b in &body.blocks {
            let mut edges = Vec::new();
            for_each_terminator_successor(&b.terminator, |s| edges.push(s.0));
            succ.insert(b.id.0, edges);
        }
        let Some(entry) = body.blocks.first().map(|b| b.id.0) else {
            return Some(Self { loops: Vec::new(), succ });
        };
        // DFS from the entry: `u -> v` is a back edge iff `v` is on the stack.
        // `color` ends up holding every reachable block.
        let mut color: FxHashMap<usize, u8> = FxHashMap::default();
        let mut back_edges: Vec<(usize, usize)> = Vec::new();
        color.insert(entry, 1);
        let mut stack: Vec<(usize, usize)> = vec![(entry, 0)];
        while let Some(&(u, i)) = stack.last() {
            let edges = succ.get(&u).map(Vec::as_slice).unwrap_or(&[]);
            if let Some(&v) = edges.get(i) {
                stack.last_mut()?.1 += 1;
                match color.get(&v).copied().unwrap_or(0) {
                    0 => {
                        color.insert(v, 1);
                        stack.push((v, 0));
                    }
                    1 => back_edges.push((u, v)),
                    _ => {}
                }
            } else {
                color.insert(u, 2);
                stack.pop();
            }
        }
        let mut pred: FxHashMap<usize, Vec<usize>> = FxHashMap::default();
        for &u in color.keys() {
            for &v in succ.get(&u).map(Vec::as_slice).unwrap_or(&[]) {
                pred.entry(v).or_default().push(u);
            }
        }
        let mut by_header: FxHashMap<usize, Vec<usize>> = FxHashMap::default();
        for (u, h) in back_edges {
            by_header.entry(h).or_default().push(u);
        }
        let mut loops = Vec::new();
        for (header, back_sources) in by_header {
            let mut body: FxHashSet<usize> = FxHashSet::default();
            body.insert(header);
            let mut work = back_sources;
            while let Some(x) = work.pop() {
                if body.insert(x) {
                    work.extend(pred.get(&x).map(Vec::as_slice).unwrap_or(&[]).iter().copied());
                }
            }
            // SINGLE ENTRY: no block of the body but the header has a predecessor
            // outside it, and the function entry is in the body only as its header.
            // Otherwise the header does not dominate the body.
            let single_entry = body.iter().all(|&x| {
                x == header
                    || (x != entry
                        && pred.get(&x).is_none_or(|ps| ps.iter().all(|p| body.contains(p))))
            });
            if !single_entry {
                return None;
            }
            loops.push(NaturalLoop { header, body });
        }
        for (i, a) in loops.iter().enumerate() {
            for b in &loops[i + 1..] {
                let overlap = a.body.iter().any(|x| b.body.contains(x));
                if overlap && !a.body.is_subset(&b.body) && !b.body.is_subset(&a.body) {
                    return None;
                }
            }
        }
        Some(Self { loops, succ })
    }

    /// The loops containing `block`, innermost first.
    #[must_use]
    pub fn containing(&self, block: usize) -> Vec<&NaturalLoop> {
        let mut chain: Vec<&NaturalLoop> =
            self.loops.iter().filter(|l| l.contains(block)).collect();
        // Nested bodies are strictly smaller.
        chain.sort_by_key(|l| l.body.len());
        chain
    }

    /// True iff `block` is in `lp` and in no loop nested in `lp`.
    #[must_use]
    pub fn owns(&self, lp: &NaturalLoop, block: usize) -> bool {
        lp.contains(block)
            && !self
                .loops
                .iter()
                .any(|l| l.header != lp.header && l.contains(block) && l.body.is_subset(&lp.body))
    }

    fn succs(&self, block: usize) -> &[usize] {
        self.succ.get(&block).map(Vec::as_slice).unwrap_or(&[])
    }

    /// True iff every iteration of `lp` that returns to the header crosses
    /// `edge`: no walk of the body from the header that avoids `edge` takes an
    /// edge back into the header. (A bottom-tested loop's driver edge IS its back
    /// edge, so this asks about edges into the header, not about blocks.)
    #[must_use]
    pub fn crosses_every_iteration(&self, lp: &NaturalLoop, edge: (usize, usize)) -> bool {
        let mut seen: FxHashSet<usize> = FxHashSet::default();
        let mut work = vec![lp.header];
        while let Some(b) = work.pop() {
            if !lp.contains(b) || !seen.insert(b) {
                continue;
            }
            for &s in self.succs(b) {
                if (b, s) == edge {
                    continue;
                }
                if s == lp.header {
                    return false;
                }
                work.push(s);
            }
        }
        true
    }

    /// True iff `block` sits behind `edge` in `lp`: no walk of the body from the
    /// header that avoids `edge` reaches it. The header itself never does.
    #[must_use]
    pub fn behind(&self, lp: &NaturalLoop, edge: (usize, usize), block: usize) -> bool {
        let mut seen: FxHashSet<usize> = FxHashSet::default();
        let mut work = vec![lp.header];
        while let Some(b) = work.pop() {
            if !lp.contains(b) || !seen.insert(b) {
                continue;
            }
            if b == block {
                return false;
            }
            work.extend(self.succs(b).iter().copied().filter(|&s| (b, s) != edge));
        }
        true
    }

    /// True iff every iteration of `lp` passes through `block`: no walk of the
    /// body from the header that avoids `block` takes an edge back into the header.
    #[must_use]
    pub fn every_iteration_passes(&self, lp: &NaturalLoop, block: usize) -> bool {
        if block == lp.header {
            return true;
        }
        let mut seen: FxHashSet<usize> = FxHashSet::default();
        let mut work = vec![lp.header];
        while let Some(b) = work.pop() {
            if b == block || !lp.contains(b) || !seen.insert(b) {
                continue;
            }
            for &s in self.succs(b) {
                if s == lp.header {
                    return false;
                }
                work.push(s);
            }
        }
        true
    }

    /// An upper bound on how many times `block` runs in one call (see the
    /// module docs). `drivers` offers candidate drivers for a loop; the first
    /// whose edge every iteration crosses is used. `None` when some containing
    /// loop has none, or on arithmetic overflow.
    pub fn block_execution_bound(
        &self,
        block: usize,
        mut drivers: impl FnMut(&Self, &NaturalLoop) -> Vec<LoopDriver>,
    ) -> Option<i128> {
        let mut bound: i128 = 1;
        // The block, then each nested loop's header: what runs once per iteration.
        let mut once_per_iteration = block;
        for lp in self.containing(block) {
            let driver = drivers(self, lp)
                .into_iter()
                .find(|d| d.trip >= 0 && self.crosses_every_iteration(lp, d.edge))?;
            let factor = if self.behind(lp, driver.edge, once_per_iteration) {
                driver.trip
            } else {
                driver.trip.checked_add(1)?
            };
            bound = bound.checked_mul(factor)?;
            once_per_iteration = lp.header;
        }
        Some(bound)
    }
}

/// The `Iterator::next` call that can drive `lp`: the ONE call `is_next` accepts
/// in `lp`'s own blocks ([`LoopNest::owns`]), whose return block switches on
/// its result's discriminant and is entered from that call alone. Returns
/// `(dest local, Some edge)`: `Option`'s discriminant 1 is `Some`. `None` for two
/// such calls, no switch, a switch another block also jumps to, or a switch whose
/// `Some` and `None` arms meet (cutting one edge would cut both).
///
/// The sole-predecessor clause is what makes each crossing of the `Some` edge
/// one `Some` the iterator yielded: a second way into the switch would re-read
/// the previous result without advancing the iterator (trip-count lane review,
/// 2026-09-29).
pub fn next_call_driving(
    body: &VerifiableBody,
    nest: &LoopNest,
    lp: &NaturalLoop,
    is_next: impl Fn(&str) -> bool,
) -> Option<(usize, (usize, usize))> {
    let mut found = None;
    for block in &body.blocks {
        let Terminator::Call { func: callee, dest, target, .. } = &block.terminator else {
            continue;
        };
        if !nest.owns(lp, block.id.0) || !is_next(callee) {
            continue;
        }
        if found.is_some() || !dest.projections.is_empty() {
            return None;
        }
        found = Some((block.id.0, dest.local, (*target)?));
    }
    let (call_block_id, dest, switch) = found?;
    if !nest.owns(lp, switch.0) {
        return None;
    }
    let mut entries = nest.succ.iter().filter(|(_, succs)| succs.contains(&switch.0));
    let (Some((&only, _)), None) = (entries.next(), entries.next()) else { return None };
    if only != call_block_id {
        return None;
    }
    let switch_block = body
        .blocks
        .get(switch.0)
        .filter(|b| b.id == switch)
        .or_else(|| body.blocks.iter().find(|b| b.id == switch))?;
    let Terminator::SwitchInt { discr, targets, otherwise, .. } = &switch_block.terminator else {
        return None;
    };
    let (Operand::Copy(d) | Operand::Move(d)) = discr else { return None };
    let reads_result_discriminant = d.projections.is_empty()
        && switch_block.stmts.iter().any(|stmt| {
            matches!(
                stmt,
                Statement::Assign { place, rvalue: Rvalue::Discriminant(read), .. }
                    if place.local == d.local
                        && place.projections.is_empty()
                        && read.local == dest
                        && read.projections.is_empty()
            )
        });
    if !reads_result_discriminant {
        return None;
    }
    let arm = |value: u128| targets.iter().find(|(v, _)| *v == value).map(|(_, b)| b.0);
    let some = arm(1).unwrap_or(otherwise.0);
    let none = arm(0).unwrap_or(otherwise.0);
    (some != none).then_some((dest, (switch.0, some)))
}

/// True iff `rvalue` may read `local`. Exhaustive (this crate owns `Rvalue`), so a
/// new variant fails to compile until it is classified here.
fn rvalue_may_read(rvalue: &Rvalue, local: usize) -> bool {
    let place_reads = |p: &Place| {
        p.local == local
            || p.projections.iter().any(|q| matches!(q, Projection::Index(i) if *i == local))
    };
    let op_reads =
        |op: &Operand| matches!(op, Operand::Copy(p) | Operand::Move(p) if place_reads(p));
    match rvalue {
        Rvalue::Use(op) | Rvalue::UnaryOp(_, op) | Rvalue::Cast(op, _) | Rvalue::Repeat(op, _) => {
            op_reads(op)
        }
        Rvalue::BinaryOp(_, a, b)
        | Rvalue::CheckedBinaryOp(_, a, b)
        | Rvalue::UncheckedBinaryOp(_, a, b) => op_reads(a) || op_reads(b),
        Rvalue::PtrOffset { ptr, count } => op_reads(ptr) || op_reads(count),
        Rvalue::Aggregate(_, ops) => ops.iter().any(op_reads),
        Rvalue::Unsupported { operands, .. } => operands.iter().any(op_reads),
        Rvalue::Ref { place, .. }
        | Rvalue::AddressOf(_, place)
        | Rvalue::Discriminant(place)
        | Rvalue::Len(place)
        | Rvalue::CopyForDeref(place) => place_reads(place),
    }
}

/// `stmt` is `q = &mut instance` (both whole locals, `q` not the `next` receiver)
/// and `q`'s every other occurrence is as the SOLE argument of a call to the
/// sysroot `Peekable::peek` (at least one such call): no
/// statement reads or writes `q` besides such borrows, and no other terminator
/// mentions it. Those calls buffer
/// at most one item the instance's own `next` then returns, so the instance yields
/// no more `Some`s than its source (sweep q45, `if it.peek() != Some(&&x)`). Any
/// other method (`peek_mut`, whose `&mut` result can rewrite the buffered item and
/// is refused by the vcgen conduit gate too, `next_if`, `by_ref`, a user trait)
/// keeps the escape refusing.
fn is_peek_only_borrow(
    body: &VerifiableBody,
    stmt: &Statement,
    instance: usize,
    receiver: usize,
) -> bool {
    let Statement::Assign { place: q, rvalue: Rvalue::Ref { mutable: true, place: src }, .. } =
        stmt
    else {
        return false;
    };
    if !q.projections.is_empty()
        || q.local == receiver
        || q.local == instance
        || src.local != instance
        || !src.projections.is_empty()
    {
        return false;
    }
    let q = q.local;
    let is_peek = |func: &str| {
        !crate::path_has_unauthenticated_crate_stamp(func)
            && crate::utils::strip_generics_eq(
                func,
                "core::iter::adapters::peekable::Peekable::peek",
            )
    };
    let mentions = |op: &Operand| matches!(op, Operand::Copy(p) | Operand::Move(p) if p.local == q);
    let mut peeks = false;
    for block in &body.blocks {
        for other in &block.stmts {
            let is_peek_borrow = matches!(
                other,
                Statement::Assign { place, rvalue: Rvalue::Ref { mutable: true, place: src }, .. }
                    if place.local == q && place.projections.is_empty()
                        && src.local == instance && src.projections.is_empty()
            );
            if is_peek_borrow {
                continue;
            }
            if !matches!(other.local_write(q), LocalWrite::Untouched)
                || other.escapes_local(q)
                || matches!(other, Statement::Assign { rvalue, .. } if rvalue_may_read(rvalue, q))
            {
                return false;
            }
        }
        match &block.terminator {
            Terminator::Call { func, args, dest, .. } => {
                if dest.local == q {
                    return false;
                }
                if args.iter().any(mentions) {
                    if !(is_peek(func) && args.len() == 1) {
                        return false;
                    }
                    peeks = true;
                }
            }
            Terminator::TailCall { args, .. } => {
                if args.iter().any(mentions) {
                    return false;
                }
            }
            Terminator::SwitchInt { discr: op, .. } | Terminator::Assert { cond: op, .. } => {
                if mentions(op) {
                    return false;
                }
            }
            Terminator::Drop { place, .. } => {
                if place.local == q {
                    return false;
                }
            }
            _ => {}
        }
    }
    // A borrow no `peek` reads is not this shape (a unit model of `let p = &mut r;
    // *p = …` elides the write); refuse it rather than accept it vacuously.
    peeks
}

/// True iff the iterator a `next` call advances is ONE instance for a whole
/// entry of `lp`. The caller has resolved the call's receiver to
/// `receiver = &mut instance` (a whole local); this checks that nothing inside
/// `lp` writes `instance`, that no write anywhere is unlocatable, and that the
/// only alias of `instance` is `receiver`, read by the `next` call writing
/// `next_dest` and by nothing else. A trip count bounds the `Some`s ONE instance
/// yields: `let mut r = 0..10` inside the loop makes a new instance every
/// iteration, and `let p = &mut r; *p = 0..10;` resets one.
#[must_use]
pub fn iterator_instance_is_fixed(
    body: &VerifiableBody,
    lp: &NaturalLoop,
    next_dest: usize,
    receiver: usize,
    instance: usize,
) -> bool {
    let reads_receiver =
        |op: &Operand| matches!(op, Operand::Copy(p) | Operand::Move(p) if p.local == receiver);
    for block in &body.blocks {
        let in_loop = lp.contains(block.id.0);
        let writes_instance = |write: LocalWrite<'_>| match write {
            LocalWrite::Untouched | LocalWrite::Escape => false,
            LocalWrite::Unlocatable => true,
            _ => in_loop,
        };
        for stmt in &block.stmts {
            if writes_instance(stmt.local_write(instance)) {
                return false;
            }
            if stmt.escapes_local(instance)
                && !matches!(
                    stmt,
                    Statement::Assign { place, .. }
                        if place.local == receiver && place.projections.is_empty()
                )
                && !is_peek_only_borrow(body, stmt, instance, receiver)
            {
                return false;
            }
            if let Statement::Assign { rvalue, .. } = stmt
                && rvalue_may_read(rvalue, receiver)
            {
                return false;
            }
        }
        if writes_instance(block.terminator.local_write(instance)) {
            return false;
        }
        let other_read = match &block.terminator {
            Terminator::Call { args, dest, .. } => {
                let is_driver = dest.local == next_dest && dest.projections.is_empty();
                args.iter().any(reads_receiver) && !(is_driver && args.len() == 1)
            }
            Terminator::TailCall { args, .. } => args.iter().any(reads_receiver),
            Terminator::SwitchInt { discr: op, .. } | Terminator::Assert { cond: op, .. } => {
                reads_receiver(op)
            }
            Terminator::Drop { place, .. } => place.local == receiver,
            _ => false,
        };
        if other_read {
            return false;
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{BasicBlock, BlockId, SourceSpan, UnwindEdge};

    // Locals: 1 `r` (the iterator), 2 `&mut r`, 3 the `next` result, 4 its
    // discriminant, 5 a flag.
    const R: usize = 1;
    const RECV: usize = 2;
    const OPT: usize = 3;
    const DISCR: usize = 4;
    const FLAG: usize = 5;

    fn block(id: usize, stmts: Vec<Statement>, terminator: Terminator) -> BasicBlock {
        BasicBlock { id: BlockId(id), stmts, terminator }
    }

    fn assign(place: usize, rvalue: Rvalue) -> Statement {
        Statement::Assign { place: Place::local(place), rvalue, span: SourceSpan::default() }
    }

    fn new_range() -> Statement {
        assign(R, Rvalue::Aggregate(crate::AggregateKind::Tuple, vec![]))
    }

    fn borrow_r() -> Statement {
        assign(RECV, Rvalue::Ref { mutable: true, place: Place::local(R) })
    }

    fn next_call(target: usize) -> Terminator {
        Terminator::Call {
            func: "next".into(),
            args: vec![Operand::Move(Place::local(RECV))],
            dest: Place::local(OPT),
            target: Some(BlockId(target)),
            span: SourceSpan::default(),
            atomic: None,
            is_unsafe_sig: false,
            callee_identity: None,
            callee_key: None,
            is_foreign: false,
            unwind: UnwindEdge::Unreachable,
        }
    }

    fn read_discriminant() -> Statement {
        assign(DISCR, Rvalue::Discriminant(Place::local(OPT)))
    }

    /// `switchInt(discr) -> [0: none, 1: some, otherwise: unreachable]`.
    fn switch_option(none: usize, some: usize, unreachable: usize) -> Terminator {
        Terminator::SwitchInt {
            discr: Operand::Move(Place::local(DISCR)),
            targets: vec![(0, BlockId(none)), (1, BlockId(some))],
            otherwise: BlockId(unreachable),
            exhaustive_enum_unreachable: false,
            span: SourceSpan::default(),
        }
    }

    fn branch(on: usize, if_true: usize, if_false: usize) -> Terminator {
        Terminator::SwitchInt {
            discr: Operand::Copy(Place::local(on)),
            targets: vec![(0, BlockId(if_false))],
            otherwise: BlockId(if_true),
            exhaustive_enum_unreachable: false,
            span: SourceSpan::default(),
        }
    }

    fn body(blocks: Vec<BasicBlock>) -> VerifiableBody {
        VerifiableBody {
            locals: vec![],
            blocks,
            arg_count: 0,
            return_ty: crate::Ty::Unit,
            datatype_defs: Default::default(),
        }
    }

    /// The `next` driver with trip count 10, when the instance checks pass.
    fn next_driver(body: &VerifiableBody, nest: &LoopNest, lp: &NaturalLoop) -> Vec<LoopDriver> {
        next_call_driving(body, nest, lp, |callee| callee == "next")
            .filter(|&(dest, _)| iterator_instance_is_fixed(body, lp, dest, RECV, R))
            .map(|(_, edge)| LoopDriver { edge, trip: 10 })
            .into_iter()
            .collect()
    }

    fn bound(body: &VerifiableBody, block: usize) -> Option<i128> {
        LoopNest::of(body)?.block_execution_bound(block, |nest, lp| next_driver(body, nest, lp))
    }

    /// `let mut r = …; loop { match r.next() { Some(_) => ADD, None => break } }`
    /// bb0 init | bb1 `&mut r; next` | bb2 switch | bb3 Some: ADD | bb4 exit | bb5 unreachable
    fn for_loop() -> VerifiableBody {
        body(vec![
            block(0, vec![new_range()], Terminator::Goto(BlockId(1))),
            block(1, vec![borrow_r()], next_call(2)),
            block(2, vec![read_discriminant()], switch_option(4, 3, 5)),
            block(3, vec![], Terminator::Goto(BlockId(1))),
            block(4, vec![], Terminator::Return),
            block(5, vec![], Terminator::Unreachable),
        ])
    }

    #[test]
    fn a_block_behind_the_some_edge_runs_trip_times() {
        assert_eq!(bound(&for_loop(), 3), Some(10));
    }

    #[test]
    fn a_block_outside_every_loop_runs_once() {
        assert_eq!(bound(&for_loop(), 4), Some(1));
    }

    #[test]
    fn the_header_runs_once_more_than_the_trip_count() {
        // The header block holds the `next` call, which also runs on the last,
        // exiting iteration.
        assert_eq!(bound(&for_loop(), 1), Some(11));
    }

    #[test]
    fn an_iterator_built_inside_the_loop_bounds_nothing() {
        // `loop { let mut r = …; match r.next() … }`: a fresh instance every time.
        let mut b = for_loop();
        b.blocks[0].stmts.clear();
        b.blocks[1].stmts.insert(0, new_range());
        assert_eq!(bound(&b, 3), None);
    }

    #[test]
    fn a_second_alias_of_the_iterator_bounds_nothing() {
        // `let p = &mut r; *p = …;` inside the loop resets the instance without a
        // statement that names `r` as its place.
        let mut b = for_loop();
        b.blocks[3].stmts.push(assign(6, Rvalue::Ref { mutable: true, place: Place::local(R) }));
        assert_eq!(bound(&b, 3), None);
    }

    #[test]
    fn a_cycle_that_skips_next_bounds_nothing() {
        // `loop { if flag { ADD; continue } match r.next() … }`
        // bb1 branch | bb6 ADD -> bb1 | bb7 `&mut r; next`.
        let b = body(vec![
            block(0, vec![new_range()], Terminator::Goto(BlockId(1))),
            block(1, vec![], branch(FLAG, 6, 7)),
            block(2, vec![read_discriminant()], switch_option(4, 3, 5)),
            block(3, vec![], Terminator::Goto(BlockId(1))),
            block(4, vec![], Terminator::Return),
            block(5, vec![], Terminator::Unreachable),
            block(6, vec![], Terminator::Goto(BlockId(1))),
            block(7, vec![borrow_r()], next_call(2)),
        ]);
        assert_eq!(bound(&b, 6), None);
    }

    #[test]
    fn a_none_arm_that_loops_bounds_nothing() {
        // `loop { match r.next() { Some(_) => {}, None => ADD } }`: the `None` arm
        // (bb4) returns to the header without crossing the `Some` edge.
        let mut b = for_loop();
        b.blocks[4].terminator = Terminator::Goto(BlockId(1));
        assert_eq!(bound(&b, 4), None);
    }

    #[test]
    fn a_sibling_loop_is_not_a_factor() {
        // Two sequential copies of the loop; the second's body block is bounded by
        // the second loop alone, whatever the first one's trip count.
        let b = body(vec![
            block(0, vec![new_range()], Terminator::Goto(BlockId(1))),
            block(1, vec![borrow_r()], next_call(2)),
            block(2, vec![read_discriminant()], switch_option(4, 3, 5)),
            block(3, vec![], Terminator::Goto(BlockId(1))),
            block(4, vec![], Terminator::Goto(BlockId(6))),
            block(5, vec![], Terminator::Unreachable),
            block(6, vec![], Terminator::Goto(BlockId(6))),
        ]);
        // bb6 is a self-loop with no driver: it bounds nothing, but it is not a
        // factor of bb3's bound.
        assert_eq!(bound(&b, 3), Some(10));
        assert_eq!(bound(&b, 6), None);
    }

    #[test]
    fn nested_loops_multiply() {
        // `for _ in outer { for _ in inner { ADD } }`, both drivers the same shape:
        // locals 1-4 for the outer, 11-14 for the inner.
        let offset = |mut s: Statement| {
            if let Statement::Assign { place, rvalue, .. } = &mut s {
                place.local += 10;
                match rvalue {
                    Rvalue::Ref { place, .. } | Rvalue::Discriminant(place) => place.local += 10,
                    _ => {}
                }
            }
            s
        };
        let inner_next = |target: usize| {
            let Terminator::Call { func, target: _, span, .. } = next_call(target) else {
                unreachable!()
            };
            Terminator::Call {
                func,
                args: vec![Operand::Move(Place::local(RECV + 10))],
                dest: Place::local(OPT + 10),
                target: Some(BlockId(target)),
                span,
                atomic: None,
                is_unsafe_sig: false,
                callee_identity: None,
                callee_key: None,
                is_foreign: false,
                unwind: UnwindEdge::Unreachable,
            }
        };
        let inner_switch = |none: usize, some: usize| Terminator::SwitchInt {
            discr: Operand::Move(Place::local(DISCR + 10)),
            targets: vec![(0, BlockId(none)), (1, BlockId(some))],
            otherwise: BlockId(5),
            exhaustive_enum_unreachable: false,
            span: SourceSpan::default(),
        };
        let b = body(vec![
            block(0, vec![new_range()], Terminator::Goto(BlockId(1))),
            block(1, vec![borrow_r()], next_call(2)),
            block(2, vec![read_discriminant()], switch_option(4, 3, 5)),
            // Outer body: build the inner iterator, then its loop.
            block(3, vec![offset(new_range())], Terminator::Goto(BlockId(6))),
            block(4, vec![], Terminator::Return),
            block(5, vec![], Terminator::Unreachable),
            block(6, vec![offset(borrow_r())], inner_next(7)),
            block(7, vec![offset(read_discriminant())], inner_switch(1, 8)),
            block(8, vec![], Terminator::Goto(BlockId(6))),
        ]);
        let nest = LoopNest::of(&b).expect("reducible");
        let drivers = |nest: &LoopNest, lp: &NaturalLoop| {
            let inner = lp.contains(8) && !lp.contains(2);
            let (recv, inst, trip) = if inner { (RECV + 10, R + 10, 4) } else { (RECV, R, 10) };
            next_call_driving(&b, nest, lp, |callee| callee == "next")
                .filter(|&(dest, _)| iterator_instance_is_fixed(&b, lp, dest, recv, inst))
                .map(|(_, edge)| LoopDriver { edge, trip })
                .into_iter()
                .collect()
        };
        assert_eq!(nest.block_execution_bound(8, drivers), Some(40));
    }

    #[test]
    fn a_bottom_tested_driver_is_its_back_edge() {
        // `loop { ADD; if flag { continue } else { break } }`: the continue edge
        // bb1 -> bb1 is both the driver edge and the only back edge.
        let b = body(vec![
            block(0, vec![], Terminator::Goto(BlockId(1))),
            block(1, vec![], branch(FLAG, 1, 2)),
            block(2, vec![], Terminator::Return),
        ]);
        let nest = LoopNest::of(&b).expect("reducible");
        let lp = nest.containing(1)[0];
        assert!(nest.crosses_every_iteration(lp, (1, 1)));
        let driver = |_: &LoopNest, _: &NaturalLoop| vec![LoopDriver { edge: (1, 1), trip: 5 }];
        // The block holding the test runs on the exiting iteration too.
        assert_eq!(nest.block_execution_bound(1, driver), Some(6));
    }

    #[test]
    fn a_switch_entered_other_than_from_its_call_bounds_nothing() {
        // The switch (bb1) is the loop header, entered first from bb0 without a
        // `next` call and then from the call at the loop's end: the first
        // `Some` crossing reads a result no `next` produced this entry, so the
        // `Some`s crossed are not the `Some`s yielded (review, 2026-09-29).
        // bb0 | bb1 switch (header) | bb2 Some: ADD | bb3 `&mut r; next` -> bb1
        let b = body(vec![
            block(0, vec![new_range()], Terminator::Goto(BlockId(1))),
            block(1, vec![read_discriminant()], switch_option(4, 2, 5)),
            block(2, vec![], Terminator::Goto(BlockId(3))),
            block(3, vec![borrow_r()], next_call(1)),
            block(4, vec![], Terminator::Return),
            block(5, vec![], Terminator::Unreachable),
        ]);
        assert_eq!(bound(&b, 2), None);
    }

    #[test]
    fn an_irreducible_cfg_has_no_nest() {
        // bb0 branches into both bb1 and bb2, which jump to each other: the cycle
        // has two entries.
        let b = body(vec![
            block(0, vec![], branch(FLAG, 1, 2)),
            block(1, vec![], Terminator::Goto(BlockId(2))),
            block(2, vec![], Terminator::Goto(BlockId(1))),
        ]);
        assert!(LoopNest::of(&b).is_none());
    }
}
