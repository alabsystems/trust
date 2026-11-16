//! Trust: 2026-09-30 — THE COST FIX, PINNED FOR EXACTNESS. Under trust-6606d3bd
//! the fold's stability walk spent >90 CPU-minutes in one `aterm-census` body with
//! a 120 s function budget in force, because no loop of the fold polled the
//! budget. Its whole-body alias scans were asked per statement, per guard, per
//! visited state; a store through another pointer re-resolved that pointer with a
//! nested stability walk at every such point; and a nested verdict was never
//! stored, so pointers whose regions store through one another nested their walks
//! through every ordering of the pointers. The fix answers the same questions
//! from a per-function index, a per-walk resolution cache, an outcome enumeration
//! that decides a store without the nested walk wherever its answer cannot depend
//! on it, and a verdict memo certified by the in-progress marks each verdict
//! consulted; and it bounds every loop of the fold by the ambient per-function
//! budget. Every test here checks an ANSWER against the computation without the
//! fix (the scans, `reference_walk`), and the cost is pinned by deterministic work
//! counters per family: linear, crossed, ladder, and the budget for what is left.

use trust_types::{
    BasicBlock, BlockId, ConstValue, LocalDecl, Operand, Place, Projection, Rvalue, SourceSpan,
    Statement, Terminator, Ty, VerifiableBody, VerifiableFunction,
};

use super::{AliasKind, FoldIndex, local_storage_borrowed_anywhere, slot_alias_scan};

fn usize_ty() -> Ty {
    Ty::Int { width: 64, signed: false }
}

fn raw_mut_usize() -> Ty {
    Ty::RawPtr { mutable: true, pointee: Box::new(usize_ty()) }
}

fn arr_ty() -> Ty {
    Ty::Array { elem: Box::new(usize_ty()), len: 4 }
}

fn assign(place: Place, rvalue: Rvalue) -> Statement {
    Statement::Assign { place, rvalue, span: SourceSpan::default() }
}

fn deref(local: usize) -> Place {
    Place { local, projections: vec![Projection::Deref] }
}

fn indexed(local: usize, index: usize) -> Place {
    Place { local, projections: vec![Projection::Index(index)] }
}

fn function(
    name: &str,
    locals: Vec<Ty>,
    arg_count: usize,
    stmts: Vec<Statement>,
) -> VerifiableFunction {
    VerifiableFunction {
        name: name.to_string(),
        def_path: format!("test::{name}"),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: locals
                .into_iter()
                .enumerate()
                .map(|(index, ty)| LocalDecl { index, ty, name: None })
                .collect(),
            blocks: vec![BasicBlock { id: BlockId(0), stmts, terminator: Terminator::Return }],
            arg_count,
            return_ty: Ty::Unit,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

/// Two raw pointers whose regions each hold a store through the other:
///
/// ```ignore (illustrative)
/// _3 = copy _1;  _4 = copy _2;       // i, j: SSA guards (not parameters)
/// _7 = &raw mut _5[_3];              // p = &raw mut a[i]
/// _8 = &raw mut _6[_4];              // q = &raw mut b[j]
/// (*_8) = 1;                         // in p's region: resolve q, nested
/// (*_7) = 2;                         // in q's region: resolve p — CUT when
///                                    //   q's walk runs inside p's
/// _9 = copy (*_7); _10 = copy (*_8);
/// ```
///
/// So the nested verdict for `q` is computed under a stack holding `p`, and
/// the one for `p` under a stack holding `q`: exactly the verdicts the old memo
/// refused to store, and the ones the certificate must not replay in a stack
/// that answers the cut differently. `borrowed_guards` adds `&_3`/`&_4`, which
/// opens the unattributable-store arm's alias gate for the cut resolution.
fn crossed_stores(borrowed_guards: bool) -> VerifiableFunction {
    let mut locals = vec![Ty::Unit, usize_ty(), usize_ty(), usize_ty(), usize_ty()];
    locals.extend([arr_ty(), arr_ty(), raw_mut_usize(), raw_mut_usize()]);
    locals.extend([usize_ty(), usize_ty()]);
    let mut stmts = vec![
        assign(Place::local(3), Rvalue::Use(Operand::Copy(Place::local(1)))),
        assign(Place::local(4), Rvalue::Use(Operand::Copy(Place::local(2)))),
    ];
    if borrowed_guards {
        locals.extend([
            Ty::Ref { mutable: false, inner: Box::new(usize_ty()) },
            Ty::Ref { mutable: false, inner: Box::new(usize_ty()) },
        ]);
        stmts
            .push(assign(Place::local(11), Rvalue::Ref { mutable: false, place: Place::local(3) }));
        stmts
            .push(assign(Place::local(12), Rvalue::Ref { mutable: false, place: Place::local(4) }));
    }
    stmts.extend([
        assign(Place::local(7), Rvalue::AddressOf(true, indexed(5, 3))),
        assign(Place::local(8), Rvalue::AddressOf(true, indexed(6, 4))),
        assign(deref(8), Rvalue::Use(Operand::Constant(ConstValue::Uint(1, 64)))),
        assign(deref(7), Rvalue::Use(Operand::Constant(ConstValue::Uint(2, 64)))),
        assign(Place::local(9), Rvalue::Use(Operand::Copy(deref(7)))),
        assign(Place::local(10), Rvalue::Use(Operand::Copy(deref(8)))),
    ]);
    function(
        if borrowed_guards { "crossed_stores_borrowed" } else { "crossed_stores" },
        locals,
        2,
        stmts,
    )
}

/// Every place `func` spells, each prefix of each, and every bare local — the
/// candidate guards an alias question can be asked about.
fn candidate_places(func: &VerifiableFunction) -> Vec<Place> {
    fn push_prefixes(out: &mut Vec<Place>, place: &Place) {
        for n in 0..=place.projections.len() {
            out.push(Place { local: place.local, projections: place.projections[..n].to_vec() });
        }
        for proj in &place.projections {
            if let Projection::Index(l) = proj {
                out.push(Place::local(*l));
            }
        }
    }
    fn operand(out: &mut Vec<Place>, op: &Operand) {
        if let Operand::Copy(p) | Operand::Move(p) = op {
            push_prefixes(out, p);
        }
    }
    let mut out: Vec<Place> = (0..func.body.locals.len()).map(Place::local).collect();
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            if let Statement::Assign { place, rvalue, .. } = stmt {
                push_prefixes(&mut out, place);
                match rvalue {
                    Rvalue::Ref { place, .. }
                    | Rvalue::AddressOf(_, place)
                    | Rvalue::Discriminant(place)
                    | Rvalue::Len(place)
                    | Rvalue::CopyForDeref(place) => push_prefixes(&mut out, place),
                    Rvalue::Use(op) | Rvalue::UnaryOp(_, op) | Rvalue::Cast(op, _) => {
                        operand(&mut out, op)
                    }
                    Rvalue::BinaryOp(_, a, b) | Rvalue::CheckedBinaryOp(_, a, b) => {
                        operand(&mut out, a);
                        operand(&mut out, b);
                    }
                    Rvalue::Aggregate(_, ops) => ops.iter().for_each(|op| operand(&mut out, op)),
                    _ => {}
                }
            }
        }
        match &block.terminator {
            Terminator::Call { dest, args, .. } => {
                push_prefixes(&mut out, dest);
                args.iter().for_each(|op| operand(&mut out, op));
            }
            Terminator::Drop { place, .. } => push_prefixes(&mut out, place),
            _ => {}
        }
    }
    out.sort_by(|a, b| format!("{a:?}").cmp(&format!("{b:?}")));
    out.dedup();
    out
}

/// The real-compiler MIR this crate's integration tests already read.
fn fixtures() -> Vec<VerifiableFunction> {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures");
    let mut paths: Vec<_> = std::fs::read_dir(&dir)
        .expect("tests/fixtures is readable")
        .map(|e| e.expect("dir entry").path())
        .filter(|p| p.extension().and_then(|e| e.to_str()) == Some("json"))
        .collect();
    paths.sort();
    paths
        .iter()
        .filter_map(|p| {
            serde_json::from_str::<VerifiableFunction>(&std::fs::read_to_string(p).ok()?).ok()
        })
        .collect()
}

fn assert_index_agrees(func: &VerifiableFunction) -> usize {
    let index = FoldIndex::build(func);
    let mut asked = 0;
    for g in candidate_places(func) {
        for kind in [AliasKind::Any, AliasKind::WriteCapable] {
            asked += 1;
            assert_eq!(
                index.slot_aliased(&g, kind),
                slot_alias_scan(func, &g, kind),
                "{}: the index and the scan disagree on {g:?}",
                func.def_path
            );
            // And again: the second answer comes from the index's own cache.
            assert_eq!(index.slot_aliased(&g, kind), slot_alias_scan(func, &g, kind));
        }
    }
    for l in 0..func.body.locals.len() {
        asked += 1;
        assert_eq!(
            index.storage_borrowed.contains(&l),
            local_storage_borrowed_anywhere(func, l),
            "{}: the index and the scan disagree on the storage of _{l}",
            func.def_path
        );
    }
    asked
}

/// The index answers every alias question the walk asks exactly as the
/// whole-body scans it replaced — on the hand-built bodies and on every
/// real-MIR fixture of this crate.
#[test]
fn index_agrees_with_the_scans() {
    assert_index_agrees(&crossed_stores(false));
    assert_index_agrees(&crossed_stores(true));
    let fixtures = fixtures();
    // ANTI-VACUITY: the fixture directory holds hundreds of real bodies; a
    // deserialization change that silently skipped them would leave only the
    // two hand-built rows above.
    assert!(fixtures.len() >= 300, "only {} fixtures deserialized", fixtures.len());
    let with_borrows = fixtures.iter().filter(|f| !FoldIndex::build(f).borrows.is_empty()).count();
    assert!(with_borrows >= 100, "only {with_borrows} fixtures borrow anything");
    let asked: usize = fixtures.iter().map(assert_index_agrees).sum();
    assert!(asked > 10_000, "only {asked} questions compared");
}

/// `resolve_referent` of every local (in `order`) and `canonicalize_deref` of
/// every place in `places`, inside a fresh VC-gen scope when `scoped` (the
/// fold index, the per-function taint and the certified verdict memo are then
/// shared across every question), with every memo inert otherwise.
fn all_resolutions(
    func: &VerifiableFunction,
    order: &[usize],
    places: &[Place],
    scoped: bool,
) -> (Vec<(usize, Option<Place>)>, Vec<Place>) {
    let _scope = scoped.then(super::super::gen_work::enter);
    let mut locals: Vec<(usize, Option<Place>)> =
        order.iter().map(|&l| (l, super::super::resolve_referent(func, l, 16))).collect();
    locals.sort_by_key(|(l, _)| *l);
    let canonical =
        places.iter().map(|p| super::super::canonicalize_deref(func, p.clone(), 16)).collect();
    (locals, canonical)
}

fn deref_places(func: &VerifiableFunction) -> Vec<Place> {
    candidate_places(func)
        .into_iter()
        .filter(|p| matches!(p.projections.first(), Some(Projection::Deref)))
        .collect()
}

/// THE EXACTNESS PIN. Every pointer local's resolution and every deref place's
/// canonical form, computed with the fold's shortcuts — the per-walk
/// resolution cache, the outcome enumeration, the known-bit skip — inside a
/// VC-gen scope where the certified verdict memo serves nested walks too,
/// asked in two orders, and again outside any scope, equals the REFERENCE:
/// outside any scope (no memo) with the shortcuts off, every nested walk run
/// from scratch as before 2026-09-30. Over every real-MIR fixture that stores
/// through a pointer and every synthetic family the cost tests below use.
#[test]
fn the_fold_shortcuts_and_memo_change_no_resolution() {
    let mut bodies = vec![crossed_stores(false), crossed_stores(true)];
    for escaped in [false, true] {
        bodies.push(store_chain_with(2, &[1], 8, escaped));
        bodies.push(store_chain_with(5, &[0, 1, 2, 3, 4], 1, escaped));
        bodies.push(store_chain_with(4, &[0, 2, 3], 2, escaped));
        bodies.push(store_ladder(6, escaped));
    }
    // The two bodies whose nested verdicts differ by stack (2026-10-02): the
    // certificate is what keeps them exact (`a_nested_verdict_replays_…` below).
    bodies.push(asymmetric_pair());
    bodies.push(cut_through_a_third());
    bodies.extend(fixtures().into_iter().filter(|f| {
        f.body.blocks.iter().any(|b| {
            b.stmts.iter().any(|s| {
                matches!(s, Statement::Assign { place, .. }
                    if matches!(place.projections.first(), Some(Projection::Deref)))
            })
        })
    }));
    // ANTI-VACUITY: bodies that store through a pointer are the ones with
    // nested walks at all.
    assert!(bodies.len() >= 40, "only {} bodies store through a pointer", bodies.len());
    let (mut hits, mut decided, mut nested_hits) = (0, 0, 0);
    for func in &bodies {
        let n = func.body.locals.len();
        let forward: Vec<usize> = (0..n).collect();
        let places = deref_places(func);
        let reference = super::reference_walk(|| all_resolutions(func, &forward, &places, false));
        for order in [forward.clone(), (0..n).rev().collect()] {
            crate::fn_memo::reset_analysis_memo_stats();
            let got = all_resolutions(func, &order, &places, true);
            let stats = crate::fn_memo::analysis_memo_stats();
            assert_eq!(got.0, reference.0, "{}: a resolution changed", func.def_path);
            assert_eq!(got.1, reference.1, "{}: a canonical form changed", func.def_path);
            hits += stats.fold_memo_hits;
            decided += stats.fold_outcome_decisions;
            if func.def_path.starts_with("test::store_ladder") {
                nested_hits += stats.fold_memo_hits;
            }
        }
        assert_eq!(
            all_resolutions(func, &forward, &places, false),
            reference,
            "{}: the shortcuts changed an answer outside a scope",
            func.def_path
        );
    }
    assert!(hits > 0, "ANTI-VACUITY: the memo never served a verdict");
    assert!(nested_hits > 0, "ANTI-VACUITY: the memo never served a ladder verdict");
    assert!(decided > 0, "ANTI-VACUITY: no store was decided by its outcomes");
}

/// A walk that meets a tripped ambient budget REFUSES the fold — the same
/// opaque answer an in-progress cut gives — and the refusal is not stored:
/// the same question asked again in the same VC-gen scope, under no budget,
/// gets the full answer back.
#[test]
fn a_tripped_budget_refuses_the_fold_and_is_not_remembered() {
    let func = crossed_stores(false);
    let want = Some(indexed(5, 3));
    assert_eq!(
        super::super::resolve_referent(&func, 7, 16),
        want,
        "control: with no budget `p` folds to `_5[_3]`"
    );
    let _scope = super::super::gen_work::enter();
    {
        // One step: the resolution's own poll spends it, and the stability
        // walk's poll trips.
        let _budget = trust_types::verify_budget::VerifyBudgetGuard::install(None, 1);
        assert_eq!(
            super::super::resolve_referent(&func, 7, 16),
            None,
            "a tripped budget must refuse the fold, never admit it"
        );
        assert!(trust_types::verify_budget::exhausted_readonly());
    }
    assert_eq!(
        super::super::resolve_referent(&func, 7, 16),
        want,
        "the budget refusal leaked into the memo"
    );
}

fn opaque_call(arg: usize, dest: usize, target: usize) -> Terminator {
    Terminator::Call {
        unwind: trust_types::UnwindEdge::Unreachable,
        is_unsafe_sig: false,
        callee_identity: None,
        callee_key: None,
        is_foreign: false,
        func: "test::opaque".to_string(),
        args: vec![Operand::Move(Place::local(arg))],
        dest: Place::local(dest),
        target: Some(BlockId(target)),
        span: SourceSpan::default(),
        atomic: None,
    }
}

/// The locals of the chain families: `_0` unit, `_1` the array, `_2` a `usize`
/// parameter, then `k` guards, `k` raw pointers, `k` read slots, `k` `&mut`
/// borrows of the guards and one unit call destination (the last two used
/// only by an `escaped` body).
struct Layout {
    k: usize,
}

impl Layout {
    fn guard(&self, m: usize) -> usize {
        3 + m
    }
    fn ptr(&self, m: usize) -> usize {
        3 + self.k + m
    }
    fn read(&self, m: usize) -> usize {
        3 + 2 * self.k + m
    }
    fn borrow(&self, m: usize) -> usize {
        3 + 3 * self.k + m
    }
    fn call_dest(&self) -> usize {
        3 + 4 * self.k
    }
    fn locals(&self) -> Vec<Ty> {
        let k = self.k;
        let mut locals = vec![Ty::Unit, arr_ty(), usize_ty()];
        locals.extend((0..k).map(|_| usize_ty()));
        locals.extend((0..k).map(|_| raw_mut_usize()));
        locals.extend((0..k).map(|_| usize_ty()));
        locals.extend((0..k).map(|_| Ty::Ref { mutable: true, inner: Box::new(usize_ty()) }));
        locals.push(Ty::Unit);
        locals
    }
    fn bind_pointer(&self, m: usize) -> Statement {
        assign(Place::local(self.ptr(m)), Rvalue::AddressOf(true, indexed(1, self.guard(m))))
    }
    fn store_through(&self, m: usize) -> Statement {
        assign(deref(self.ptr(m)), Rvalue::Use(Operand::Constant(ConstValue::Uint(m as u128, 64))))
    }
    fn read_through(&self, m: usize) -> Statement {
        assign(Place::local(self.read(m)), Rvalue::Use(Operand::Copy(deref(self.ptr(m)))))
    }
}

/// The entry of a chain family: every guard bound (`g_m = copy _2`) and — when
/// `escaped` — every guard's storage `&mut`-borrowed and the borrow handed to
/// an opaque call, one block per call. The last block `Goto`s the next id.
///
/// ESCAPED is the shape no outcome enumeration can decide: every guard is then
/// ALIASED and its provenance taint ESCAPED, so a store through a pointer this
/// walk cannot resolve may rebind it (`unattributable_store_rebinds`) while the
/// same store attributed to its folded referent — an element of `_1` — does
/// not. The answer then depends on the other pointer's own stability. The calls
/// run before any pointer is taken, so no region contains one.
fn chain_entry(l: &Layout, escaped: bool) -> Vec<BasicBlock> {
    let mut stmts: Vec<Statement> = (0..l.k)
        .map(|m| assign(Place::local(l.guard(m)), Rvalue::Use(Operand::Copy(Place::local(2)))))
        .collect();
    let mut blocks = Vec::new();
    if escaped {
        for m in 0..l.k {
            stmts.push(assign(
                Place::local(l.borrow(m)),
                Rvalue::Ref { mutable: true, place: Place::local(l.guard(m)) },
            ));
            let id = blocks.len();
            blocks.push(BasicBlock {
                id: BlockId(id),
                stmts: std::mem::take(&mut stmts),
                terminator: opaque_call(l.borrow(m), l.call_dest(), id + 1),
            });
        }
    }
    let id = blocks.len();
    blocks.push(BasicBlock {
        id: BlockId(id),
        stmts,
        terminator: Terminator::Goto(BlockId(id + 1)),
    });
    blocks
}

fn chain_function(name: String, l: &Layout, blocks: Vec<BasicBlock>) -> VerifiableFunction {
    // `_1` (the array) and `_2` are the parameters.
    let mut func = function(&name, l.locals(), 2, vec![]);
    func.body.blocks = blocks;
    func
}

/// `k` raw pointers `p_m = &raw mut _1[g_m]` into one array, each guard `g_m` a
/// non-parameter local (so no guard is filtered out), then `rounds` passes of
/// `(*p_m) = m` over every pointer in `stored`, one block per store (a `Goto`
/// chain), then a read through every pointer.
///
/// With `k == 2` and only `p_1` stored through, `p_0`'s region holds `n`
/// stores through ANOTHER pointer and nothing else: the linear family. With
/// every pointer stored through, each pointer's region holds stores through
/// all the others: the crossed family, whose nested walks recursed through
/// every ordering of the pointers.
fn store_chain(k: usize, stored: &[usize], rounds: usize) -> VerifiableFunction {
    store_chain_with(k, stored, rounds, false)
}

fn store_chain_with(
    k: usize,
    stored: &[usize],
    rounds: usize,
    escaped: bool,
) -> VerifiableFunction {
    let l = Layout { k };
    let mut blocks = chain_entry(&l, escaped);
    let id = blocks.len();
    blocks.push(BasicBlock {
        id: BlockId(id),
        stmts: (0..k).map(|m| l.bind_pointer(m)).collect(),
        terminator: Terminator::Goto(BlockId(id + 1)),
    });
    for _ in 0..rounds {
        for &m in stored {
            let id = blocks.len();
            blocks.push(BasicBlock {
                id: BlockId(id),
                stmts: vec![l.store_through(m)],
                terminator: Terminator::Goto(BlockId(id + 1)),
            });
        }
    }
    let id = blocks.len();
    blocks.push(BasicBlock {
        id: BlockId(id),
        stmts: (0..k).map(|m| l.read_through(m)).collect(),
        terminator: Terminator::Return,
    });
    let name = format!(
        "store_chain_{k}_{}_{rounds}{}",
        stored.len(),
        if escaped { "_escaped" } else { "" }
    );
    chain_function(name, &l, blocks)
}

/// THE LADDER: `p_m = &raw mut _1[g_m]; (*p_m) = m;` for `m` in order, then a
/// read through every pointer. `p_m`'s region holds the stores through `p_m`
/// and through every LATER pointer, so resolving `p_0` resolves `p_1`, which
/// resolves `p_2`, … — no cut anywhere, and every fold stands. With `escaped`
/// guards no store is decided by its outcomes, and before the certified memo
/// every enclosing walk re-ran every later pointer's walk: `2^(k-1)` walks.
fn store_ladder(k: usize, escaped: bool) -> VerifiableFunction {
    let l = Layout { k };
    let mut blocks = chain_entry(&l, escaped);
    for m in 0..k {
        let id = blocks.len();
        blocks.push(BasicBlock {
            id: BlockId(id),
            stmts: vec![l.bind_pointer(m), l.store_through(m)],
            terminator: Terminator::Goto(BlockId(id + 1)),
        });
    }
    let id = blocks.len();
    blocks.push(BasicBlock {
        id: BlockId(id),
        stmts: (0..k).map(|m| l.read_through(m)).collect(),
        terminator: Terminator::Return,
    });
    chain_function(format!("store_ladder_{k}{}", if escaped { "_escaped" } else { "" }), &l, blocks)
}

/// Deterministic fold work for resolving `local`, fresh VC-gen scope.
struct Work {
    resolved: Option<Place>,
    /// States popped plus statements examined.
    units: u64,
    walks: u64,
    nested: u64,
    decided: u64,
}

fn fold_work(func: &VerifiableFunction, local: usize) -> Work {
    let _scope = super::super::gen_work::enter();
    crate::fn_memo::reset_analysis_memo_stats();
    let resolved = super::super::resolve_referent(func, local, 16);
    let stats = crate::fn_memo::analysis_memo_stats();
    Work {
        resolved,
        units: stats.fold_walk_steps + stats.fold_stmt_visits,
        walks: stats.fold_walks,
        nested: stats.fold_nested_resolutions,
        decided: stats.fold_outcome_decisions,
    }
}

/// THE LINEAR PIN. A pointer whose region holds `n` stores through another
/// pointer costs `O(n)` fold work. Unescaped, every one of those stores is
/// decided by the other pointer's outcomes and nothing nested runs at all;
/// escaped, the other pointer is resolved ONCE per walk (it used to be
/// re-resolved — a whole nested stability walk — at every store, which made
/// this family `O(n²)`). Each store's alias questions are answered from the
/// per-function index (they used to be whole-body scans). Doubling the body
/// must at most double the work, up to a constant.
#[test]
fn fold_work_is_linear_in_the_body() {
    for escaped in [false, true] {
        let p0 = Layout { k: 2 }.ptr(0);
        let mut last: Option<(usize, u64)> = None;
        for n in [64usize, 128, 256, 512] {
            let func = store_chain_with(2, &[1], n, escaped);
            let work = fold_work(&func, p0);
            assert_eq!(
                work.resolved,
                Some(indexed(1, 3)),
                "control: nothing in the region rebinds `p_0`'s guard, so it folds"
            );
            if escaped {
                assert_eq!(work.nested, 1, "n = {n}: resolved once per walk");
            } else {
                assert_eq!(work.nested, 0, "n = {n}: decided by the outcomes");
                assert!(work.decided >= 1, "ANTI-VACUITY: n = {n}: no store decided");
            }
            // ANTI-VACUITY: the walk really crossed every store.
            assert!(work.units >= n as u64, "n = {n}: only {} units", work.units);
            if let Some((m, prev)) = last {
                assert!(
                    work.units * (m as u64) <= prev * (n as u64) + 64 * (n as u64),
                    "fold work grew super-linearly: {prev} at n = {m}, {} at n = {n}",
                    work.units
                );
            }
            last = Some((n, work.units));
        }
    }
}

/// THE CROSSED PIN. Every pointer stored through in every other's region —
/// the shape of the `aterm-census` loop bodies that ran for hours (`index[v]`,
/// `low[v]`, `on_stack[v]` written through reborrowed `Vec` buffers). Each
/// store's rebinding answer is the same whatever the other pointer resolves
/// to, so the outcome enumeration decides it and one walk decides the fold:
/// the work is linear in `k` where it was `(k-1)!` nested walks.
#[test]
fn the_crossed_family_costs_one_walk() {
    let all = |k: usize| (0..k).collect::<Vec<_>>();
    // Control: the reference (every nested walk run) agrees on a small one.
    let small = store_chain(4, &all(4), 1);
    let p0 = Layout { k: 4 }.ptr(0);
    assert_eq!(
        super::reference_walk(|| super::super::resolve_referent(&small, p0, 16)),
        Some(indexed(1, 3))
    );
    let mut last: Option<(usize, u64)> = None;
    for k in [4usize, 8, 16, 32] {
        let func = store_chain(k, &all(k), 1);
        let work = fold_work(&func, Layout { k }.ptr(0));
        assert_eq!(work.resolved, Some(indexed(1, 3)), "k = {k}: the fold stands");
        assert_eq!(work.walks, 1, "k = {k}: only `p_0`'s own walk runs");
        assert_eq!(work.nested, 0, "k = {k}: no nested resolution runs");
        assert!(work.decided >= (k - 1) as u64, "k = {k}: every other store decided");
        if let Some((m, prev)) = last {
            // `k` stores, each over `k` reads' worth of statements: at most
            // quadratic in `k`, never factorial.
            assert!(
                work.units * (m * m) as u64 <= prev * (k * k) as u64 + 64 * (k * k) as u64,
                "k = {k}: {} units after {prev} at k = {m}",
                work.units
            );
        }
        last = Some((k, work.units));
    }
}

/// THE MEMO PIN. The escaped ladder: every store's answer depends on the later
/// pointer's stability, so each walk resolves the next pointer for real — and
/// the next pointer's verdict, computed nested, is certified by the locals it
/// consulted (itself and every later pointer, none in progress). Every
/// enclosing walk's stack satisfies that certificate, so each pointer is
/// walked ONCE: `k` walks, where storing nothing for a nested walk cost
/// `2^(k-1)`.
#[test]
fn a_ladder_of_pointers_walks_each_pointer_once() {
    let small = store_ladder(6, true);
    let p0 = Layout { k: 6 }.ptr(0);
    assert_eq!(
        super::reference_walk(|| super::super::resolve_referent(&small, p0, 16)),
        Some(indexed(1, 3)),
        "control: the reference folds the small ladder"
    );
    for k in [6usize, 12, 24] {
        let func = store_ladder(k, true);
        let work = fold_work(&func, Layout { k }.ptr(0));
        assert_eq!(work.resolved, Some(indexed(1, 3)), "k = {k}: the fold stands");
        assert!(work.walks <= k as u64, "k = {k}: {} walks for {k} pointers", work.walks);
        assert!(
            work.nested >= (k - 1) as u64,
            "ANTI-VACUITY: k = {k}: the escaped ladder must resolve for real"
        );
    }
}

/// THE BUDGET PIN. The fold still has families it cannot make cheap — ones
/// whose stores' answers depend on the other pointers' stability AND whose
/// verdicts depend on which pointers are already in progress, so no
/// certificate is shared across orderings — and the ambient per-function
/// budget is what bounds them. Pinned on the escaped ladder, which folds with
/// no budget: under a budget far smaller than its work the resolution returns,
/// REFUSES (the opaque answer, never the fold), and every state it popped was
/// counted against the budget.
#[test]
fn the_fold_is_bounded_by_the_ambient_budget() {
    let k = 24;
    let func = store_ladder(k, true);
    let p0 = Layout { k }.ptr(0);
    let unbudgeted = fold_work(&func, p0);
    assert_eq!(unbudgeted.resolved, Some(indexed(1, 3)), "control: it folds unbudgeted");
    const STEPS: u64 = 64;
    assert!(
        unbudgeted.units > 4 * STEPS,
        "ANTI-VACUITY: the ladder must outgrow the {STEPS}-step budget"
    );
    let _scope = super::super::gen_work::enter();
    crate::fn_memo::reset_analysis_memo_stats();
    let _budget = trust_types::verify_budget::VerifyBudgetGuard::install(None, STEPS);
    let resolved = super::super::resolve_referent(&func, p0, 16);
    assert!(trust_types::verify_budget::exhausted_readonly(), "ANTI-VACUITY: no trip");
    assert_eq!(resolved, None, "a tripped budget must refuse the fold, never admit it");
    let stats = crate::fn_memo::analysis_memo_stats();
    assert!(
        stats.fold_walk_steps <= STEPS,
        "the fold popped {} states under a {STEPS}-step budget",
        stats.fold_walk_steps
    );
}

// ---------------------------------------------------------------------------
// Trust: 2026-10-02 — THE CERTIFICATE, THE CAP AND THE TRIP FILTERS, PINNED.
//
// An independent review planted 15 defects in the fold; seven passed every test
// above. Four of those survived two randomized differentials as well: a stored
// verdict replayed whatever its stack certificate said, a nested walk's
// consultations left out of the enclosing walk's certificate, an outcome set cut
// short at the cap reported as complete, and an outcome set enumerated across a
// budget trip trusted. The other three: a verdict, or a slot taint, computed
// after a trip kept for the function, and a verdict memo keyed without the guard
// list. Each test below fails under at least one of the seven.
// ---------------------------------------------------------------------------

/// An `escaped` chain-family entry for `k` pointers (every guard `&mut`-borrowed
/// and handed to an opaque call, so a store this walk cannot attribute may
/// rebind any guard), then ONE block of `stmts` ending in `Return`.
fn escaped_body(
    name: &str,
    k: usize,
    stmts: impl FnOnce(&Layout) -> Vec<Statement>,
) -> VerifiableFunction {
    let l = Layout { k };
    let mut blocks = chain_entry(&l, true);
    let id = blocks.len();
    blocks.push(BasicBlock { id: BlockId(id), stmts: stmts(&l), terminator: Terminator::Return });
    chain_function(name.to_string(), &l, blocks)
}

/// Two pointers, `p = p_0` and `q = p_1`, whose nested verdicts DEPEND ON THE
/// STACK:
///
/// ```ignore (illustrative)
/// p = &raw mut a[g0];  q = &raw mut a[g1];
/// (*p) = 0;            // in q's region: a store through p (p's last mention)
/// (*q) = 1;            // in p's region, after p's last mention: p asks q
/// r1 = copy (*q);
/// ```
///
/// Resolving `p` walks `p`, which asks `q`; `q`'s walk, nested, asks `p` — in
/// progress, so CUT, opaque — and the escaped guard makes that store rebind `g1`
/// before `q`'s next mention: under `p`, `q` is UNSTABLE. Asked at top level,
/// `q`'s walk resolves `p` for real (with `q` the cut, which `p` survives: its
/// last mention is before the store through `q`), so `q` FOLDS. Resolving `p`
/// leaves `q`'s `false` in the memo with the certificate `cut = [p]`; replayed in
/// the empty stack, it would refuse a fold the computation admits.
fn asymmetric_pair() -> VerifiableFunction {
    escaped_body("asymmetric_pair", 2, |l| {
        vec![
            l.bind_pointer(0),
            l.bind_pointer(1),
            l.store_through(0),
            l.store_through(1),
            l.read_through(1),
        ]
    })
}

/// Three pointers, `p = p_0`, `q = p_1`, `r = p_2`, where `q`'s dependence on the
/// stack runs THROUGH a nested walk:
///
/// ```ignore (illustrative)
/// r = &raw mut a[g2];  q = &raw mut a[g1];
/// (*r) = 2;            // in q's region: q asks r
/// r1 = copy (*q);      // q's mention
/// p = &raw mut a[g0];
/// (*p) = 0;            // in r's region: r asks p (p's last mention)
/// r2 = copy (*r);      // r's mention
/// (*q) = 1;            // in p's region, after p's last mention: p asks q
/// ```
///
/// Resolving `p` nests `p -> q -> r`, and `r` is cut by `p`: `r`, then `q`, are
/// unstable under `p`. `q`'s own walk never asks about `p` — only the walk of `r`
/// nested inside it does — so `q`'s certificate names `p` only if a nested walk's
/// consultations reach the enclosing walk's. Without that, `q`'s `false` is stored
/// with an EMPTY cut and replays at top level, where `q` folds.
fn cut_through_a_third() -> VerifiableFunction {
    escaped_body("cut_through_a_third", 3, |l| {
        vec![
            l.bind_pointer(2),
            l.bind_pointer(1),
            l.store_through(2),
            l.read_through(1),
            l.bind_pointer(0),
            l.store_through(0),
            l.read_through(2),
            l.store_through(1),
        ]
    })
}

/// THE CERTIFICATE PIN. A nested verdict computed under an in-progress cut IS
/// stored (that is what walks the escaped ladder once per pointer), and it is
/// replayed ONLY in a stack that answers every in-progress question it asked —
/// itself or in a walk nested inside it — the same way. On the two bodies above,
/// `p_1`'s verdict under `p_0`'s cut (`false`) differs from its top-level verdict
/// (`true`): resolving `p_0` first stores the cut verdict, and `p_1`, asked next
/// at top level in the same scope, must still fold.
#[test]
fn a_nested_verdict_replays_only_where_its_consultations_answer_alike() {
    for (func, k) in [(asymmetric_pair(), 2usize), (cut_through_a_third(), 3)] {
        let l = Layout { k };
        let want: Vec<Option<Place>> = (0..k).map(|m| Some(indexed(1, l.guard(m)))).collect();
        let resolve_all = || -> Vec<Option<Place>> {
            (0..k).map(|m| super::super::resolve_referent(&func, l.ptr(m), 16)).collect()
        };
        assert_eq!(
            super::reference_walk(resolve_all),
            want,
            "{}: control: the reference folds every pointer at top level",
            func.def_path
        );
        let _scope = super::super::gen_work::enter();
        assert_eq!(super::super::resolve_referent(&func, l.ptr(0), 16), want[0]);
        let q_guards = [Place::local(l.guard(1))];
        let stored = crate::havoc_memo::fold_stable(
            &func,
            l.ptr(1),
            &indexed(1, l.guard(1)),
            &q_guards,
            |entry| !entry.verdict && entry.cut == [l.ptr(0)],
        )
        .unwrap_or_else(|| {
            panic!("ANTI-VACUITY: {}: no verdict for p_1 stored under p_0's cut", func.def_path)
        });
        assert!(
            stored.consulted.contains(&l.ptr(0)),
            "{}: p_1's certificate must name p_0, whose in-progress mark decided it",
            func.def_path
        );
        assert_eq!(
            resolve_all(),
            want,
            "{}: a verdict computed under p_0's cut was replayed outside it",
            func.def_path
        );
    }
}

/// THE CAP PIN. [`super::outcomes`] lists EVERY choice sequence's value, or
/// reports nothing. A set cut short at the cap may lack the one value that
/// disagrees, so "every listed value agrees" would decide a store the real
/// resolution decides the other way.
#[test]
fn the_outcome_enumeration_lists_every_sequence_or_nothing() {
    use super::{MAX_OUTCOME_RUNS, choose, enumerating, outcomes};
    for k in 0..=5usize {
        let got = outcomes(|| (0..k).map(|_| choose()).collect::<Vec<bool>>())
            .unwrap_or_else(|| panic!("k = {k}: 2^{k} sequences are within the cap"));
        let mut distinct = got.clone();
        distinct.sort();
        distinct.dedup();
        assert_eq!((got.len(), distinct.len()), (1 << k, 1 << k), "k = {k}: every sequence once");
        assert!(!enumerating(), "k = {k}: the enumeration outlived its call");
    }
    assert_eq!(MAX_OUTCOME_RUNS, 1 << 5, "the k = 5 row must sit exactly at the cap");
    // One choice past the cap. Depth-first with `false` first, the first 32 runs
    // all take `false` at the first choice and answer `false`; only a later run
    // answers `true`, so a truncated set would read as "always false".
    let all_true = outcomes(|| (0..6).map(|_| choose()).fold(true, |acc, c| acc & c));
    assert_eq!(all_true, None, "a set truncated at the cap was reported as complete");
    assert_eq!(outcomes(|| (0..6).map(|_| choose()).collect::<Vec<bool>>()), None);
    // A choice that exists on one branch only: the tree need not be full.
    let ragged = outcomes(|| if choose() { Some(choose()) } else { None });
    assert_eq!(ragged, Some(vec![None, Some(false), Some(true)]));
    assert!(!enumerating());
}

/// THE TRIP-FILTER PINS for the two caches a walk reads that are not the verdict
/// memo. After the ambient budget trips, every answer is a refusal and not the
/// function's answer: the walk's outcome set (a set enumerated across a trip may
/// lack the real value) must report nothing, and the slot taint must fail closed
/// (`escaped`) WITHOUT being kept for the function. The verdict memo's filter is
/// pinned by the sweep below and by `a_tripped_budget_refuses_the_fold_and_…`.
#[test]
fn an_outcome_set_or_a_taint_computed_after_a_trip_is_not_kept() {
    use trust_types::verify_budget::{VerifyBudgetGuard, exhausted_readonly};
    // The walk's outcome set, for `q` (`_8`) of the crossed pair.
    let func = crossed_stores(false);
    let control = super::TaintCache::new(&func).outcomes(8);
    assert_eq!(
        control.as_deref().map(<[_]>::len),
        Some(2),
        "control: `q` folds or does not: {control:?}"
    );
    {
        // A step budget of 0 is spent before the first poll.
        let _budget = VerifyBudgetGuard::install(None, 0);
        assert!(exhausted_readonly());
        assert!(
            super::TaintCache::new(&func).outcomes(8).is_none(),
            "an outcome set enumerated after a trip must not be reported"
        );
    }
    // The function's slot taint, for the shared-borrowed guard `_3`.
    let func = crossed_stores(true);
    let guard = Place::local(3);
    let index = FoldIndex::build(&func);
    {
        let _budget = VerifyBudgetGuard::install(None, 0);
        assert!(index.taint(&func, &guard).escaped, "a taint computed after a trip fails closed");
    }
    let taint = index.taint(&func, &guard);
    assert!(
        !taint.escaped && taint.tainted.contains(&11),
        "a taint computed after a trip was kept for the function: escaped = {}, tainted = {:?}",
        taint.escaped,
        taint.tainted
    );
}

/// THE MEMO-KEY PIN. A verdict is a function of the guard list the walk used,
/// so the memo keys on it: `extra` guards (those of a referent read OUT OF this
/// pointer's pointee) make a different question of the same `(local, referent)`.
///
/// ```ignore (illustrative)
/// g = copy _2;  h = copy _2;
/// p = &raw mut a[g];
/// h = const 9;          // rebinds `h`, not `g`
/// r = copy (*p);        // p's mention
/// ```
#[test]
fn the_verdict_memo_keys_on_the_guard_list() {
    let locals =
        vec![Ty::Unit, arr_ty(), usize_ty(), usize_ty(), usize_ty(), raw_mut_usize(), usize_ty()];
    let stmts = vec![
        assign(Place::local(3), Rvalue::Use(Operand::Copy(Place::local(2)))),
        assign(Place::local(4), Rvalue::Use(Operand::Copy(Place::local(2)))),
        assign(Place::local(5), Rvalue::AddressOf(true, indexed(1, 3))),
        assign(Place::local(4), Rvalue::Use(Operand::Constant(ConstValue::Uint(9, 64)))),
        assign(Place::local(6), Rvalue::Use(Operand::Copy(deref(5)))),
    ];
    let func = function("extra_guard_rebound", locals, 2, stmts);
    let referent = indexed(1, 3);
    let widened = [Place::local(4)];
    let ask = |extra: &[Place]| super::is_stable(&func, 5, &referent, extra);
    assert_eq!(
        super::reference_walk(|| (ask(&[]), ask(&widened))),
        (true, false),
        "control: `h`'s rebinding refuses the widened question only"
    );
    for widened_first in [false, true] {
        let _scope = super::super::gen_work::enter();
        let answers = if widened_first {
            let widened_answer = ask(&widened);
            (ask(&[]), widened_answer)
        } else {
            let bare = ask(&[]);
            (bare, ask(&widened))
        };
        assert_eq!(
            answers,
            (true, false),
            "widened question asked first: {widened_first}: one verdict answered the other"
        );
    }
}

/// One pointer, one store this walk cannot attribute (through the raw-pointer
/// PARAMETER `_3`) and a shared borrow of the guard: the store is decided by the
/// guard's provenance taint, which leaves `_3` clean, so the fold stands —
/// exactly as long as the taint is the real one.
///
/// ```ignore (illustrative)
/// g = copy _2;  b = &g;  p = &raw mut a[g];  (*_3) = 7;  r = copy (*p);
/// ```
fn unattributable_store() -> VerifiableFunction {
    let locals = vec![
        Ty::Unit,
        arr_ty(),
        usize_ty(),
        raw_mut_usize(),
        usize_ty(),
        Ty::Ref { mutable: false, inner: Box::new(usize_ty()) },
        raw_mut_usize(),
        usize_ty(),
    ];
    let stmts = vec![
        assign(Place::local(4), Rvalue::Use(Operand::Copy(Place::local(2)))),
        assign(Place::local(5), Rvalue::Ref { mutable: false, place: Place::local(4) }),
        assign(Place::local(6), Rvalue::AddressOf(true, indexed(1, 4))),
        assign(deref(3), Rvalue::Use(Operand::Constant(ConstValue::Uint(7, 64)))),
        assign(Place::local(7), Rvalue::Use(Operand::Copy(deref(6)))),
    ];
    function("unattributable_store", locals, 3, stmts)
}

/// THE SWEEP. For every step budget from 1 until one is large enough not to trip:
/// every resolution under the budget is the unbudgeted one or the refusal (`None`)
/// — never another fold, never a fold the unbudgeted run refuses — and asking
/// everything again in the SAME VC-gen scope once the budget is lifted gives the
/// unbudgeted answers exactly, whichever cache the tripped run touched (the
/// verdict memo, the per-function slot taint, the fold index). The budgets step
/// through every poll the fold makes on these bodies, so every poll site is
/// tripped by one of them.
#[test]
fn every_budget_trip_refuses_and_leaves_nothing_behind() {
    use trust_types::verify_budget::{VerifyBudgetGuard, exhausted_readonly};
    let bodies = [
        unattributable_store(),
        crossed_stores(true),
        store_chain_with(2, &[0, 1], 1, true),
        asymmetric_pair(),
        cut_through_a_third(),
        store_ladder(4, true),
    ];
    for func in &bodies {
        let n = func.body.locals.len();
        let resolve_all = || -> Vec<Option<Place>> {
            (0..n).map(|l| super::super::resolve_referent(func, l, 16)).collect()
        };
        let want = {
            let _scope = super::super::gen_work::enter();
            resolve_all()
        };
        assert!(
            want.iter().filter(|w| w.is_some()).count() >= 2,
            "ANTI-VACUITY: {}: too little folds: {want:?}",
            func.def_path
        );
        let mut trips = 0u64;
        for steps in 1u64.. {
            assert!(steps < 1_000_000, "{}: no budget was large enough", func.def_path);
            let _scope = super::super::gen_work::enter();
            let (budgeted, exhausted) = {
                let _budget = VerifyBudgetGuard::install(None, steps);
                (resolve_all(), exhausted_readonly())
            };
            for (l, (got, w)) in budgeted.iter().zip(&want).enumerate() {
                assert!(
                    got.is_none() || got == w,
                    "{}: {steps} steps: _{l} resolved to {got:?} under the budget, {w:?} without",
                    func.def_path
                );
            }
            assert_eq!(
                resolve_all(),
                want,
                "{}: {steps} steps: an answer computed across the trip was kept in the scope",
                func.def_path
            );
            if !exhausted {
                break;
            }
            trips += 1;
        }
        assert!(trips >= 8, "ANTI-VACUITY: {}: only {trips} budgets tripped", func.def_path);
    }
}
