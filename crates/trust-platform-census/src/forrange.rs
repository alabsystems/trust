//! Two passes over a root's translated bodies.
//!
//! * [`taint`] (X1): which variables may hold an untracked value
//!   (`Expr::Opaque`, through assignments and call arguments). A guard that
//!   reads one becomes `Cond::Nondet` (both arms explored, an
//!   over-approximation the replay lists — C-9); a descriptor operand, a
//!   std-row operand or a loop bound that reads one is a named refusal
//!   (`PC-UNTRACKED-FD`, or `PC-FD-TRUNC` when the value came from a
//!   truncating cast).
//! * [`recognize`] (design §2.4, the `ForRange` row): in a body that runs in
//!   a forked child, a loop whose header tests `v < hi` (`hi` loop-invariant),
//!   whose body is table-local (`fcntl`/`close`/`ioctl`/`dup2` with operands
//!   `v`, invariants and literals) and whose only loop-carried update is
//!   `v := v + 1` becomes one `StmtKind::ForRange { var: v, lo, hi, body }`
//!   — one SD-3 step the derivation runs at the real constants. The
//!   overflow/wrap check on `v + 1` is discharged by the guard (`v < hi` and
//!   `hi` is of the compared type, so `v + 1` is in range); any other
//!   path-ending branch, call, nested loop or untracked guard keeps the loop
//!   a CFG loop.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use trust_platform::Call;
use trust_platform_derive::program::{
    Block, Body, BodyId, CmpOp, Cond, Expr, Loc, Operand, StdCall, StmtKind, Term, Var, VarId,
};

use crate::translate::{Ctx, HaltKind, Why};
use crate::{IrSite, Refusal};

fn succs(t: &Term) -> Vec<usize> {
    match t {
        Term::Goto(b) => vec![*b],
        Term::Branch { then, els, .. } => vec![*then, *els],
        Term::Return(_) => Vec::new(),
    }
}

fn expr_find_var(e: &Expr, mut pred: impl FnMut(VarId) -> bool) -> Option<VarId> {
    match e {
        Expr::Use(Operand::Var(v)) => pred(*v).then_some(*v),
        Expr::Add(a, b) | Expr::Min(a, b) | Expr::BitAnd(a, b) => {
            if let Operand::Var(v) = a
                && pred(*v)
            {
                return Some(*v);
            }
            if let Operand::Var(v) = b
                && pred(*v)
            {
                return Some(*v);
            }
            None
        }
        Expr::Use(Operand::Lit(_)) | Expr::Opaque => None,
    }
}

fn cond_vars(c: &Cond, out: &mut Vec<VarId>) {
    match c {
        Cond::Cmp(_, a, b) => {
            for o in [a, b] {
                if let Operand::Var(v) = o {
                    out.push(*v);
                }
            }
        }
        Cond::And(x, y) | Cond::Or(x, y) => {
            cond_vars(x, out);
            cond_vars(y, out);
        }
        Cond::Not(x) => cond_vars(x, out),
        Cond::Const(_) | Cond::Nondet => {}
    }
}

fn cond_any_var(c: &Cond, pred: &mut impl FnMut(VarId) -> bool) -> bool {
    match c {
        Cond::Cmp(_, a, b) => {
            (matches!(a, Operand::Var(v) if pred(*v)))
                || (matches!(b, Operand::Var(v) if pred(*v)))
        }
        Cond::And(x, y) | Cond::Or(x, y) => cond_any_var(x, pred) || cond_any_var(y, pred),
        Cond::Not(x) => cond_any_var(x, pred),
        Cond::Const(_) | Cond::Nondet => false,
    }
}

fn call_find_var(c: &Call<Operand>, mut pred: impl FnMut(VarId) -> bool) -> Option<VarId> {
    let mut found = None;
    let _ = c.map(|o| {
        if found.is_none()
            && let Operand::Var(v) = o
            && pred(*v)
        {
            found = Some(*v);
        }
    });
    found
}

/// First variable a statement reads that satisfies `pred`.
fn stmt_find_read(kind: &StmtKind, mut pred: impl FnMut(VarId) -> bool) -> Option<VarId> {
    match kind {
        StmtKind::Event(ev) => call_find_var(&ev.call, pred),
        StmtKind::Assign { expr, .. } => expr_find_var(expr, pred),
        StmtKind::Call { args, .. } => args.iter().find_map(|(_, o)| match o {
            Operand::Var(v) if pred(*v) => Some(*v),
            _ => None,
        }),
        StmtKind::ForRange { lo, hi, .. } => [lo, hi].into_iter().find_map(|o| match o {
            Operand::Var(v) if pred(*v) => Some(*v),
            _ => None,
        }),
        StmtKind::Std(StdCall::Row { args, .. }) => args.iter().find_map(|o| match o {
            Operand::Var(v) if pred(*v) => Some(*v),
            _ => None,
        }),
        _ => None,
    }
}

fn term_any_read(t: &Term, pred: &mut impl FnMut(VarId) -> bool) -> bool {
    match t {
        Term::Branch { cond, .. } => cond_any_var(cond, pred),
        Term::Return(Some(Operand::Var(v))) => pred(*v),
        _ => false,
    }
}

/// Blocks of `body` that are targets of a back edge, with their natural
/// loops.
fn loops(body: &Body) -> Vec<(usize, BTreeSet<usize>)> {
    let n = body.blocks.len();
    let mut state = vec![0u8; n];
    let mut back = Vec::new();
    let mut stack: Vec<(usize, usize)> = vec![(0, 0)];
    if n == 0 {
        return Vec::new();
    }
    state[0] = 1;
    while let Some((b, i)) = stack.pop() {
        let ss = succs(&body.blocks[b].term);
        if i < ss.len() {
            stack.push((b, i + 1));
            let s = ss[i];
            if s >= n {
                continue;
            }
            match state[s] {
                0 => {
                    state[s] = 1;
                    stack.push((s, 0));
                }
                1 => back.push((b, s)),
                _ => {}
            }
        } else {
            state[b] = 2;
        }
    }
    let mut preds: Vec<Vec<usize>> = vec![Vec::new(); n];
    for (b, blk) in body.blocks.iter().enumerate() {
        for s in succs(&blk.term) {
            if s < n {
                preds[s].push(b);
            }
        }
    }
    let mut out: BTreeMap<usize, BTreeSet<usize>> = BTreeMap::new();
    for (tail, head) in back {
        let l = out.entry(head).or_insert_with(|| [head].into_iter().collect());
        let mut work = vec![tail];
        while let Some(x) = work.pop() {
            if l.insert(x) {
                work.extend(preds[x].iter().copied());
            }
        }
    }
    out.into_iter().collect()
}

/// X1 over a root's bodies (see the module docs).
pub(crate) fn taint(
    bodies: &mut [Body],
    vars: &[Var],
    origins: &BTreeMap<VarId, (Loc, Why)>,
    locs: &BTreeMap<Loc, IrSite>,
    refusals: &mut Vec<(Option<IrSite>, Refusal)>,
    notes: &mut Vec<String>,
) {
    let mut tainted: BTreeMap<VarId, (Loc, Why)> = BTreeMap::new();
    loop {
        let mut changed = false;
        for body in bodies.iter() {
            for block in &body.blocks {
                for s in &block.stmts {
                    match &s.kind {
                        StmtKind::Assign { var, expr: Expr::Opaque } => {
                            if !tainted.contains_key(var) {
                                let o = origins.get(var).cloned().unwrap_or_else(|| {
                                    (s.loc.clone(), Why::Op("an untracked value".into()))
                                });
                                tainted.insert(*var, o);
                                changed = true;
                            }
                        }
                        StmtKind::Assign { var, expr } => {
                            if !tainted.contains_key(var)
                                && let Some(src) = expr_find_var(expr, |x| tainted.contains_key(&x))
                            {
                                let o = tainted[&src].clone();
                                tainted.insert(*var, o);
                                changed = true;
                            }
                        }
                        StmtKind::Call { args, .. } => {
                            for (p, o) in args {
                                if let Operand::Var(x) = o
                                    && !tainted.contains_key(p)
                                    && let Some(org) = tainted.get(x).cloned()
                                {
                                    tainted.insert(*p, org);
                                    changed = true;
                                }
                            }
                        }
                        _ => {}
                    }
                }
            }
        }
        if !changed {
            break;
        }
    }
    let name = |v: VarId| vars.get(v).map_or_else(|| format!("v{v}"), |x| x.name.clone());
    let refusal_for = |org: &(Loc, Why), symbol: String, arg: String| match org.1 {
        Why::Trunc => Refusal::FdTrunc { at: org.0.0.clone() },
        _ => Refusal::UntrackedFd { symbol, arg: format!("{arg} ({}, at {})", org.1, org.0) },
    };
    for body in bodies.iter_mut() {
        let lps = loops(body);
        for (k, block) in body.blocks.iter_mut().enumerate() {
            for s in &block.stmts {
                let symbol = match &s.kind {
                    StmtKind::Event(ev) => ev.symbol.clone(),
                    StmtKind::Std(StdCall::Row { path, .. }) => path.clone(),
                    StmtKind::ForRange { .. } => "a descriptor loop".to_string(),
                    _ => continue,
                };
                if let Some(x) = stmt_find_read(&s.kind, |x| tainted.contains_key(&x)) {
                    let r = refusal_for(&tainted[&x], symbol, format!("operand `{}`", name(x)));
                    refusals.push((locs.get(&s.loc).copied(), r));
                }
            }
            if let Term::Branch { cond, .. } = &mut block.term {
                let mut hit = None;
                let new = rewrite(cond, &tainted, &mut hit);
                if let Some(x) = hit {
                    let org = tainted[&x].clone();
                    let is_event_loop = lps.iter().any(|(h, _)| *h == k);
                    if is_event_loop {
                        let r =
                            refusal_for(&org, "a loop".into(), format!("its bound `{}`", name(x)));
                        refusals.push((locs.get(&block.term_loc).copied(), r));
                    }
                    notes.push(format!(
                        "over-approximation: the guard at {} reads `{}`, untracked ({}, at {}): \
                         both arms are explored (Cond::Nondet)",
                        block.term_loc,
                        name(x),
                        org.1,
                        org.0
                    ));
                    *cond = new;
                }
            }
        }
    }
}

fn rewrite(c: &Cond, tainted: &BTreeMap<VarId, (Loc, Why)>, hit: &mut Option<VarId>) -> Cond {
    match c {
        Cond::Cmp(_, a, b) => {
            for o in [a, b] {
                if let Operand::Var(v) = o
                    && tainted.contains_key(v)
                {
                    hit.get_or_insert(*v);
                    return Cond::Nondet;
                }
            }
            c.clone()
        }
        Cond::And(x, y) => {
            Cond::And(Box::new(rewrite(x, tainted, hit)), Box::new(rewrite(y, tainted, hit)))
        }
        Cond::Or(x, y) => {
            Cond::Or(Box::new(rewrite(x, tainted, hit)), Box::new(rewrite(y, tainted, hit)))
        }
        Cond::Not(x) => Cond::Not(Box::new(rewrite(x, tainted, hit))),
        Cond::Const(_) | Cond::Nondet => c.clone(),
    }
}

/// A loop-relative symbolic value.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Sym {
    /// `v + k` (v: the induction variable's value at this iteration).
    Base(i64),
    Lit(i64),
    /// Not assigned in the loop: its value at loop entry.
    Inv,
    Unknown,
}

struct Plan {
    header: usize,
    v: VarId,
    src: VarId,
    cform: bool,
    hi: Operand,
    exit: usize,
    /// Loop blocks in topological order (the entry first).
    order: Vec<usize>,
    /// Branches discharged: block -> continuation.
    discharged: BTreeMap<usize, usize>,
    /// Statements whose operands are rewritten: (block, idx) -> new kind.
    events: BTreeMap<(usize, usize), StmtKind>,
    /// Branch conditions rewritten.
    conds: BTreeMap<usize, Cond>,
}

/// The `ForRange` recognizer over every child-context body.
pub(crate) fn recognize(
    bodies: &mut Vec<Body>,
    ctx: &[Ctx],
    halts: &BTreeMap<(BodyId, usize), HaltKind>,
    notes: &mut Vec<String>,
) {
    let n = bodies.len();
    for bi in 0..n {
        if ctx.get(bi) != Some(&Ctx::Child) {
            continue;
        }
        let mut tried = BTreeSet::new();
        loop {
            let cands: Vec<usize> = loops(&bodies[bi])
                .into_iter()
                .map(|(h, _)| h)
                .filter(|h| !tried.contains(h))
                .collect();
            let Some(h) = cands.first().copied() else { break };
            tried.insert(h);
            if let Some(plan) = analyze(&bodies[bi], bi, h, halts) {
                apply(bodies, bi, plan, notes);
            }
        }
    }
}

fn header_cond(c: &Cond) -> Option<(VarId, Operand, bool)> {
    // (v, hi, body is the then-arm)
    match c {
        Cond::Cmp(CmpOp::Lt, Operand::Var(v), hi) | Cond::Cmp(CmpOp::Gt, hi, Operand::Var(v)) => {
            Some((*v, *hi, true))
        }
        Cond::Cmp(CmpOp::Ge, Operand::Var(v), hi) | Cond::Cmp(CmpOp::Le, hi, Operand::Var(v)) => {
            Some((*v, *hi, false))
        }
        _ => None,
    }
}

#[allow(clippy::too_many_lines)]
fn analyze(
    body: &Body,
    bi: BodyId,
    h: usize,
    halts: &BTreeMap<(BodyId, usize), HaltKind>,
) -> Option<Plan> {
    let hb = &body.blocks[h];
    let Term::Branch { cond, then, els } = &hb.term else { return None };
    let (v, hi, then_is_body) = header_cond(cond)?;
    let cmp_ty = hb.term_tag.as_deref()?.strip_prefix("census:cmp:")?;
    let (entry, exit) = if then_is_body { (*then, *els) } else { (*els, *then) };
    let (src, cform) = match hb.stmts.as_slice() {
        [] => (v, false),
        [s] => match &s.kind {
            StmtKind::Assign { var, expr: Expr::Use(Operand::Var(c)) } if *var == v && *c != v => {
                (*c, true)
            }
            _ => return None,
        },
        _ => return None,
    };
    let is_halt = |b: usize| halts.contains_key(&(bi, b));
    // S: reachable from the entry without passing the header.
    let mut s_set = BTreeSet::new();
    let mut work = vec![entry];
    while let Some(b) = work.pop() {
        if b == h || b >= body.blocks.len() || !s_set.insert(b) {
            continue;
        }
        if is_halt(b) {
            continue;
        }
        work.extend(succs(&body.blocks[b].term));
    }
    if s_set.contains(&exit) || entry == h {
        return None;
    }
    let l: BTreeSet<usize> = s_set.iter().copied().filter(|b| !is_halt(*b)).collect();
    // Topological order of L (no inner cycle), entry first.
    let mut indeg: BTreeMap<usize, usize> = l.iter().map(|b| (*b, 0)).collect();
    for b in &l {
        for s in succs(&body.blocks[*b].term) {
            if let Some(d) = indeg.get_mut(&s) {
                *d += 1;
            }
        }
    }
    if indeg.get(&entry) != Some(&0) {
        return None;
    }
    let mut order = Vec::with_capacity(l.len());
    let mut q: VecDeque<usize> = VecDeque::from([entry]);
    while let Some(b) = q.pop_front() {
        order.push(b);
        for s in succs(&body.blocks[b].term) {
            if let Some(d) = indeg.get_mut(&s) {
                *d -= 1;
                if *d == 0 {
                    q.push_back(s);
                }
            }
        }
    }
    if order.len() != l.len() {
        return None;
    }
    // Every block outside L ∪ {H} that jumps into L would make it irreducible.
    for (b, blk) in body.blocks.iter().enumerate() {
        if b != h && !l.contains(&b) && succs(&blk.term).iter().any(|s| l.contains(s)) {
            return None;
        }
    }
    // Variables assigned in L ∪ {H}.
    let mut assigned: BTreeSet<VarId> = BTreeSet::new();
    for b in l.iter().chain([h].iter()) {
        for st in &body.blocks[*b].stmts {
            match &st.kind {
                StmtKind::Assign { var, .. } => {
                    assigned.insert(*var);
                }
                StmtKind::Event(ev) => {
                    assigned.extend(
                        [ev.bind.ret, ev.bind.ret2, ev.bind.rlim_soft].into_iter().flatten(),
                    );
                }
                _ => {}
            }
        }
    }
    if let Operand::Var(x) = hi
        && (assigned.contains(&x) || x == v || x == src)
    {
        return None;
    }
    // Symbolic execution.
    let eval_var = |st: &BTreeMap<VarId, Sym>, x: VarId| -> Sym {
        st.get(&x).copied().unwrap_or(if assigned.contains(&x) { Sym::Unknown } else { Sym::Inv })
    };
    let eval = |st: &BTreeMap<VarId, Sym>, e: &Expr| -> Sym {
        let op = |o: &Operand| match o {
            Operand::Lit(n) => Sym::Lit(*n),
            Operand::Var(x) => eval_var(st, *x),
        };
        match e {
            Expr::Use(o) => op(o),
            Expr::Add(a, b) => match (op(a), op(b)) {
                (Sym::Base(k), Sym::Lit(n)) | (Sym::Lit(n), Sym::Base(k)) => Sym::Base(k + n),
                (Sym::Lit(x), Sym::Lit(y)) => Sym::Lit(x.saturating_add(y)),
                _ => Sym::Unknown,
            },
            _ => Sym::Unknown,
        }
    };
    let mut init = BTreeMap::new();
    init.insert(v, Sym::Base(0));
    init.insert(src, Sym::Base(0));
    let mut state_in: BTreeMap<usize, BTreeMap<VarId, Sym>> = BTreeMap::new();
    state_in.insert(entry, init);
    let mut plan = Plan {
        header: h,
        v,
        src,
        cform,
        hi,
        exit,
        order: order.clone(),
        discharged: BTreeMap::new(),
        events: BTreeMap::new(),
        conds: BTreeMap::new(),
    };
    let ok_operand = |st: &BTreeMap<VarId, Sym>, o: &Operand| -> Option<Operand> {
        match o {
            Operand::Lit(_) => Some(*o),
            Operand::Var(x) => match eval_var(st, *x) {
                Sym::Base(0) => Some(Operand::Var(v)),
                Sym::Inv => Some(*o),
                Sym::Lit(n) => Some(Operand::Lit(n)),
                _ => None,
            },
        }
    };
    for b in &order {
        let mut st = state_in.get(b).cloned()?;
        let blk = &body.blocks[*b];
        for (i, s) in blk.stmts.iter().enumerate() {
            match &s.kind {
                StmtKind::Assign { var, expr } => {
                    let val = eval(&st, expr);
                    st.insert(*var, val);
                }
                StmtKind::Event(ev) => {
                    if !matches!(
                        ev.call,
                        Call::Fcntl { .. }
                            | Call::Close { .. }
                            | Call::Ioctl { .. }
                            | Call::Dup2 { .. }
                    ) {
                        return None;
                    }
                    let mut bad = false;
                    let call = ev.call.map(|o| {
                        ok_operand(&st, o).unwrap_or_else(|| {
                            bad = true;
                            *o
                        })
                    });
                    if bad {
                        return None;
                    }
                    let mut ev2 = ev.clone();
                    ev2.call = call;
                    plan.events.insert((*b, i), StmtKind::Event(ev2));
                    for x in [ev.bind.ret, ev.bind.ret2, ev.bind.rlim_soft].into_iter().flatten() {
                        st.insert(x, Sym::Unknown);
                    }
                }
                StmtKind::Neutral { .. } | StmtKind::Skip => {}
                _ => return None,
            }
        }
        match &blk.term {
            Term::Goto(t) if *t == h => {
                if eval_var(&st, src) != Sym::Base(1) {
                    return None;
                }
            }
            Term::Goto(t) => merge_into(&mut state_in, *t, &st),
            Term::Branch { cond, then, els } => {
                let check = blk.term_tag.as_deref().and_then(|t| {
                    t.strip_prefix("census:wrap:").or_else(|| t.strip_prefix("census:ovf:"))
                });
                if let Some(ty) = check
                    && is_halt(*els)
                    && ty == cmp_ty
                {
                    let mut vs = Vec::new();
                    cond_vars(cond, &mut vs);
                    if vs.is_empty() || vs.iter().any(|x| eval_var(&st, *x) != Sym::Base(1)) {
                        return None;
                    }
                    plan.discharged.insert(*b, *then);
                    if *then == h {
                        if eval_var(&st, src) != Sym::Base(1) {
                            return None;
                        }
                    } else {
                        merge_into(&mut state_in, *then, &st);
                    }
                    continue;
                }
                if is_halt(*then) || is_halt(*els) {
                    return None;
                }
                let c = rewrite_cond(cond, &|o| ok_operand(&st, o))?;
                plan.conds.insert(*b, c);
                for t in [*then, *els] {
                    if t == h {
                        if eval_var(&st, src) != Sym::Base(1) {
                            return None;
                        }
                    } else {
                        merge_into(&mut state_in, t, &st);
                    }
                }
            }
            Term::Return(_) => return None,
        }
    }
    // Liveness: nothing assigned in the loop (but v and its source) is read
    // outside it.
    let inside: BTreeSet<usize> = l.iter().copied().chain([h]).collect();
    let temps: BTreeSet<VarId> =
        assigned.iter().copied().filter(|x| *x != v && *x != src).collect();
    for (b, blk) in body.blocks.iter().enumerate() {
        if inside.contains(&b) {
            continue;
        }
        let mut rd_temp = |x: VarId| temps.contains(&x);
        if blk.stmts.iter().any(|s| stmt_find_read(&s.kind, &mut rd_temp).is_some())
            || term_any_read(&blk.term, &mut rd_temp)
        {
            return None;
        }
    }
    Some(plan)
}

fn merge_into(
    state_in: &mut BTreeMap<usize, BTreeMap<VarId, Sym>>,
    t: usize,
    st: &BTreeMap<VarId, Sym>,
) {
    match state_in.get_mut(&t) {
        None => {
            state_in.insert(t, st.clone());
        }
        Some(prev) => {
            for (&k, v) in prev.iter_mut() {
                if st.get(&k) != Some(v) {
                    *v = Sym::Unknown;
                }
            }
            for &k in st.keys() {
                prev.entry(k).or_insert(Sym::Unknown);
            }
        }
    }
}

fn rewrite_cond(c: &Cond, f: &dyn Fn(&Operand) -> Option<Operand>) -> Option<Cond> {
    Some(match c {
        Cond::Cmp(op, a, b) => Cond::Cmp(*op, f(a)?, f(b)?),
        Cond::And(x, y) => Cond::And(Box::new(rewrite_cond(x, f)?), Box::new(rewrite_cond(y, f)?)),
        Cond::Or(x, y) => Cond::Or(Box::new(rewrite_cond(x, f)?), Box::new(rewrite_cond(y, f)?)),
        Cond::Not(x) => Cond::Not(Box::new(rewrite_cond(x, f)?)),
        Cond::Const(b) => Cond::Const(*b),
        Cond::Nondet => return None,
    })
}

fn apply(bodies: &mut Vec<Body>, bi: BodyId, plan: Plan, notes: &mut Vec<String>) {
    let nb = bodies.len();
    let body = &bodies[bi];
    let hloc = body.blocks[plan.header].term_loc.clone();
    let map: BTreeMap<usize, usize> = plan.order.iter().enumerate().map(|(i, b)| (*b, i)).collect();
    let ret = plan.order.len();
    let m = |b: usize| if b == plan.header { ret } else { map.get(&b).copied().unwrap_or(ret) };
    let mut blocks = Vec::new();
    for b in &plan.order {
        let blk = &body.blocks[*b];
        let stmts = blk
            .stmts
            .iter()
            .enumerate()
            .filter_map(|(i, s)| match plan.events.get(&(*b, i)) {
                Some(k) => {
                    Some(trust_platform_derive::program::Stmt { kind: k.clone(), ..s.clone() })
                }
                None if matches!(s.kind, StmtKind::Neutral { .. } | StmtKind::Skip) => {
                    Some(s.clone())
                }
                None => None,
            })
            .collect();
        let term = if let Some(t) = plan.discharged.get(b) {
            Term::Goto(m(*t))
        } else {
            match &blk.term {
                Term::Goto(t) => Term::Goto(m(*t)),
                Term::Branch { then, els, .. } => Term::Branch {
                    cond: plan.conds.get(b).cloned().unwrap_or(Cond::Nondet),
                    then: m(*then),
                    els: m(*els),
                },
                Term::Return(o) => Term::Return(*o),
            }
        };
        blocks.push(Block { stmts, term, term_loc: blk.term_loc.clone(), term_tag: None });
    }
    blocks.push(Block {
        stmts: Vec::new(),
        term: Term::Return(None),
        term_loc: hloc.clone(),
        term_tag: None,
    });
    let name = format!("{} [descriptor loop at {}]", body.name, hloc);
    bodies.push(Body { name, params: Vec::new(), blocks });
    let body = &mut bodies[bi];
    let lo = Operand::Var(plan.v);
    let mut stmts = body.blocks[plan.header].stmts.clone();
    stmts.push(trust_platform_derive::program::Stmt {
        kind: StmtKind::ForRange { var: plan.v, lo, hi: plan.hi, body: nb },
        loc: hloc.clone(),
        tag: None,
    });
    if plan.cform {
        stmts.push(trust_platform_derive::program::Stmt {
            kind: StmtKind::Assign { var: plan.src, expr: Expr::Use(Operand::Var(plan.v)) },
            loc: hloc.clone(),
            tag: None,
        });
    }
    body.blocks[plan.header] =
        Block { stmts, term: Term::Goto(plan.exit), term_loc: hloc.clone(), term_tag: None };
    for b in &plan.order {
        body.blocks[*b] = Block {
            stmts: Vec::new(),
            term: Term::Return(None),
            term_loc: hloc.clone(),
            term_tag: None,
        };
    }
    notes.push(format!(
        "descriptor loop at {hloc} recognized as one ForRange step ({} form, bound {:?})",
        if plan.cform { "cell" } else { "block-parameter" },
        plan.hi
    ));
}
