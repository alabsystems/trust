//! X6 tests: [`alpha_eq`] holds under exactly the renamings its contract
//! names (and the derivation agrees: the same machine sizes and verdict),
//! and fails on every single perturbation of a fixture — the M1 fixtures
//! and the M2 ones (release marks, thread start and join, std opens, the
//! M2 policies), each checked under its own property.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use trust_platform::{Call, Errno, Oracle, darwin};

use super::*;
use crate::derive::{DeriveOptions, Derived, Stats, derive};
use crate::program::{Loc, ProgramBuilder, StmtRef};
use crate::{fixtures, property};

// ---- a deterministic scrambler: the renamings alpha_eq must ignore ----------

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        // xorshift64*
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }
    fn below(&mut self, n: usize) -> usize {
        usize::try_from(self.next() % u64::try_from(n.max(1)).unwrap_or(1)).unwrap_or(0)
    }
    /// A permutation of `0..n` (Fisher-Yates); `fix0` keeps 0 in place.
    fn perm(&mut self, n: usize, fix0: bool) -> Vec<usize> {
        let mut v: Vec<usize> = (0..n).collect();
        let lo = usize::from(fix0 && n > 0);
        for i in (lo + 1..n).rev() {
            let j = lo + self.below(i - lo + 1);
            v.swap(i, j);
        }
        v
    }
}

/// The renamings a scramble applied (old index -> new index).
struct Scramble {
    vars: Vec<usize>,
    bodies: Vec<usize>,
    sites: Vec<usize>,
    classes: BTreeMap<String, String>,
}

fn rename_class(map: &mut BTreeMap<String, String>, c: &str) -> String {
    if reserved(c) {
        return c.to_string();
    }
    let n = map.len();
    map.entry(c.to_string()).or_insert_with(|| format!("cls{n}")).clone()
}

/// Rename everything alpha_eq ignores, insert `Skip`s, jump-only blocks and
/// inert dead blocks, and permute blocks (the entry stays block 0).
fn scramble(p: &EventProgram, seed: u64) -> (EventProgram, Scramble) {
    let mut rng = Rng(seed | 1);
    let vperm = rng.perm(p.vars.len(), false);
    let bperm = rng.perm(p.bodies.len(), false);
    let sperm = rng.perm(p.sites.len(), false);
    let mut classes = BTreeMap::new();
    let mut locs = 0usize;
    let mut loc = || {
        locs += 1;
        Loc::new(format!("scrambled:{locs}"))
    };
    let v = |x: VarId| vperm[x];
    let op = |o: &Operand| match o {
        Operand::Lit(x) => Operand::Lit(*x),
        Operand::Var(x) => Operand::Var(v(*x)),
    };
    fn cond(c: &Cond, op: &dyn Fn(&Operand) -> Operand) -> Cond {
        match c {
            Cond::Cmp(k, a, b) => Cond::Cmp(*k, op(a), op(b)),
            Cond::And(a, b) => Cond::And(Box::new(cond(a, op)), Box::new(cond(b, op))),
            Cond::Or(a, b) => Cond::Or(Box::new(cond(a, op)), Box::new(cond(b, op))),
            Cond::Not(a) => Cond::Not(Box::new(cond(a, op))),
            Cond::Const(b) => Cond::Const(*b),
            Cond::Nondet => Cond::Nondet,
        }
    }
    let bind =
        |b: &Bind| Bind { ret: b.ret.map(v), ret2: b.ret2.map(v), rlim_soft: b.rlim_soft.map(v) };
    let mut bodies: Vec<Option<Body>> = vec![None; p.bodies.len()];
    for (bi, body) in p.bodies.iter().enumerate() {
        let n = body.blocks.len();
        let kperm = rng.perm(n, true);
        // Old block j lives at kperm[j]; trampoline to it at n + j; then one
        // inert dead block.
        let mut blocks: Vec<Option<Block>> = vec![None; 2 * n + 1];
        let retarget = |t: BlockId, rng: &mut Rng| {
            if rng.below(2) == 0 { kperm[t] } else { n + t }
        };
        for (j, block) in body.blocks.iter().enumerate() {
            let mut stmts = Vec::new();
            for s in &block.stmts {
                if rng.below(3) == 0 {
                    stmts.push(Stmt { kind: StmtKind::Skip, loc: loc(), tag: None });
                }
                let kind = match &s.kind {
                    StmtKind::Event(e) => StmtKind::Event(Event {
                        symbol: e.symbol.clone(),
                        call: e.call.map(op),
                        bind: bind(&e.bind),
                        oracles: e.oracles.clone(),
                        site: e.site.map(|x| sperm[x]),
                        ofd_names: e
                            .ofd_names
                            .iter()
                            .map(|c| rename_class(&mut classes, c))
                            .collect(),
                        std_origin: e.std_origin.clone(),
                        path: e.path.clone(),
                        // Its text is notes only; a raw read/write keeps
                        // whether it has one (lower admits it only with one).
                        assumption: e
                            .assumption
                            .as_ref()
                            .filter(|_| raw_io(e))
                            .map(|_| "scrambled assumption".to_string()),
                    }),
                    StmtKind::Assign { var, expr } => StmtKind::Assign {
                        var: v(*var),
                        expr: match expr {
                            Expr::Use(a) => Expr::Use(op(a)),
                            Expr::Add(a, b) => Expr::Add(op(a), op(b)),
                            Expr::Min(a, b) => Expr::Min(op(a), op(b)),
                            Expr::BitAnd(a, b) => Expr::BitAnd(op(a), op(b)),
                            Expr::Opaque => Expr::Opaque,
                        },
                    },
                    StmtKind::Call { body, args, ret } => StmtKind::Call {
                        body: bperm[*body],
                        args: args.iter().map(|(x, o)| (v(*x), op(o))).collect(),
                        ret: ret.map(v),
                    },
                    StmtKind::ForRange { var, lo, hi, body } => StmtKind::ForRange {
                        var: v(*var),
                        lo: op(lo),
                        hi: op(hi),
                        body: bperm[*body],
                    },
                    StmtKind::Fork { child, site, bind, std_origin } => StmtKind::Fork {
                        child: bperm[*child],
                        site: sperm[*site],
                        bind: bind.map(v),
                        std_origin: std_origin.clone(),
                    },
                    StmtKind::Neutral { symbol } => StmtKind::Neutral { symbol: symbol.clone() },
                    StmtKind::Std(StdCall::Row { path, args, bind, ofd_names }) => {
                        StmtKind::Std(StdCall::Row {
                            path: path.clone(),
                            args: args.iter().map(op).collect(),
                            bind: bind.iter().map(|x| v(*x)).collect(),
                            ofd_names: ofd_names
                                .iter()
                                .map(|c| rename_class(&mut classes, c))
                                .collect(),
                        })
                    }
                    StmtKind::Std(StdCall::CommandSpawn { stdio, shape, pre_exec, site, bind }) => {
                        StmtKind::Std(StdCall::CommandSpawn {
                            stdio: *stdio,
                            shape: *shape,
                            pre_exec: pre_exec.iter().map(|b| bperm[*b]).collect(),
                            site: sperm[*site],
                            bind: bind.map(v),
                        })
                    }
                    StmtKind::Std(StdCall::OpenFile { std_fn, file, flags, bind, ofd_name }) => {
                        StmtKind::Std(StdCall::OpenFile {
                            std_fn: std_fn.clone(),
                            file: file.clone(),
                            flags: *flags,
                            bind: v(*bind),
                            ofd_name: rename_class(&mut classes, ofd_name),
                        })
                    }
                    StmtKind::Release { classes: cs } => StmtKind::Release {
                        classes: cs.iter().map(|c| rename_class(&mut classes, c)).collect(),
                    },
                    // Roots keep their indices.
                    StmtKind::SpawnThread { root } => StmtKind::SpawnThread { root: *root },
                    StmtKind::Join { root } => StmtKind::Join { root: *root },
                    StmtKind::Skip => StmtKind::Skip,
                };
                stmts.push(Stmt { kind, loc: loc(), tag: None });
            }
            let term = match &block.term {
                Term::Goto(t) => Term::Goto(retarget(*t, &mut rng)),
                Term::Branch { cond: c, then, els } => Term::Branch {
                    cond: cond(c, &op),
                    then: retarget(*then, &mut rng),
                    els: retarget(*els, &mut rng),
                },
                Term::Return(o) => Term::Return(o.as_ref().map(op)),
            };
            blocks[kperm[j]] = Some(Block { stmts, term, term_loc: loc(), term_tag: None });
            blocks[n + j] = Some(Block {
                stmts: vec![Stmt { kind: StmtKind::Skip, loc: loc(), tag: None }],
                term: Term::Goto(kperm[j]),
                term_loc: loc(),
                term_tag: None,
            });
        }
        blocks[2 * n] = Some(Block {
            stmts: Vec::new(),
            term: Term::Return(None),
            term_loc: loc(),
            term_tag: None,
        });
        let blocks = if n == 0 { Vec::new() } else { blocks.into_iter().flatten().collect() };
        bodies[bperm[bi]] = Some(Body {
            name: format!("body{}", bperm[bi]),
            params: body.params.iter().map(|x| v(*x)).collect(),
            blocks,
        });
    }
    let mut vars: Vec<Option<Var>> = vec![None; p.vars.len()];
    for (i, var) in p.vars.iter().enumerate() {
        vars[vperm[i]] = Some(Var { name: format!("v{}", vperm[i]), init: var.init });
    }
    let mut sites: Vec<Option<SpawnSite>> = vec![None; p.sites.len()];
    for (i, s) in p.sites.iter().enumerate() {
        sites[sperm[i]] = Some(SpawnSite {
            name: format!("site{}", sperm[i]),
            loc: loc(),
            policy: s.policy.as_ref().map(|f| FdInherit {
                lanes: f
                    .lanes
                    .iter()
                    .map(|l| Lane { fd: l.fd, ofd_class: rename_class(&mut classes, &l.ofd_class) })
                    .collect(),
            }),
        });
    }
    let fd_params = p
        .fd_params
        .iter()
        .map(|f| FdParam {
            var: v(f.var),
            class: rename_class(&mut classes, &f.class),
            peer_class: f.peer_class.as_ref().map(|c| rename_class(&mut classes, c)),
        })
        .collect();
    let q = EventProgram {
        name: format!("{} (scrambled)", p.name),
        provenance: Vec::new(),
        vars: vars.into_iter().flatten().collect(),
        bodies: bodies.into_iter().flatten().collect(),
        roots: p
            .roots
            .iter()
            .enumerate()
            .map(|(k, r)| Root {
                name: format!("root{k}"),
                body: bperm[r.body],
                dormant: r.dormant,
            })
            .collect(),
        sites: sites.into_iter().flatten().collect(),
        fd_params,
        disclosures: Vec::new(),
        // Membership is what is read: the fd-identity roots, reversed.
        policies: Policies {
            lock_release: p.policies.lock_release,
            fd_identity: p.policies.fd_identity.iter().rev().copied().collect(),
        },
    };
    (q, Scramble { vars: vperm, bodies: bperm, sites: sperm, classes })
}

// ---- helpers ------------------------------------------------------------------

/// Machine states reachable from `rl_init` carrying `atom`.
fn reachable_with(d: &Derived, atom: &str) -> usize {
    let n = d.machine.states.len();
    let mut succ = vec![Vec::new(); n];
    for (f, _, t) in &d.machine.transitions {
        succ[*f].push(*t);
    }
    let mut seen = vec![false; n];
    let mut q = VecDeque::from([0usize]);
    seen[0] = true;
    let mut hits = 0;
    while let Some(s) = q.pop_front() {
        if d.machine.labels.get(&s).is_some_and(|l| l.iter().any(|x| x == atom)) {
            hits += 1;
        }
        for t in &succ[s] {
            if !seen[*t] {
                seen[*t] = true;
                q.push_back(*t);
            }
        }
    }
    hits
}

/// The machine's shape, without anything a name can change.
fn shape(s: &Stats) -> [usize; 9] {
    [
        s.init_tables,
        s.concrete_states,
        s.abstract_states,
        s.full_states,
        s.machine_states,
        s.machine_transitions,
        s.actions,
        s.horizon_states,
        usize::from(s.encoding_exact),
    ]
}

/// Every variable a statement, terminator, parameter list or descriptor
/// parameter of `p` names.
fn used_vars(p: &EventProgram) -> BTreeSet<VarId> {
    let mut out = BTreeSet::new();
    let op = |o: &Operand, out: &mut BTreeSet<VarId>| {
        if let Operand::Var(x) = o {
            out.insert(*x);
        }
    };
    fn cond(c: &Cond, out: &mut BTreeSet<VarId>) {
        match c {
            Cond::Cmp(_, a, b) => {
                for o in [a, b] {
                    if let Operand::Var(x) = o {
                        out.insert(*x);
                    }
                }
            }
            Cond::And(a, b) | Cond::Or(a, b) => {
                cond(a, out);
                cond(b, out);
            }
            Cond::Not(a) => cond(a, out),
            Cond::Const(_) | Cond::Nondet => {}
        }
    }
    for f in &p.fd_params {
        out.insert(f.var);
    }
    for body in &p.bodies {
        out.extend(body.params.iter().copied());
        for block in &body.blocks {
            for s in &block.stmts {
                match &s.kind {
                    StmtKind::Event(e) => {
                        let _ = e.call.map(|o| op(o, &mut out));
                        out.extend(
                            [e.bind.ret, e.bind.ret2, e.bind.rlim_soft].into_iter().flatten(),
                        );
                    }
                    StmtKind::Assign { var, expr } => {
                        out.insert(*var);
                        match expr {
                            Expr::Use(a) => op(a, &mut out),
                            Expr::Add(a, b) | Expr::Min(a, b) | Expr::BitAnd(a, b) => {
                                op(a, &mut out);
                                op(b, &mut out);
                            }
                            Expr::Opaque => {}
                        }
                    }
                    StmtKind::Call { args, ret, .. } => {
                        for (x, o) in args {
                            out.insert(*x);
                            op(o, &mut out);
                        }
                        out.extend(ret.iter().copied());
                    }
                    StmtKind::ForRange { var, lo, hi, .. } => {
                        out.insert(*var);
                        op(lo, &mut out);
                        op(hi, &mut out);
                    }
                    StmtKind::Fork { bind, .. } => out.extend(bind.iter().copied()),
                    StmtKind::Std(StdCall::Row { args, bind, .. }) => {
                        for o in args {
                            op(o, &mut out);
                        }
                        out.extend(bind.iter().copied());
                    }
                    StmtKind::Std(StdCall::CommandSpawn { bind, .. }) => {
                        out.extend(bind.iter().copied());
                    }
                    StmtKind::Std(StdCall::OpenFile { bind, .. }) => {
                        out.insert(*bind);
                    }
                    StmtKind::Neutral { .. }
                    | StmtKind::Skip
                    | StmtKind::Release { .. }
                    | StmtKind::SpawnThread { .. }
                    | StmtKind::Join { .. } => {}
                }
            }
            match &block.term {
                Term::Branch { cond: c, .. } => cond(c, &mut out),
                Term::Return(Some(o)) => op(o, &mut out),
                Term::Goto(_) | Term::Return(None) => {}
            }
        }
    }
    out
}

// ---- the fixtures: M1's and M2's, each with the atom its verdict reads -----

struct Case {
    name: &'static str,
    program: EventProgram,
    env: crate::env::EnvSpec,
    /// The proposition whose reachability is the fixture's verdict.
    atom: String,
}

fn cases() -> Vec<Case> {
    let m1 = fixtures::all().into_iter().map(|f| Case {
        name: f.name,
        atom: property::premised(property::VIOLATION, &f.premises),
        program: f.program,
        env: f.env,
    });
    let m2 = fixtures::m2().into_iter().map(|f| Case {
        name: f.name,
        atom: match f.property {
            fixtures::Property::LockRelease => property::LOCK_LEAK.to_string(),
            fixtures::Property::FdIdentity => property::FD_IDENTITY_VIOLATION.to_string(),
        },
        program: f.program,
        env: f.env,
    });
    m1.chain(m2).collect()
}

// ---- reflexivity, invariance, congruence ----------------------------------------

#[test]
fn every_fixture_is_alpha_equal_to_itself_by_the_identity() {
    for f in cases() {
        let w = alpha_witness(&f.program, &f.program).unwrap_or_else(|e| panic!("{}: {e}", f.name));
        assert!(w.vars.iter().all(|(x, y)| x == y), "{}", f.name);
        assert!(w.bodies.iter().all(|(x, y)| x == y), "{}", f.name);
        assert!(w.sites.iter().all(|(x, y)| x == y), "{}", f.name);
        assert!(w.classes.iter().all(|(x, y)| x == y), "{}", f.name);
        assert_eq!(w.vars.keys().copied().collect::<BTreeSet<_>>(), used_vars(&f.program));
        assert_eq!(w.bodies.len(), f.program.bodies.len(), "{}: a body no root reaches", f.name);
    }
}

/// Every fixture, scrambled three ways, is alpha-equal to itself through
/// exactly the scramble's renaming, and derives the same machine (sizes,
/// injectivity of the encoding, fd-inherit verdict): the things alpha_eq
/// ignores are things the derivation does not read.
#[test]
fn a_scrambled_fixture_is_alpha_equal_and_derives_the_same_machine() {
    for f in cases() {
        let d = derive(&f.program, &f.env, &DeriveOptions::default())
            .unwrap_or_else(|e| panic!("{}: {e}", f.name));
        let atom = &f.atom;
        for seed in [1u64, 0x9e37_79b9, 0xdead_beef] {
            let (q, s) = scramble(&f.program, seed);
            assert_ne!(q, f.program, "{}: the scramble changed nothing", f.name);
            let w = alpha_witness(&f.program, &q)
                .unwrap_or_else(|e| panic!("{} (seed {seed:#x}): {e}", f.name));
            for (x, y) in &w.vars {
                assert_eq!(s.vars[*x], *y, "{}: var {x}", f.name);
            }
            for (x, y) in &w.bodies {
                assert_eq!(s.bodies[*x], *y, "{}: body {x}", f.name);
            }
            for (x, y) in &w.sites {
                assert_eq!(s.sites[*x], *y, "{}: site {x}", f.name);
            }
            for (x, y) in &w.classes {
                assert_eq!(s.classes.get(x).unwrap_or(x), y, "{}: class {x}", f.name);
            }
            assert!(alpha_eq(&q, &f.program), "{}: not symmetric", f.name);
            let e = derive(&q, &f.env, &DeriveOptions::default())
                .unwrap_or_else(|e| panic!("{} scrambled: {e}", f.name));
            assert_eq!(shape(&d.stats), shape(&e.stats), "{} (seed {seed:#x})", f.name);
            assert_eq!(
                reachable_with(&d, atom) > 0,
                reachable_with(&e, atom) > 0,
                "{} (seed {seed:#x}): the verdict moved",
                f.name
            );
        }
    }
}

// ---- single perturbations: each must be a mismatch -------------------------------

/// Every way of changing one thing in a program that the derivation reads.
fn perturbations(p: &EventProgram) -> Vec<(String, EventProgram)> {
    let used: Vec<VarId> = used_vars(p).into_iter().collect();
    let other_var = |x: VarId| used.iter().copied().find(|y| *y != x);
    let mut class_names: Vec<String> = Vec::new();
    for (_, s) in p.stmts() {
        match &s.kind {
            StmtKind::Event(e) => class_names.extend(e.ofd_names.iter().cloned()),
            StmtKind::Std(StdCall::OpenFile { ofd_name, .. }) => class_names.push(ofd_name.clone()),
            _ => {}
        }
    }
    class_names.sort();
    class_names.dedup();
    let mut out: Vec<(String, EventProgram)> = Vec::new();
    let refs: Vec<StmtRef> = p.stmts().map(|(r, _)| r).collect();
    let bump = |o: &Operand| match o {
        Operand::Lit(x) => Operand::Lit(x + 1),
        Operand::Var(x) => Operand::Var(*x),
    };
    for at in refs {
        let s = p.stmt(at).cloned().expect("stmt");
        let mut push = |what: String, kind: StmtKind| {
            let mut q = p.clone();
            q.bodies[at.body].blocks[at.block].stmts[at.idx].kind = kind;
            out.push((format!("{at} {what}"), q));
        };
        // A statement a mutation already deleted (an M2 fixture built by one)
        // has nothing left to delete.
        if !matches!(s.kind, StmtKind::Skip) {
            push("deleted".to_string(), StmtKind::Skip);
        }
        match &s.kind {
            StmtKind::Event(e) => {
                let mut ops = Vec::new();
                let _ = e.call.map(|o| ops.push(*o));
                for (k, o) in ops.iter().enumerate() {
                    let mut n = 0usize;
                    let new = match o {
                        Operand::Lit(_) => e.call.map(|x| {
                            n += 1;
                            if n - 1 == k { bump(x) } else { *x }
                        }),
                        Operand::Var(x) => {
                            let Some(y) = other_var(*x) else { continue };
                            e.call.map(|z| {
                                n += 1;
                                if n - 1 == k { Operand::Var(y) } else { *z }
                            })
                        }
                    };
                    push(format!("operand {k}"), StmtKind::Event(Event { call: new, ..e.clone() }));
                }
                let mut oracles = e.oracles.clone();
                oracles.push(Oracle::Fail(Errno::EBADF));
                push("oracles".to_string(), StmtKind::Event(Event { oracles, ..e.clone() }));
                if let Some(r) = e.bind.ret
                    && let Some(y) = other_var(r)
                {
                    let bind = Bind { ret: Some(y), ..e.bind.clone() };
                    push("bind".to_string(), StmtKind::Event(Event { bind, ..e.clone() }));
                }
                if let Some(first) = e.ofd_names.first()
                    && let Some(other) = class_names.iter().find(|c| *c != first)
                {
                    let mut names = e.ofd_names.clone();
                    names[0].clone_from(other);
                    push(
                        "class".to_string(),
                        StmtKind::Event(Event { ofd_names: names, ..e.clone() }),
                    );
                }
                push(
                    "symbol".to_string(),
                    StmtKind::Event(Event { symbol: format!("{}_", e.symbol), ..e.clone() }),
                );
                if raw_io(e) {
                    let assumption = match e.assumption {
                        Some(_) => None,
                        None => Some("assumed".to_string()),
                    };
                    push(
                        "raw read/write assumption".to_string(),
                        StmtKind::Event(Event { assumption, ..e.clone() }),
                    );
                }
                if let Call::Spawn { actions, flags } = &e.call {
                    let call = Call::Spawn {
                        actions: actions.clone(),
                        flags: flags ^ darwin::POSIX_SPAWN_CLOEXEC_DEFAULT,
                    };
                    push("spawn flags".to_string(), StmtKind::Event(Event { call, ..e.clone() }));
                }
            }
            StmtKind::Assign { var, expr } => {
                if let Some(y) = other_var(*var) {
                    push("target".to_string(), StmtKind::Assign { var: y, expr: expr.clone() });
                }
                let e2 = match expr {
                    Expr::Use(a) => Expr::Add(*a, Operand::Lit(0)),
                    Expr::Add(a, b) => Expr::Min(*a, *b),
                    Expr::Min(a, b) => Expr::Add(*a, *b),
                    Expr::BitAnd(a, b) => Expr::Min(*a, *b),
                    Expr::Opaque => Expr::Use(Operand::Lit(0)),
                };
                push("expression".to_string(), StmtKind::Assign { var: *var, expr: e2 });
            }
            StmtKind::Call { body, args, ret } => {
                if let Some((x, Operand::Lit(_))) = args.first() {
                    let mut a2 = args.clone();
                    a2[0] = (*x, bump(&args[0].1));
                    push(
                        "argument".to_string(),
                        StmtKind::Call { body: *body, args: a2, ret: *ret },
                    );
                }
                if let Some(r) = ret
                    && let Some(y) = other_var(*r)
                {
                    push(
                        "result".to_string(),
                        StmtKind::Call { body: *body, args: args.clone(), ret: Some(y) },
                    );
                }
            }
            StmtKind::ForRange { var, lo, hi, body } => {
                let (lo2, hi2) = match (lo, hi) {
                    (Operand::Lit(_), _) => (bump(lo), *hi),
                    (_, Operand::Lit(_)) => (*lo, bump(hi)),
                    (Operand::Var(x), _) => match other_var(*x) {
                        Some(y) => (Operand::Var(y), *hi),
                        None => continue,
                    },
                };
                push(
                    "bound".to_string(),
                    StmtKind::ForRange { var: *var, lo: lo2, hi: hi2, body: *body },
                );
            }
            StmtKind::Neutral { symbol } => {
                push("symbol".to_string(), StmtKind::Neutral { symbol: format!("{symbol}_") });
            }
            StmtKind::Std(StdCall::CommandSpawn { stdio, shape, pre_exec, site, bind }) => {
                let mut sh = *shape;
                sh.setsid = !sh.setsid;
                push(
                    "spawn shape".to_string(),
                    StmtKind::Std(StdCall::CommandSpawn {
                        stdio: *stdio,
                        shape: sh,
                        pre_exec: pre_exec.clone(),
                        site: *site,
                        bind: *bind,
                    }),
                );
            }
            StmtKind::Std(StdCall::Row { path, args, bind, ofd_names }) => {
                push(
                    "row".to_string(),
                    StmtKind::Std(StdCall::Row {
                        path: format!("{path}_"),
                        args: args.clone(),
                        bind: bind.clone(),
                        ofd_names: ofd_names.clone(),
                    }),
                );
            }
            StmtKind::Std(StdCall::OpenFile { std_fn, file, flags, bind, ofd_name }) => {
                let open = |std_fn: &str, file: &str, flags: i32, bind: VarId, ofd: &str| {
                    StmtKind::Std(StdCall::OpenFile {
                        std_fn: std_fn.to_string(),
                        file: file.to_string(),
                        flags,
                        bind,
                        ofd_name: ofd.to_string(),
                    })
                };
                push(
                    "std fn".to_string(),
                    open(&format!("{std_fn}_"), file, *flags, *bind, ofd_name),
                );
                push(
                    "std path".to_string(),
                    open(std_fn, &format!("{file}_"), *flags, *bind, ofd_name),
                );
                push(
                    "std flags".to_string(),
                    open(std_fn, file, flags ^ darwin::O_EXLOCK, *bind, ofd_name),
                );
                if let Some(y) = other_var(*bind) {
                    push("std bind".to_string(), open(std_fn, file, *flags, y, ofd_name));
                }
                if let Some(other) = class_names.iter().find(|c| *c != ofd_name) {
                    push("std class".to_string(), open(std_fn, file, *flags, *bind, other));
                }
            }
            StmtKind::Release { classes } => {
                if let Some(first) = classes.first()
                    && let Some(other) = class_names.iter().find(|c| *c != first)
                {
                    let mut cs = classes.clone();
                    cs[0].clone_from(other);
                    push("released class".to_string(), StmtKind::Release { classes: cs });
                }
                let mut more = classes.clone();
                more.extend(class_names.iter().find(|c| !classes.contains(c)).cloned());
                if more.len() > classes.len() {
                    push(
                        "one more released class".to_string(),
                        StmtKind::Release { classes: more },
                    );
                }
            }
            StmtKind::SpawnThread { root } => {
                if let Some(other) = (0..p.roots.len()).find(|r| r != root && p.roots[*r].dormant) {
                    push("started root".to_string(), StmtKind::SpawnThread { root: other });
                }
            }
            StmtKind::Join { root } => {
                if let Some(other) = (0..p.roots.len()).find(|r| r != root) {
                    push("joined root".to_string(), StmtKind::Join { root: other });
                }
            }
            StmtKind::Fork { .. } | StmtKind::Skip => {}
        }
    }
    for (bi, body) in p.bodies.iter().enumerate() {
        for (k, block) in body.blocks.iter().enumerate() {
            let mut push = |what: &str, term: Term| {
                let mut q = p.clone();
                q.bodies[bi].blocks[k].term = term;
                out.push((format!("b{bi}.{k} {what}"), q));
            };
            match &block.term {
                Term::Branch { cond, then, els } => push(
                    "negated guard",
                    Term::Branch {
                        cond: Cond::Not(Box::new(cond.clone())),
                        then: *then,
                        els: *els,
                    },
                ),
                Term::Return(Some(Operand::Lit(x))) => {
                    push("return value", Term::Return(Some(Operand::Lit(x + 1))));
                }
                _ => {}
            }
        }
    }
    for x in &used {
        let mut q = p.clone();
        q.vars[*x].init += 1;
        out.push((format!("init of var {x}"), q));
    }
    for (si, s) in p.sites.iter().enumerate() {
        if let Some(f) = &s.policy
            && !f.lanes.is_empty()
        {
            let mut q = p.clone();
            if let Some(pol) = q.sites[si].policy.as_mut() {
                pol.lanes[0].fd += 1000;
            }
            out.push((format!("site {si} lane"), q));
        }
        let mut q = p.clone();
        q.sites[si].policy =
            if s.policy.is_some() { None } else { Some(FdInherit { lanes: Vec::new() }) };
        out.push((format!("site {si} policy"), q));
    }
    // M2: the policies, and whether a root waits to be started.
    let mut q = p.clone();
    q.policies.lock_release = !q.policies.lock_release;
    out.push(("P-LOCK-RELEASE".to_string(), q));
    for r in 0..p.roots.len() {
        let mut q = p.clone();
        if let Some(k) = q.policies.fd_identity.iter().position(|x| *x == r) {
            q.policies.fd_identity.remove(k);
        } else {
            q.policies.fd_identity.push(r);
        }
        out.push((format!("fd-identity of root {r}"), q));
        let mut q = p.clone();
        q.roots[r].dormant = !q.roots[r].dormant;
        out.push((format!("root {r} dormant"), q));
    }
    out
}

#[test]
fn every_single_perturbation_of_a_fixture_is_a_mismatch() {
    let mut checked = 0usize;
    for f in cases() {
        for (what, q) in perturbations(&f.program) {
            if let Ok(w) = alpha_witness(&f.program, &q) {
                panic!("{}: `{what}` is alpha-equal to the original: {w:?}", f.name);
            }
            checked += 1;
        }
    }
    assert!(checked > 1000, "only {checked} perturbations");
}

// ---- named cases ---------------------------------------------------------------

fn tiny(name: &str, f: impl FnOnce(&mut ProgramBuilder, VarId)) -> EventProgram {
    let mut p = ProgramBuilder::new(name);
    let fd = p.var("fd", -1);
    f(&mut p, fd);
    p.build()
}

fn mismatch(a: &EventProgram, b: &EventProgram) -> String {
    match alpha_witness(a, b) {
        Err(m) => m.to_string(),
        Ok(w) => panic!("expected a mismatch, got {w:?}"),
    }
}

/// X1's constructs are compared like any other.
#[test]
fn opaque_and_nondet_are_compared() {
    let build = |expr: Expr, cond: Cond| {
        tiny("x1", |p, fd| {
            let main = p.body("main", Vec::new(), |b| {
                b.assign("t:1", fd, expr);
                b.when("t:2", cond, |b| {
                    b.event("t:3", "close", Call::Close { fd: Operand::Lit(9) }, Bind::none());
                });
            });
            p.root("main", main);
        })
    };
    let x1 = build(Expr::Opaque, Cond::Nondet);
    assert!(alpha_eq(&x1, &build(Expr::Opaque, Cond::Nondet)));
    assert!(mismatch(&x1, &build(Expr::Use(Operand::Lit(0)), Cond::Nondet)).contains("expression"));
    assert!(mismatch(&x1, &build(Expr::Opaque, Cond::Const(true))).contains("guard"));
}

/// M2's constructs are compared: a release mark's classes under the class
/// renaming, a thread start and join by root index, whether a root is
/// dormant, the M2 policies (the fd-identity roots as a set), a std open's
/// fields, and whether a raw read/write carries the census's assumption
/// (not its text).
#[test]
fn m2_constructs_are_compared() {
    #[derive(Clone, Copy)]
    struct V {
        lock: &'static str,
        release: &'static str,
        started: usize,
        dormant: bool,
        lock_release: bool,
        identity: &'static [usize],
        flags: i32,
        why: Option<&'static str>,
    }
    let base = V {
        lock: "lock",
        release: "lock",
        started: 1,
        dormant: true,
        lock_release: true,
        identity: &[0, 1],
        flags: darwin::O_RDWR | darwin::O_CREAT,
        why: Some("a byte on a socketpair end"),
    };
    let build = |v: V| {
        let mut p = ProgramBuilder::new("m2");
        let fd = p.var("fd", -1);
        let worker = p.body("worker", Vec::new(), |b| {
            b.io(
                "t:10",
                Call::WriteSome { fd: Operand::Lit(1) },
                Bind::none(),
                v.why.unwrap_or_default(),
            );
        });
        let main = p.body("main", Vec::new(), |b| {
            b.std_open("t:1", "std::fs::File::create", "lockfile", v.flags, fd, v.lock);
            b.spawn_thread("t:2", v.started);
            b.join("t:3", v.started);
            b.event("t:4", "close", Call::Close { fd: Operand::Var(fd) }, Bind::none());
            b.release("t:5", &[v.release]);
        });
        p.root("main", main);
        let t = p.thread("worker", worker);
        if v.lock_release {
            p.lock_release_policy();
        }
        p.fd_identity_policy(v.identity);
        let mut prog = p.build();
        prog.roots[t].dormant = v.dormant;
        if v.why.is_none() {
            for b in &mut prog.bodies {
                for k in &mut b.blocks {
                    for st in &mut k.stmts {
                        if let StmtKind::Event(e) = &mut st.kind {
                            e.assumption = None;
                        }
                    }
                }
            }
        }
        prog
    };
    let a = build(base);
    // Renamed class (both uses), the identity roots reordered, the
    // assumption's text: equal.
    assert!(alpha_eq(&a, &build(V { lock: "held", release: "held", ..base })));
    assert!(alpha_eq(&a, &build(V { identity: &[1, 0], ..base })));
    assert!(alpha_eq(&a, &build(V { why: Some("another text"), ..base })));
    for (what, v, says) in [
        ("released class", V { release: "other", ..base }, "already paired"),
        ("started root", V { started: 0, ..base }, "root"),
        ("dormant", V { dormant: false, ..base }, "dormant"),
        ("P-LOCK-RELEASE", V { lock_release: false, ..base }, "P-LOCK-RELEASE"),
        ("fd-identity", V { identity: &[0], ..base }, "fd-identity"),
        ("open flags", V { flags: darwin::O_RDWR, ..base }, "std open"),
        ("assumption", V { why: None, ..base }, "assumption"),
    ] {
        let m = mismatch(&a, &build(v));
        assert!(m.contains(says), "{what}: {m}");
    }
}

/// Unreachable code with content is not compared: a mismatch, even against
/// itself, never a silent equality.
#[test]
fn unreachable_content_is_a_mismatch() {
    let mut p = ProgramBuilder::new("dead");
    let main = p.body("main", Vec::new(), |b| {
        b.ret("t:1", None);
        b.event("t:2", "close", Call::Close { fd: Operand::Lit(9) }, Bind::none());
    });
    p.root("main", main);
    let p = p.build();
    assert!(mismatch(&p, &p).contains("unreachable block has content"));

    let mut q = ProgramBuilder::new("dead body");
    let main = q.body("main", Vec::new(), |_| {});
    q.body("unused", Vec::new(), |b| {
        b.event("t:2", "close", Call::Close { fd: Operand::Lit(9) }, Bind::none());
    });
    q.root("main", main);
    let q = q.build();
    assert!(mismatch(&q, &q).contains("no root reaches"));
}

/// The interpreter reads the rest of a block (an `F_DUPFD` then `close` of
/// its source is a move a torn table copy can straddle), so splitting a
/// block in two — even with a plain jump between the halves — is not a
/// renaming.
#[test]
fn block_boundaries_are_compared() {
    let whole = tiny("move", |p, fd| {
        let main = p.body("main", Vec::new(), |b| {
            b.event(
                "t:1",
                "fcntl",
                Call::Fcntl { fd: Operand::Var(fd), cmd: darwin::F_DUPFD, arg: 10 },
                Bind::none(),
            );
            b.event("t:2", "close", Call::Close { fd: Operand::Var(fd) }, Bind::none());
        });
        p.root("main", main);
    });
    let mut split = whole.clone();
    let body = &mut split.bodies[0];
    let close = body.blocks[0].stmts.pop().expect("close");
    let second = body.blocks.len();
    let term = std::mem::replace(&mut body.blocks[0].term, Term::Goto(second));
    body.blocks.push(Block { stmts: vec![close], term, term_loc: Loc::new("t:3"), term_tag: None });
    assert!(alpha_eq(&whole, &whole.clone()));
    assert!(mismatch(&whole, &split).contains("statements"));
}

/// RL-INIT's classes keep their names; the namespace lower generates names
/// in is refused; two classes whose fd-inherit atoms coincide must still
/// coincide.
#[test]
fn class_renamings_are_checked() {
    let build = |a: &str, b: &str| {
        let mut p = ProgramBuilder::new("classes");
        let x = p.var("x", -1);
        let y = p.var("y", -1);
        let main = p.body("main", Vec::new(), |bb| {
            for (k, (v, class)) in [(x, a), (y, b)].into_iter().enumerate() {
                bb.event_full(
                    &format!("t:{k}"),
                    "socket",
                    Call::Socket { domain: darwin::AF_UNIX, ty: darwin::SOCK_STREAM, protocol: 0 },
                    Bind::ret(v),
                    vec![Oracle::Nominal],
                    None,
                    vec![class],
                );
            }
        });
        p.root("main", main);
        p.build()
    };
    assert!(alpha_eq(&build("first", "second"), &build("p", "q")));
    assert!(mismatch(&build("first", "second"), &build("foreign", "q")).contains("RL-INIT"));
    assert!(
        mismatch(&build("ofd_b0.0.0_0", "q"), &build("ofd_b0.0.0_0", "q")).contains("namespace")
    );
    assert!(mismatch(&build("a-b", "a_b"), &build("p", "q")).contains("atom"));
    assert!(alpha_eq(&build("a-b", "a_b"), &build("p-q", "p_q")));
    assert!(!alpha_eq(&build("first", "second"), &build("p", "p")));
}

/// A census-shaped program that differs from a hand-written one only in
/// numbering, names, locations and an unused variable and body matches it.
#[test]
fn a_fixture_and_its_twin_written_independently_match() {
    // The same three lines, written twice with different builders' numbering:
    // the twin declares an extra unused variable first and its body second.
    let one = {
        let mut p = ProgramBuilder::new("hand");
        let fd = p.var("fd", -1);
        let main = p.body("main", Vec::new(), |b| {
            b.event("hand:1", "dup", Call::Dup { fd: Operand::Lit(0) }, Bind::ret(fd));
            b.when("hand:2", Cond::ne(Operand::Var(fd), Operand::Lit(-1)), |b| {
                b.event("hand:3", "close", Call::Close { fd: Operand::Var(fd) }, Bind::none());
            });
        });
        p.root("spawn_with_two_fds", main);
        p.build()
    };
    let twin = {
        let mut p = ProgramBuilder::new("census");
        let _unused = p.var("%unused", 7);
        let v = p.var("%3", -1);
        let helper = p.declare("helper", Vec::new());
        let main = p.body("aterm_uds::spawnfd::spawn_with_two_fds", Vec::new(), |b| {
            b.event("spawnfd.rs:10:5", "dup", Call::Dup { fd: Operand::Lit(0) }, Bind::ret(v));
            b.if_(
                "spawnfd.rs:11:8",
                Cond::ne(Operand::Var(v), Operand::Lit(-1)),
                |b| {
                    b.event(
                        "spawnfd.rs:12:9",
                        "close",
                        Call::Close { fd: Operand::Var(v) },
                        Bind::none(),
                    )
                },
                |_| {},
            );
        });
        p.define(helper, |_| {});
        p.root("root", main);
        p.build()
    };
    let w = alpha_witness(&one, &twin).unwrap_or_else(|e| panic!("{e}"));
    assert_eq!(w.vars.get(&0), Some(&1));
    assert_eq!(w.bodies.get(&0), Some(&1));
}
