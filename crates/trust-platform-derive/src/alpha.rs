//! X6: alpha-equivalence of event programs (design 2026-10-01 §2.6; exit
//! criterion E4).
//!
//! The census will produce, from real trust-ir, the programs the hand
//! fixtures transcribe. A twin test compares the two, and a match deletes the
//! hand fixture. [`alpha_eq`] is that comparison. Its contract: two programs
//! it calls equal derive the same machine up to the names of its states,
//! actions and atoms, because they differ ONLY in things the derivation
//! never reads as values:
//!
//! * the numbering of variables, bodies, blocks and spawn sites;
//! * the names of open-file-description classes (a consistent renaming;
//!   the RL-INIT classes `stdio0..2` and `foreign` are fixed, and the
//!   renaming must keep two classes' atoms — `inherits_<class>` and M2's
//!   `lock_leak_<class>`, both through `property::atom` — apart iff it kept
//!   them apart before);
//! * locations, names of programs, bodies, variables, roots and sites,
//!   mutation tags, provenance, disclosures, and the text of the hand
//!   census's event assumptions (notes only) — but not WHETHER a raw
//!   `read`/`write` carries one: since M2, `lower` admits a raw read/write as
//!   the model's `ReadSome`/`WriteSome` only with it and refuses it without;
//!   an `open`'s assumption only changes the notes, so it is ignored;
//! * `Skip` statements and empty blocks that only jump on (the interpreter
//!   runs straight through both and no step reads them);
//! * unreachable blocks and bodies that are INERT (no statement, and a
//!   terminator with no operand), which no step reads either.
//!
//! Everything else must be identical, under one consistent renaming for the
//! whole program: every statement in order within its block, every operand,
//! literal, guard, oracle list, `std` row and spawn shape, every block
//! boundary (the interpreter reads the rest of a block to detect a
//! `F_DUPFD`-then-`close` move, so blocks are not merged), the roots in
//! order (each dormant or not), the descriptor parameters in order, the spawn
//! sites and their policies, and the initial value of every variable the
//! program uses. M2's constructs are compared the same way: a release mark's
//! classes in order under the class renaming, a thread start or join by its
//! root's index (roots are not renumbered), a std `File::open`'s function,
//! path, flags, result variable and class, and the M2 policies
//! (P-LOCK-RELEASE on both or neither; the same SET of fd-identity roots,
//! the set the interpreter reads).
//! Anything outside this — unreachable code with content, or a class name in
//! the namespace `lower` generates names in — is a mismatch with its reason,
//! never a silent equality. A mismatch is the safe outcome: it keeps a hand
//! fixture.
//!
//! The comparison is a lockstep walk from the roots. It never searches, so
//! it is linear in the size of the programs, and its first mismatch is
//! reported with its position in both.

use std::collections::{BTreeMap, BTreeSet};

use crate::env::{FOREIGN, STDIO_CLASSES};
use crate::program::{
    Bind, Block, BlockId, Body, BodyId, Cond, Event, EventProgram, Expr, FdInherit, FdParam, Lane,
    Operand, Policies, Root, SiteId, SpawnSite, StdCall, Stmt, StmtKind, Term, Var, VarId,
};
use crate::property::atom;

/// The renaming that makes two programs equal.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct AlphaWitness {
    /// Every variable the first program uses -> its twin.
    pub vars: BTreeMap<VarId, VarId>,
    /// Every reachable body -> its twin.
    pub bodies: BTreeMap<BodyId, BodyId>,
    /// Every spawn site -> its twin.
    pub sites: BTreeMap<SiteId, SiteId>,
    /// Every class name -> its twin (an environment over the first program
    /// applies to the second through this map).
    pub classes: BTreeMap<String, String>,
    /// Per body of the first program, every reachable block -> its twin.
    pub blocks: BTreeMap<BodyId, BTreeMap<BlockId, BlockId>>,
}

/// Why two programs are not alpha-equivalent: the first difference found.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AlphaMismatch {
    /// Where, in both programs.
    pub at: String,
    pub detail: String,
}

impl std::fmt::Display for AlphaMismatch {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}: {}", self.at, self.detail)
    }
}

/// `a` and `b` are the same program up to numbering, class names and
/// locations (the module documentation lists exactly what is ignored).
#[must_use]
pub fn alpha_eq(a: &EventProgram, b: &EventProgram) -> bool {
    alpha_witness(a, b).is_ok()
}

/// [`alpha_eq`], with the renaming that witnesses it or the first mismatch.
pub fn alpha_witness(a: &EventProgram, b: &EventProgram) -> Result<AlphaWitness, AlphaMismatch> {
    let mut m = Matcher::new(a, b);
    m.run()?;
    Ok(m.witness())
}

/// A partial bijection built pair by pair.
#[derive(Clone, Debug)]
struct Bij<K> {
    fwd: BTreeMap<K, K>,
    back: BTreeMap<K, K>,
}

impl<K: Ord + Clone + std::fmt::Debug> Bij<K> {
    fn new() -> Self {
        Bij { fwd: BTreeMap::new(), back: BTreeMap::new() }
    }

    /// Pair `x` with `y`. `Ok(true)`: a new pair.
    fn unify(&mut self, x: &K, y: &K) -> Result<bool, String> {
        match (self.fwd.get(x), self.back.get(y)) {
            (None, None) => {
                self.fwd.insert(x.clone(), y.clone());
                self.back.insert(y.clone(), x.clone());
                Ok(true)
            }
            (Some(y2), _) if y2 == y => Ok(false),
            (Some(y2), _) => Err(format!("{x:?} is already paired with {y2:?}, here with {y:?}")),
            (None, Some(x2)) => {
                Err(format!("{y:?} is already paired with {x2:?}, here with {x:?}"))
            }
        }
    }
}

/// Where a jump really lands once empty jump-only blocks are skipped.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Target {
    Block(BlockId),
    /// A cycle of empty jump-only blocks (a local loop with no step).
    Spin,
}

fn live(block: &Block) -> Vec<&Stmt> {
    block.stmts.iter().filter(|s| !matches!(s.kind, StmtKind::Skip)).collect()
}

fn jump_only(block: &Block) -> bool {
    live(block).is_empty() && matches!(block.term, Term::Goto(_))
}

/// No statement, and a terminator that reads no operand.
fn inert(block: &Block) -> bool {
    live(block).is_empty() && matches!(block.term, Term::Goto(_) | Term::Return(None))
}

fn target(body: &Body, mut b: BlockId) -> Result<Target, String> {
    let mut seen = BTreeSet::new();
    loop {
        let block = body
            .blocks
            .get(b)
            .ok_or_else(|| format!("block {b} of `{}` does not exist", body.name))?;
        let Term::Goto(next) = block.term else { return Ok(Target::Block(b)) };
        if !jump_only(block) {
            return Ok(Target::Block(b));
        }
        if !seen.insert(b) {
            return Ok(Target::Spin);
        }
        b = next;
    }
}

/// The statement kind's name, for mismatch messages.
fn kind_name(k: &StmtKind) -> &'static str {
    match k {
        StmtKind::Event(_) => "an event",
        StmtKind::Assign { .. } => "an assignment",
        StmtKind::Call { .. } => "a call",
        StmtKind::ForRange { .. } => "a descriptor loop",
        StmtKind::Fork { .. } => "a fork",
        StmtKind::Neutral { .. } => "a neutral census row",
        StmtKind::Std(s) => std_name(s),
        StmtKind::Skip => "a skip",
        StmtKind::Release { .. } => "a release mark",
        StmtKind::SpawnThread { .. } => "a thread start",
        StmtKind::Join { .. } => "a join",
    }
}

/// A `read`/`write` the program makes itself (not a std row's step): `lower`
/// admits it only with the hand census's assumption (M2).
pub(crate) fn raw_io(e: &Event) -> bool {
    e.std_origin.is_none()
        && matches!(
            e.call,
            trust_platform::Call::ReadSome { .. } | trust_platform::Call::WriteSome { .. }
        )
}

/// The std call's kind, for mismatch messages.
fn std_name(s: &StdCall) -> &'static str {
    match s {
        StdCall::Row { .. } => "a std row",
        StdCall::CommandSpawn { .. } => "a Command::spawn",
        StdCall::OpenFile { .. } => "a std File::open",
    }
}

/// A class name `lower` (or a std row expansion) may generate: an explicit
/// name there could collide with a generated one in one program and not in
/// its twin.
fn generated_namespace(name: &str) -> bool {
    name.starts_with("ofd_") || name.starts_with("STD-")
}

fn reserved(name: &str) -> bool {
    name == FOREIGN || STDIO_CLASSES.contains(&name)
}

struct Matcher<'p> {
    a: &'p EventProgram,
    b: &'p EventProgram,
    vars: Bij<VarId>,
    bodies: Bij<BodyId>,
    sites: Bij<SiteId>,
    classes: Bij<String>,
    blocks: BTreeMap<BodyId, Bij<BlockId>>,
    body_work: Vec<(BodyId, BodyId)>,
    /// The current position, for mismatch messages.
    here: String,
}

type R<T = ()> = Result<T, AlphaMismatch>;

impl<'p> Matcher<'p> {
    fn new(a: &'p EventProgram, b: &'p EventProgram) -> Self {
        Matcher {
            a,
            b,
            vars: Bij::new(),
            bodies: Bij::new(),
            sites: Bij::new(),
            classes: Bij::new(),
            blocks: BTreeMap::new(),
            body_work: Vec::new(),
            here: "program".to_string(),
        }
    }

    fn miss(&self, detail: impl Into<String>) -> AlphaMismatch {
        AlphaMismatch { at: self.here.clone(), detail: detail.into() }
    }

    fn lift<T>(&self, r: Result<T, String>) -> R<T> {
        r.map_err(|d| self.miss(d))
    }

    fn witness(&self) -> AlphaWitness {
        AlphaWitness {
            vars: self.vars.fwd.clone(),
            bodies: self.bodies.fwd.clone(),
            sites: self.sites.fwd.clone(),
            classes: self.classes.fwd.clone(),
            blocks: self.blocks.iter().map(|(b, bij)| (*b, bij.fwd.clone())).collect(),
        }
    }

    // ---- the whole program --------------------------------------------------

    fn run(&mut self) -> R {
        // Every field is named: a new one must say whether it is compared.
        let EventProgram {
            name: _,
            provenance: _,
            vars: _,
            bodies: _,
            roots: roots_a,
            sites: _,
            fd_params: params_a,
            disclosures: _,
            policies: policies_a,
        } = self.a;
        let EventProgram {
            name: _,
            provenance: _,
            vars: _,
            bodies: _,
            roots: roots_b,
            sites: _,
            fd_params: params_b,
            disclosures: _,
            policies: policies_b,
        } = self.b;
        if roots_a.len() != roots_b.len() {
            return Err(self.miss(format!("{} roots vs {}", roots_a.len(), roots_b.len())));
        }
        for (k, (ra, rb)) in roots_a.iter().zip(roots_b).enumerate() {
            let Root { name: _, body: ba, dormant: da } = ra;
            let Root { name: _, body: bb, dormant: db } = rb;
            self.here = format!("root {k}");
            if da != db {
                return Err(self.miss("a dormant thread root on one side only"));
            }
            self.body_pair(*ba, *bb)?;
        }
        self.here = "M2 policies".to_string();
        self.policies(policies_a, policies_b)?;
        if params_a.len() != params_b.len() {
            self.here = "descriptor parameters".to_string();
            return Err(self.miss(format!("{} vs {}", params_a.len(), params_b.len())));
        }
        for (k, (pa, pb)) in params_a.iter().zip(params_b).enumerate() {
            let FdParam { var: va, class: ca, peer_class: qa } = pa;
            let FdParam { var: vb, class: cb, peer_class: qb } = pb;
            self.here = format!("descriptor parameter {k}");
            self.var(*va, *vb)?;
            self.class(ca, cb)?;
            match (qa, qb) {
                (None, None) => {}
                (Some(x), Some(y)) => self.class(x, y)?,
                _ => return Err(self.miss("a peer class on one side only")),
            }
        }
        while let Some((ba, bb)) = self.body_work.pop() {
            self.body(ba, bb)?;
        }
        self.unreached_bodies()?;
        self.all_sites()?;
        self.atoms_kept_apart()
    }

    fn unreached_bodies(&mut self) -> R {
        for (side, prog, seen) in
            [("a", self.a, &self.bodies.fwd), ("b", self.b, &self.bodies.back)]
        {
            for (k, body) in prog.bodies.iter().enumerate() {
                if !seen.contains_key(&k) && !body.blocks.iter().all(inert) {
                    return Err(AlphaMismatch {
                        at: format!("{side}: body {k} `{}`", body.name),
                        detail: "a body no root reaches has content (not compared)".to_string(),
                    });
                }
            }
        }
        Ok(())
    }

    /// Sites no statement names are paired in index order; then every pair's
    /// policy is compared.
    fn all_sites(&mut self) -> R {
        self.here = "spawn sites".to_string();
        if self.a.sites.len() != self.b.sites.len() {
            return Err(self.miss(format!("{} vs {}", self.a.sites.len(), self.b.sites.len())));
        }
        let rest_a: Vec<SiteId> =
            (0..self.a.sites.len()).filter(|s| !self.sites.fwd.contains_key(s)).collect();
        let rest_b: Vec<SiteId> =
            (0..self.b.sites.len()).filter(|s| !self.sites.back.contains_key(s)).collect();
        for (x, y) in rest_a.iter().zip(&rest_b) {
            let r = self.sites.unify(x, y);
            self.lift(r)?;
        }
        let pairs: Vec<(SiteId, SiteId)> = self.sites.fwd.iter().map(|(x, y)| (*x, *y)).collect();
        let (a, b) = (self.a, self.b);
        for (x, y) in pairs {
            let SpawnSite { name: _, loc: _, policy: pa } = &a.sites[x];
            let SpawnSite { name: _, loc: _, policy: pb } = &b.sites[y];
            self.here = format!("spawn site a:{x} b:{y}");
            match (pa, pb) {
                (None, None) => {}
                (Some(fa), Some(fb)) => self.policy(fa, fb)?,
                _ => return Err(self.miss("under the fd-inherit policy on one side only")),
            }
        }
        Ok(())
    }

    /// The M2 policies: P-LOCK-RELEASE on both or neither, and the same set
    /// of fd-identity roots (`Interp::listed` reads membership; roots keep
    /// their indices).
    fn policies(&mut self, a: &Policies, b: &Policies) -> R {
        let Policies { lock_release: la, fd_identity: fa } = a;
        let Policies { lock_release: lb, fd_identity: fb } = b;
        if la != lb {
            return Err(self.miss("under P-LOCK-RELEASE on one side only"));
        }
        let (sa, sb): (BTreeSet<usize>, BTreeSet<usize>) =
            (fa.iter().copied().collect(), fb.iter().copied().collect());
        if sa != sb {
            return Err(self.miss(format!("fd-identity roots {sa:?} vs {sb:?}")));
        }
        Ok(())
    }

    fn policy(&mut self, a: &FdInherit, b: &FdInherit) -> R {
        // `lower::declared_for` reads the lanes as a map (the last lane on a
        // number wins), so that is what is compared.
        fn lanes(p: &FdInherit) -> BTreeMap<i32, &str> {
            let FdInherit { lanes } = p;
            lanes
                .iter()
                .map(|l| {
                    let Lane { fd, ofd_class } = l;
                    (*fd, ofd_class.as_str())
                })
                .collect()
        }
        let (la, lb) = (lanes(a), lanes(b));
        if la.keys().ne(lb.keys()) {
            return Err(self.miss(format!(
                "lanes on fds {:?} vs {:?}",
                la.keys().collect::<Vec<_>>(),
                lb.keys().collect::<Vec<_>>()
            )));
        }
        for (x, y) in la.values().zip(lb.values()) {
            self.class(x, y)?;
        }
        Ok(())
    }

    /// Two classes have the same atom (`inherits_<class>`, and M2's
    /// `lock_leak_<class>`: both `property::atom` of the name) in one
    /// program iff their twins do in the other. RL-INIT's own classes and
    /// `?` (the class `property` names a description with none) count.
    fn atoms_kept_apart(&mut self) -> R {
        self.here = "class atoms".to_string();
        let mut map: BTreeMap<String, String> = BTreeMap::new();
        let mut back: BTreeMap<String, String> = BTreeMap::new();
        let fixed =
            STDIO_CLASSES.iter().chain([&FOREIGN, &"?"]).map(|c| (c.to_string(), c.to_string()));
        for (x, y) in self.classes.fwd.clone().into_iter().chain(fixed) {
            let (ax, ay) = (atom(&x), atom(&y));
            if map.get(&ax).is_some_and(|v| *v != ay) || back.get(&ay).is_some_and(|v| *v != ax) {
                return Err(self.miss(format!(
                    "class `{x}` -> `{y}` merges or splits the fd-inherit atom `inherits_{ax}`"
                )));
            }
            map.insert(ax.clone(), ay.clone());
            back.insert(ay, ax);
        }
        Ok(())
    }

    // ---- names ----------------------------------------------------------------

    fn var(&mut self, x: VarId, y: VarId) -> R {
        let (a, b) = (self.a, self.b);
        let (Some(va), Some(vb)) = (a.vars.get(x), b.vars.get(y)) else {
            return Err(self.miss(format!("variable a:{x} or b:{y} does not exist")));
        };
        let r = self.vars.unify(&x, &y);
        if self.lift(r)? {
            let Var { name: _, init: ia } = va;
            let Var { name: _, init: ib } = vb;
            if ia != ib {
                return Err(self.miss(format!(
                    "variable `{}` starts at {ia}, its twin `{}` at {ib}",
                    va.name, vb.name
                )));
            }
        }
        Ok(())
    }

    fn opt_var(&mut self, x: Option<VarId>, y: Option<VarId>) -> R {
        match (x, y) {
            (None, None) => Ok(()),
            (Some(x), Some(y)) => self.var(x, y),
            _ => Err(self.miss("a result variable on one side only")),
        }
    }

    fn class(&mut self, x: &str, y: &str) -> R {
        for n in [x, y] {
            if generated_namespace(n) {
                return Err(self.miss(format!(
                    "class `{n}` is in the namespace lower generates class names in (`ofd_`, \
                     `STD-`); it could collide there in one program and not in the other"
                )));
            }
        }
        if (reserved(x) || reserved(y)) && x != y {
            return Err(
                self.miss(format!("class `{x}` vs `{y}`: RL-INIT's own classes are not renamed"))
            );
        }
        let r = self.classes.unify(&x.to_string(), &y.to_string());
        self.lift(r).map(|_| ())
    }

    fn classes(&mut self, x: &[String], y: &[String]) -> R {
        if x.len() != y.len() {
            return Err(self.miss(format!("{} class names vs {}", x.len(), y.len())));
        }
        for (p, q) in x.iter().zip(y) {
            self.class(p, q)?;
        }
        Ok(())
    }

    fn site(&mut self, x: SiteId, y: SiteId) -> R {
        if x >= self.a.sites.len() || y >= self.b.sites.len() {
            return Err(self.miss(format!("site a:{x} or b:{y} does not exist")));
        }
        let r = self.sites.unify(&x, &y);
        self.lift(r).map(|_| ())
    }

    fn opt_site(&mut self, x: Option<SiteId>, y: Option<SiteId>) -> R {
        match (x, y) {
            (None, None) => Ok(()),
            (Some(x), Some(y)) => self.site(x, y),
            _ => Err(self.miss("a spawn site on one side only")),
        }
    }

    fn body_pair(&mut self, x: BodyId, y: BodyId) -> R {
        if x >= self.a.bodies.len() || y >= self.b.bodies.len() {
            return Err(self.miss(format!("body a:{x} or b:{y} does not exist")));
        }
        let r = self.bodies.unify(&x, &y);
        if self.lift(r)? {
            self.body_work.push((x, y));
        }
        Ok(())
    }

    // ---- values ----------------------------------------------------------------

    fn operand(&mut self, x: &Operand, y: &Operand) -> R {
        match (x, y) {
            (Operand::Lit(p), Operand::Lit(q)) if p == q => Ok(()),
            (Operand::Var(p), Operand::Var(q)) => self.var(*p, *q),
            _ => Err(self.miss(format!("operand {x:?} vs {y:?}"))),
        }
    }

    fn opt_operand(&mut self, x: Option<&Operand>, y: Option<&Operand>) -> R {
        match (x, y) {
            (None, None) => Ok(()),
            (Some(x), Some(y)) => self.operand(x, y),
            _ => Err(self.miss("an operand on one side only")),
        }
    }

    fn expr(&mut self, x: &Expr, y: &Expr) -> R {
        let mismatch = || format!("expression {x:?} vs {y:?}");
        match x {
            Expr::Use(p) => {
                let Expr::Use(q) = y else { return Err(self.miss(mismatch())) };
                self.operand(p, q)
            }
            Expr::Add(p1, p2) => {
                let Expr::Add(q1, q2) = y else { return Err(self.miss(mismatch())) };
                self.operand(p1, q1)?;
                self.operand(p2, q2)
            }
            Expr::Min(p1, p2) => {
                let Expr::Min(q1, q2) = y else { return Err(self.miss(mismatch())) };
                self.operand(p1, q1)?;
                self.operand(p2, q2)
            }
            Expr::BitAnd(p1, p2) => {
                let Expr::BitAnd(q1, q2) = y else { return Err(self.miss(mismatch())) };
                self.operand(p1, q1)?;
                self.operand(p2, q2)
            }
            Expr::Opaque => match y {
                Expr::Opaque => Ok(()),
                _ => Err(self.miss(mismatch())),
            },
        }
    }

    fn cond(&mut self, x: &Cond, y: &Cond) -> R {
        let mismatch = || format!("guard {x:?} vs {y:?}");
        match x {
            Cond::Cmp(op, p1, p2) => {
                let Cond::Cmp(oq, q1, q2) = y else { return Err(self.miss(mismatch())) };
                if op != oq {
                    return Err(self.miss(mismatch()));
                }
                self.operand(p1, q1)?;
                self.operand(p2, q2)
            }
            Cond::And(p1, p2) => {
                let Cond::And(q1, q2) = y else { return Err(self.miss(mismatch())) };
                self.cond(p1, q1)?;
                self.cond(p2, q2)
            }
            Cond::Or(p1, p2) => {
                let Cond::Or(q1, q2) = y else { return Err(self.miss(mismatch())) };
                self.cond(p1, q1)?;
                self.cond(p2, q2)
            }
            Cond::Not(p) => {
                let Cond::Not(q) = y else { return Err(self.miss(mismatch())) };
                self.cond(p, q)
            }
            Cond::Const(p) => match y {
                Cond::Const(q) if p == q => Ok(()),
                _ => Err(self.miss(mismatch())),
            },
            Cond::Nondet => match y {
                Cond::Nondet => Ok(()),
                _ => Err(self.miss(mismatch())),
            },
        }
    }

    // ---- statements ---------------------------------------------------------------

    fn bind(&mut self, x: &Bind, y: &Bind) -> R {
        let Bind { ret: r1, ret2: s1, rlim_soft: l1 } = x;
        let Bind { ret: r2, ret2: s2, rlim_soft: l2 } = y;
        self.opt_var(*r1, *r2)?;
        self.opt_var(*s1, *s2)?;
        self.opt_var(*l1, *l2)
    }

    fn event(&mut self, x: &Event, y: &Event) -> R {
        let Event {
            symbol: sym_a,
            call: call_a,
            bind: bind_a,
            oracles: or_a,
            site: site_a,
            ofd_names: names_a,
            std_origin: origin_a,
            path: path_a,
            assumption: why_a,
        } = x;
        let Event {
            symbol: sym_b,
            call: call_b,
            bind: bind_b,
            oracles: or_b,
            site: site_b,
            ofd_names: names_b,
            std_origin: origin_b,
            path: path_b,
            assumption: why_b,
        } = y;
        if sym_a != sym_b {
            return Err(self.miss(format!("symbol `{sym_a}` vs `{sym_b}`")));
        }
        // Everything but the operands, then the operands in order.
        if call_a.map(|_| ()) != call_b.map(|_| ()) {
            return Err(self.miss(format!("call {call_a:?} vs {call_b:?}")));
        }
        let (mut ops_a, mut ops_b) = (Vec::new(), Vec::new());
        let _ = call_a.map(|o| ops_a.push(*o));
        let _ = call_b.map(|o| ops_b.push(*o));
        for (p, q) in ops_a.iter().zip(&ops_b) {
            self.operand(p, q)?;
        }
        self.bind(bind_a, bind_b)?;
        if or_a != or_b {
            return Err(self.miss(format!("oracles {or_a:?} vs {or_b:?}")));
        }
        self.opt_site(*site_a, *site_b)?;
        self.classes(names_a, names_b)?;
        if origin_a != origin_b {
            return Err(self.miss(format!("std origin {origin_a:?} vs {origin_b:?}")));
        }
        if path_a != path_b {
            return Err(self.miss(format!("path {path_a:?} vs {path_b:?}")));
        }
        // M2: a raw read/write is admitted only with the hand census's
        // assumption (`lower`), so its PRESENCE decides the derivation; its
        // text is notes only.
        if raw_io(x) && why_a.is_some() != why_b.is_some() {
            return Err(self.miss(format!(
                "a raw `{sym_a}` with the census's assumption on one side only (lower admits it \
                 only with one)"
            )));
        }
        Ok(())
    }

    fn std(&mut self, x: &StdCall, y: &StdCall) -> R {
        let differ = |m: &Self| m.miss(format!("{} vs {}", std_name(x), std_name(y)));
        match x {
            StdCall::Row { path, args, bind, ofd_names } => {
                let StdCall::Row { path: p2, args: a2, bind: b2, ofd_names: n2 } = y else {
                    return Err(differ(self));
                };
                if path != p2 {
                    return Err(self.miss(format!("std row `{path}` vs `{p2}`")));
                }
                if args.len() != a2.len() || bind.len() != b2.len() {
                    return Err(self.miss("std row arity"));
                }
                for (p, q) in args.iter().zip(a2) {
                    self.operand(p, q)?;
                }
                for (p, q) in bind.iter().zip(b2) {
                    self.var(*p, *q)?;
                }
                self.classes(ofd_names, n2)
            }
            StdCall::CommandSpawn { stdio, shape, pre_exec, site, bind } => {
                let StdCall::CommandSpawn {
                    stdio: io2,
                    shape: sh2,
                    pre_exec: pe2,
                    site: si2,
                    bind: b2,
                } = y
                else {
                    return Err(differ(self));
                };
                if stdio != io2 || shape != sh2 {
                    return Err(self.miss(format!(
                        "spawn stdio/shape {stdio:?} {shape:?} vs {io2:?} {sh2:?}"
                    )));
                }
                if pre_exec.len() != pe2.len() {
                    return Err(self.miss("number of pre_exec closures"));
                }
                for (p, q) in pre_exec.iter().zip(pe2) {
                    self.body_pair(*p, *q)?;
                }
                self.site(*site, *si2)?;
                self.opt_var(*bind, *b2)
            }
            StdCall::OpenFile { std_fn, file, flags, bind, ofd_name } => {
                let StdCall::OpenFile { std_fn: f2, file: p2, flags: l2, bind: b2, ofd_name: n2 } =
                    y
                else {
                    return Err(differ(self));
                };
                if std_fn != f2 || file != p2 || flags != l2 {
                    return Err(self.miss(format!(
                        "std open `{std_fn}`({file:?}, {flags:#x}) vs `{f2}`({p2:?}, {l2:#x})"
                    )));
                }
                self.var(*bind, *b2)?;
                self.class(ofd_name, n2)
            }
        }
    }

    fn stmt(&mut self, x: &Stmt, y: &Stmt) -> R {
        let Stmt { kind: kx, loc: _, tag: _ } = x;
        let Stmt { kind: ky, loc: _, tag: _ } = y;
        let differ = |m: &Self| m.miss(format!("{} vs {}", kind_name(kx), kind_name(ky)));
        match kx {
            StmtKind::Event(ea) => {
                let StmtKind::Event(eb) = ky else { return Err(differ(self)) };
                self.event(ea, eb)
            }
            StmtKind::Assign { var, expr } => {
                let StmtKind::Assign { var: v2, expr: e2 } = ky else { return Err(differ(self)) };
                self.var(*var, *v2)?;
                self.expr(expr, e2)
            }
            StmtKind::Call { body, args, ret } => {
                let StmtKind::Call { body: b2, args: a2, ret: r2 } = ky else {
                    return Err(differ(self));
                };
                self.body_pair(*body, *b2)?;
                if args.len() != a2.len() {
                    return Err(self.miss("call arity"));
                }
                for ((p, o), (q, o2)) in args.iter().zip(a2) {
                    self.var(*p, *q)?;
                    self.operand(o, o2)?;
                }
                self.opt_var(*ret, *r2)
            }
            StmtKind::ForRange { var, lo, hi, body } => {
                let StmtKind::ForRange { var: v2, lo: l2, hi: h2, body: b2 } = ky else {
                    return Err(differ(self));
                };
                self.var(*var, *v2)?;
                self.operand(lo, l2)?;
                self.operand(hi, h2)?;
                self.body_pair(*body, *b2)
            }
            StmtKind::Fork { child, site, bind, std_origin } => {
                let StmtKind::Fork { child: c2, site: s2, bind: b2, std_origin: o2 } = ky else {
                    return Err(differ(self));
                };
                if std_origin != o2 {
                    return Err(self.miss(format!("fork origin {std_origin:?} vs {o2:?}")));
                }
                self.body_pair(*child, *c2)?;
                self.site(*site, *s2)?;
                self.opt_var(*bind, *b2)
            }
            StmtKind::Neutral { symbol } => match ky {
                StmtKind::Neutral { symbol: s2 } if symbol == s2 => Ok(()),
                StmtKind::Neutral { symbol: s2 } => {
                    Err(self.miss(format!("neutral `{symbol}` vs `{s2}`")))
                }
                _ => Err(differ(self)),
            },
            StmtKind::Std(sx) => {
                let StmtKind::Std(sy) = ky else { return Err(differ(self)) };
                self.std(sx, sy)
            }
            StmtKind::Skip => match ky {
                StmtKind::Skip => Ok(()),
                _ => Err(differ(self)),
            },
            StmtKind::Release { classes } => {
                let StmtKind::Release { classes: c2 } = ky else { return Err(differ(self)) };
                self.classes(classes, c2)
            }
            // Roots are compared in order, never renumbered: a thread start or
            // join names the same root index on both sides.
            StmtKind::SpawnThread { root } => match ky {
                StmtKind::SpawnThread { root: r2 } if root == r2 => Ok(()),
                StmtKind::SpawnThread { root: r2 } => {
                    Err(self.miss(format!("thread start of root {root} vs {r2}")))
                }
                _ => Err(differ(self)),
            },
            StmtKind::Join { root } => match ky {
                StmtKind::Join { root: r2 } if root == r2 => Ok(()),
                StmtKind::Join { root: r2 } => {
                    Err(self.miss(format!("join of root {root} vs {r2}")))
                }
                _ => Err(differ(self)),
            },
        }
    }

    // ---- bodies and blocks ------------------------------------------------------------

    fn body(&mut self, ba: BodyId, bb: BodyId) -> R {
        let (a, b) = (self.a, self.b);
        let (body_a, body_b) = (&a.bodies[ba], &b.bodies[bb]);
        let Body { name: na, params: pa, blocks: ka } = body_a;
        let Body { name: nb, params: pb, blocks: kb } = body_b;
        self.here = format!("a: body {ba} `{na}` / b: body {bb} `{nb}`");
        if pa.len() != pb.len() {
            return Err(self.miss("number of parameters"));
        }
        for (p, q) in pa.iter().zip(pb) {
            self.var(*p, *q)?;
        }
        // `body_work` hands each pair over once (the body renaming is a
        // bijection), so its blocks start unpaired.
        let mut blocks = Bij::new();
        if ka.is_empty() || kb.is_empty() {
            if ka.is_empty() && kb.is_empty() {
                self.blocks.insert(ba, blocks);
                return Ok(());
            }
            return Err(self.miss("a body without blocks on one side only"));
        }
        let entry = (self.lift(target(body_a, 0))?, self.lift(target(body_b, 0))?);
        let mut work = vec![entry];
        while let Some((ta, tb)) = work.pop() {
            let (x, y) = match (ta, tb) {
                (Target::Spin, Target::Spin) => continue,
                (Target::Block(x), Target::Block(y)) => (x, y),
                _ => {
                    return Err(self.miss(format!(
                        "a jump lands on {ta:?} in a and {tb:?} in b (an empty loop on one side \
                         only)"
                    )));
                }
            };
            let r = blocks.unify(&x, &y);
            if !self.lift(r)? {
                continue;
            }
            let (xa, xb) = (&ka[x], &kb[y]);
            let (sa, sb) = (live(xa), live(xb));
            self.here = format!("a: `{na}` bb{x} / b: `{nb}` bb{y}");
            if sa.len() != sb.len() {
                return Err(self.miss(format!("{} statements vs {}", sa.len(), sb.len())));
            }
            for (k, (s, t)) in sa.iter().zip(&sb).enumerate() {
                self.here = format!("a: `{na}` bb{x} stmt {k} / b: `{nb}` bb{y} stmt {k}");
                self.stmt(s, t)?;
            }
            self.here = format!("a: `{na}` bb{x} terminator / b: `{nb}` bb{y} terminator");
            let Block { stmts: _, term: term_a, term_loc: _, term_tag: _ } = xa;
            let Block { stmts: _, term: term_b, term_loc: _, term_tag: _ } = xb;
            let mut next = Vec::new();
            match term_a {
                Term::Goto(p) => {
                    let Term::Goto(q) = term_b else {
                        return Err(self.miss(format!("terminator {term_a:?} vs {term_b:?}")));
                    };
                    next.push((*p, *q));
                }
                Term::Branch { cond, then, els } => {
                    let Term::Branch { cond: c2, then: t2, els: e2 } = term_b else {
                        return Err(self.miss(format!("terminator {term_a:?} vs {term_b:?}")));
                    };
                    self.cond(cond, c2)?;
                    next.push((*then, *t2));
                    next.push((*els, *e2));
                }
                Term::Return(op) => {
                    let Term::Return(o2) = term_b else {
                        return Err(self.miss(format!("terminator {term_a:?} vs {term_b:?}")));
                    };
                    self.opt_operand(op.as_ref(), o2.as_ref())?;
                }
            }
            // Successors in reverse, so the walk takes the then-arm first.
            for (p, q) in next.into_iter().rev() {
                work.push((self.lift(target(body_a, p))?, self.lift(target(body_b, q))?));
            }
        }
        // What the walk did not reach must be inert.
        for (side, body, seen) in [("a", body_a, &blocks.fwd), ("b", body_b, &blocks.back)] {
            for (k, block) in body.blocks.iter().enumerate() {
                if !seen.contains_key(&k) && !inert(block) {
                    return Err(AlphaMismatch {
                        at: format!("{side}: `{}` bb{k}", body.name),
                        detail: "an unreachable block has content (not compared)".to_string(),
                    });
                }
            }
        }
        self.blocks.insert(ba, blocks);
        Ok(())
    }
}

#[cfg(test)]
mod tests;
