//! The event program: the input of the derivation (plan D1/D2).
//!
//! This is the shape the THIR -> trust-ir census is meant to produce: per
//! function body a control-flow graph whose statements are platform events
//! (clause calls, std summary calls, spawn sites), local scalar assignments
//! and calls, and whose terminators branch on tracked scalars. Until the
//! producer lowers the aterm-uds bodies (plan P1-P3), fixtures are written in
//! it by hand ([`crate::fixtures`]); every statement carries the source
//! location it was transcribed from.
//!
//! Two layers:
//!
//! * the **surface** a fixture writes, which may call std functions by path
//!   ([`StdCall`]): `UnixStream::pair`, `Command::spawn` on either Darwin path;
//! * the **core** the derivation runs, produced by [`crate::lower`], in which
//!   every std call has been replaced by the events of its trust-platform
//!   summary row (`trust_platform::std_summaries`), a fork-path spawn has
//!   become a [`StmtKind::Fork`] whose child body runs std's child steps, the
//!   registered `pre_exec` closures and `execvp`.
//!
//! Interleaving points are exactly the platform events (D2): [`Event`],
//! [`StmtKind::Fork`] and [`StmtKind::ForRange`] (the strip loop, one step
//! per SD-3), and thread start and join ([`StmtKind::SpawnThread`],
//! [`StmtKind::Join`], M2). Assignments, local calls, branches and release
//! markers ([`StmtKind::Release`]) are not.
//!
//! **What the census could not track (X1).** A value the census lost is
//! [`Expr::Opaque`]; a guard it cannot evaluate is [`Cond::Nondet`]. Each
//! declares its approximation direction (Critique C-1):
//!
//! * `Expr::Opaque` is EXACT: [`crate::lower`] refuses
//!   ([`crate::lower::LowerError::Untracked`]) any program in which an
//!   untracked value can reach an event operand, a guard or a loop bound
//!   ([`crate::track`]), so the value the model gives it decides nothing.
//! * `Cond::Nondet` OVER-approximates: both arms are explored, each as an
//!   explicit choice step ([`crate::nondet`]) that a replayed trace lists
//!   ([`crate::trace::Replay::overapprox`]); a refutation that relies on one
//!   is not an error (C-9: `PC-OVERAPPROX`).
//!
//! [`alpha_eq`] (X6, [`crate::alpha`]) decides whether two programs are the
//! same program up to the numbering of variables, bodies, blocks and sites,
//! the names of allocation classes, and locations — the twin check of a
//! census-produced program against a hand fixture (exit criterion E4).

use trust_platform::std_summaries::{CommandShape, StdioPlan};
use trust_platform::{Call, Oracle};

pub use crate::alpha::{AlphaMismatch, AlphaWitness, alpha_eq, alpha_witness};

pub type VarId = usize;
pub type BodyId = usize;
pub type BlockId = usize;
pub type SiteId = usize;

/// Where a statement was transcribed from (`repo@commit:path:line`).
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Loc(pub String);

impl Loc {
    #[must_use]
    pub fn new(s: impl Into<String>) -> Loc {
        Loc(s.into())
    }
}

impl std::fmt::Display for Loc {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}

/// A scalar operand: a literal or a tracked variable.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Operand {
    Lit(i64),
    Var(VarId),
}

/// A scalar expression (enough for `inherited_fd_ceiling` and loop counters).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Expr {
    Use(Operand),
    Add(Operand, Operand),
    Min(Operand, Operand),
    /// `x & y` (a flag test: `flags & O_ACCMODE`, `fd_flags & FD_CLOEXEC`).
    BitAnd(Operand, Operand),
    /// X1: a value the census did not track (a call it summarizes as
    /// "some scalar", an unsupported operation, a non-descriptor argument of
    /// the root). Exact, not an approximation: [`crate::lower`] refuses the
    /// program if such a value — directly or through assignments, calls and
    /// returns — can reach an event operand, a branch guard (an untracked
    /// guard must be written [`Cond::Nondet`]) or a `ForRange` bound.
    Opaque,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CmpOp {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

/// A branch guard over tracked scalars.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Cond {
    Cmp(CmpOp, Operand, Operand),
    And(Box<Cond>, Box<Cond>),
    Or(Box<Cond>, Box<Cond>),
    Not(Box<Cond>),
    Const(bool),
    /// X1: a guard the census could not evaluate (D2: an unsliced value that
    /// reaches a guard becomes an oracle choice). Three-valued inside
    /// `And`/`Or`/`Not` (Kleene); when the whole guard is undecided the
    /// branch is a choice step and BOTH arms are explored
    /// ([`crate::nondet`]). This over-approximates the program: every replayed
    /// trace lists the choices it took ([`crate::trace::Replay::overapprox`]).
    Nondet,
}

impl Cond {
    #[must_use]
    pub fn eq(a: Operand, b: Operand) -> Cond {
        Cond::Cmp(CmpOp::Eq, a, b)
    }
    #[must_use]
    pub fn ne(a: Operand, b: Operand) -> Cond {
        Cond::Cmp(CmpOp::Ne, a, b)
    }
    #[must_use]
    pub fn or(a: Cond, b: Cond) -> Cond {
        Cond::Or(Box::new(a), Box::new(b))
    }
}

/// Where an event's result goes. A failed call binds `-1` to `ret` and
/// `ret2` (the C convention the transcribed code tests).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Bind {
    /// Component 0 of the result (`int` return, first descriptor of a pair,
    /// `0` for `getrlimit`/`execve` success), or `-1`.
    pub ret: Option<VarId>,
    /// Component 1 of a `pipe`/`socketpair` result.
    pub ret2: Option<VarId>,
    /// `getrlimit`'s soft limit.
    pub rlim_soft: Option<VarId>,
}

impl Bind {
    #[must_use]
    pub fn none() -> Bind {
        Bind::default()
    }
    #[must_use]
    pub fn ret(v: VarId) -> Bind {
        Bind { ret: Some(v), ..Bind::default() }
    }
    #[must_use]
    pub fn pair(a: VarId, b: VarId) -> Bind {
        Bind { ret: Some(a), ret2: Some(b), ..Bind::default() }
    }
}

/// A std summary row step an event was expanded from.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StdOrigin {
    pub row: &'static str,
    pub step: usize,
    pub source: &'static str,
}

/// One platform event: a call to one `trust_platform` clause.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Event {
    /// The symbol the census saw (`fcntl`, `_dup2`, `execvp`, …); looked up
    /// in `trust_platform::symbols` (I-FD-SPECIFIED).
    pub symbol: String,
    pub call: Call<Operand>,
    pub bind: Bind,
    /// The oracle choices the exploration takes (each must be admissible).
    pub oracles: Vec<Oracle>,
    /// The spawn site, for `posix_spawn` events.
    pub site: Option<SiteId>,
    /// Names of the open-file-description classes this event allocates, by
    /// result component (allocation-site abstraction of D7).
    pub ofd_names: Vec<String>,
    /// Set when the event is a step of a std summary row.
    pub std_origin: Option<StdOrigin>,
    /// The literal path of an `open` event, as the census read it
    /// (classified by `trust_platform::symbols::classify_open_path`).
    pub path: Option<String>,
    /// For an `open` of a path the census classifies as `Other`: the hand
    /// census's own statement of what the path names and why the model's
    /// fresh-vnode clause is its descriptor effect, printed into the model's
    /// notes IN PLACE OF the default fresh-vnode assumption (which would be
    /// false for, e.g., a FIFO opened so that it cannot block).
    pub assumption: Option<String>,
}

/// A std function called by path; lowered to its summary row's events.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StdCall {
    /// A fixed row (`std_summaries::row(id)`, looked up by `path`); `args`
    /// are the row's `Arg(i)` operands, `bind` receives its returns.
    Row { path: String, args: Vec<Operand>, bind: Vec<VarId>, ofd_names: Vec<String> },
    /// `Command::spawn`. std picks the row from the command's shape
    /// (`trust_platform::std_summaries::spawn_path`): STD-SPAWN-FORK or
    /// STD-SPAWN-POSIX. `pre_exec` closures are bodies taking no parameters
    /// and returning `0` (Ok) or `-1` (Err), run in registration order; a
    /// non-empty list sets the shape's `pre_exec`. `bind` receives the child
    /// pid, or `-1` when the spawn returned `Err`.
    CommandSpawn {
        stdio: [StdioPlan; 3],
        shape: CommandShape,
        pre_exec: Vec<BodyId>,
        site: SiteId,
        bind: Option<VarId>,
    },
    /// `std::fs::File::open`/`create`/`OpenOptions::open` (`std_fn`) of a
    /// path the namespace resolves: STD-OPEN's step as a named open
    /// (`trust_platform::std_summaries::std_open_path`), `flags` without the
    /// `O_CLOEXEC` std adds. `bind` receives the descriptor or `-1`.
    OpenFile { std_fn: String, file: String, flags: i32, bind: VarId, ofd_name: String },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StmtKind {
    Event(Event),
    Assign {
        var: VarId,
        expr: Expr,
    },
    /// A call to another body of the program, inlined (non-recursive).
    Call {
        body: BodyId,
        args: Vec<(VarId, Operand)>,
        ret: Option<VarId>,
    },
    /// `for var in lo..hi { body }` where the body is table-local (the
    /// strip loop). One step (SD-3); allowed only in a forked child.
    ForRange {
        var: VarId,
        lo: Operand,
        hi: Operand,
        body: BodyId,
    },
    /// `fork(2)`: produced from STD-SPAWN-FORK (`std_origin` set), or a raw
    /// libc `fork` the program calls itself ([`BodyBuilder::fork`]). The
    /// child starts `child` with a copy of the forking actor's variables.
    Fork {
        child: BodyId,
        site: SiteId,
        bind: Option<VarId>,
        std_origin: Option<StdOrigin>,
    },
    /// A census row with no platform effect (spawn-attribute builders,
    /// `as_raw_fd`, `pre_exec` registration): its symbol must look up as
    /// `Neutral` or a spawn builder.
    Neutral {
        symbol: String,
    },
    /// Surface only.
    Std(StdCall),
    /// A statement a mutant deleted.
    Skip,
    /// P-LOCK-RELEASE (M2): the program's statement that, from here on, it
    /// holds no `flock` lock on the open file descriptions of these
    /// allocation classes — the owner's release point (a function's return
    /// after its close, a test's `release(file)`). Local: it marks the state
    /// the preceding event left, it is not an event itself.
    Release {
        classes: Vec<String>,
    },
    /// `std::thread::spawn` (M2): start thread root `root`, dormant until
    /// now, with a copy of the spawning actor's variables (the closure's
    /// captures). One `pthread_create` event of the process.
    SpawnThread {
        root: usize,
    },
    /// `JoinHandle::join` (M2): wait until thread root `root` has finished.
    /// Not enabled until it has.
    Join {
        root: usize,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Stmt {
    pub kind: StmtKind,
    pub loc: Loc,
    /// A stable name for the mutant sweep (fd-hygiene steps carry one).
    pub tag: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Term {
    Goto(BlockId),
    Branch { cond: Cond, then: BlockId, els: BlockId },
    Return(Option<Operand>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Block {
    pub stmts: Vec<Stmt>,
    pub term: Term,
    pub term_loc: Loc,
    pub term_tag: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Body {
    pub name: String,
    pub params: Vec<VarId>,
    pub blocks: Vec<Block>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Var {
    pub name: String,
    pub init: i64,
}

/// A thread root: a concurrent event source of the root process. Root 0 is
/// the function under the policy; the others are the program's other
/// threads (D4: used for refutation).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Root {
    pub name: String,
    pub body: BodyId,
    /// Started by a [`StmtKind::SpawnThread`] of another actor, not at the
    /// program's start (M2).
    pub dormant: bool,
}

/// The M2 policies a program is checked under (fd-inherit is per spawn
/// site, [`SpawnSite::policy`]).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Policies {
    /// P-LOCK-RELEASE: after the owner's release point
    /// ([`StmtKind::Release`]), no OTHER process may still hold the `flock`
    /// lock of a released class's description (a child that inherited the
    /// locked descriptor violates it).
    pub lock_release: bool,
    /// fd-identity: the thread roots whose operations on descriptor NUMBERS
    /// are checked: each must reach the open file description the actor last
    /// bound to (or observed at) that number — or none, when it closed it.
    pub fd_identity: Vec<usize>,
}

/// The P-FD-INHERIT policy on one spawn site.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FdInherit {
    /// Descriptors the child must hold at exec, each naming the open file
    /// description of the given class (e.g. fd 3 names `first`'s).
    pub lanes: Vec<Lane>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Lane {
    pub fd: i32,
    pub ofd_class: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SpawnSite {
    pub name: String,
    pub loc: Loc,
    /// `None`: the site is not under the policy (another component's spawn).
    pub policy: Option<FdInherit>,
}

/// A descriptor the program receives as an argument (an `OwnedFd`
/// parameter): RL-INIT places it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FdParam {
    pub var: VarId,
    /// Its open-file-description class (what a lane names).
    pub class: String,
    /// The class of its socketpair peer, which the root also holds
    /// (close-on-exec), if any.
    pub peer_class: Option<String>,
}

/// Where a fixture's code came from.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Provenance {
    pub repo: String,
    pub commit: String,
    pub path: String,
    pub what: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EventProgram {
    pub name: String,
    pub provenance: Vec<Provenance>,
    pub vars: Vec<Var>,
    pub bodies: Vec<Body>,
    pub roots: Vec<Root>,
    pub sites: Vec<SpawnSite>,
    pub fd_params: Vec<FdParam>,
    /// What a hand-written program leaves out or evaluates by hand, said in
    /// words (calls with no descriptor-table effect the symbol table does not
    /// model, constants read from the environment, …); printed into every
    /// derived model's notes. Empty for a census-produced program.
    pub disclosures: Vec<String>,
    /// The M2 policies (none for an M1 program).
    pub policies: Policies,
}

/// A position in a body: `(body, block, statement index)`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct StmtRef {
    pub body: BodyId,
    pub block: BlockId,
    pub idx: usize,
}

impl std::fmt::Display for StmtRef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "b{}.{}.{}", self.body, self.block, self.idx)
    }
}

impl EventProgram {
    /// Record one more source this program was read from.
    pub fn add_provenance(&mut self, repo: &str, commit: &str, path: &str, what: &str) {
        self.provenance.push(Provenance {
            repo: repo.to_string(),
            commit: commit.to_string(),
            path: path.to_string(),
            what: what.to_string(),
        });
    }

    #[must_use]
    pub fn stmt(&self, at: StmtRef) -> Option<&Stmt> {
        self.bodies.get(at.body)?.blocks.get(at.block)?.stmts.get(at.idx)
    }

    #[must_use]
    pub fn var_id(&self, name: &str) -> Option<VarId> {
        self.vars.iter().position(|v| v.name == name)
    }

    /// Every statement, with its position.
    pub fn stmts(&self) -> impl Iterator<Item = (StmtRef, &Stmt)> {
        self.bodies.iter().enumerate().flat_map(|(b, body)| {
            body.blocks.iter().enumerate().flat_map(move |(k, block)| {
                block
                    .stmts
                    .iter()
                    .enumerate()
                    .map(move |(i, s)| (StmtRef { body: b, block: k, idx: i }, s))
            })
        })
    }
}

/// A deliberate deletion of one fd-hygiene step (the mutant sweep).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Mutation {
    /// Replace every statement tagged `tag` with `Skip`.
    DeleteStmt(String),
    /// Make the branch tagged `tag` always take its else edge (deletes the
    /// then-arm).
    DeleteThen(String),
    /// Clear `flag` from the `posix_spawn` event tagged `tag`.
    ClearSpawnFlag { tag: String, flag: i32 },
    /// Replace the event tagged `tag` by a call of `symbol` (reverting a fix
    /// that changed which call a statement makes: an identity query back to a
    /// flag query).
    ReplaceCall { tag: String, symbol: String, call: Call<Operand> },
}

impl Mutation {
    #[must_use]
    pub fn name(&self) -> String {
        match self {
            Mutation::DeleteStmt(t) => format!("delete `{t}`"),
            Mutation::DeleteThen(t) => format!("delete the then-arm of `{t}`"),
            Mutation::ClearSpawnFlag { tag, flag } => format!("clear flag {flag:#x} on `{tag}`"),
            Mutation::ReplaceCall { tag, symbol, .. } => format!("make `{tag}` a `{symbol}` call"),
        }
    }
}

/// Why a mutation could not be applied.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MutationMissed(pub String);

impl EventProgram {
    /// Apply one mutation to a surface or core program. Fails when the tag
    /// names nothing, so a sweep cannot silently test the unmutated program.
    pub fn mutate(&self, m: &Mutation) -> Result<EventProgram, MutationMissed> {
        let mut p = self.clone();
        let mut hit = false;
        for body in &mut p.bodies {
            for block in &mut body.blocks {
                match m {
                    Mutation::DeleteStmt(tag) => {
                        for s in &mut block.stmts {
                            if s.tag.as_deref() == Some(tag) {
                                s.kind = StmtKind::Skip;
                                hit = true;
                            }
                        }
                    }
                    Mutation::DeleteThen(tag) => {
                        if block.term_tag.as_deref() == Some(tag)
                            && let Term::Branch { cond, .. } = &mut block.term
                        {
                            *cond = Cond::Const(false);
                            hit = true;
                        }
                    }
                    Mutation::ClearSpawnFlag { tag, flag } => {
                        for s in &mut block.stmts {
                            if s.tag.as_deref() == Some(tag)
                                && let StmtKind::Event(Event {
                                    call: Call::Spawn { flags, .. },
                                    ..
                                }) = &mut s.kind
                                && *flags & *flag != 0
                            {
                                *flags &= !*flag;
                                hit = true;
                            }
                        }
                    }
                    Mutation::ReplaceCall { tag, symbol, call } => {
                        for s in &mut block.stmts {
                            if s.tag.as_deref() == Some(tag)
                                && let StmtKind::Event(ev) = &mut s.kind
                            {
                                ev.symbol.clone_from(symbol);
                                ev.call = call.clone();
                                hit = true;
                            }
                        }
                    }
                }
            }
        }
        if hit { Ok(p) } else { Err(MutationMissed(m.name())) }
    }
}

// ---------------------------------------------------------------------------
// Builder: structured code -> CFG, so a fixture reads like the code it
// transcribes.
// ---------------------------------------------------------------------------

/// Builds an [`EventProgram`].
pub struct ProgramBuilder {
    prog: EventProgram,
}

impl ProgramBuilder {
    #[must_use]
    pub fn new(name: &str) -> ProgramBuilder {
        ProgramBuilder {
            prog: EventProgram {
                name: name.to_string(),
                provenance: Vec::new(),
                vars: Vec::new(),
                bodies: Vec::new(),
                roots: Vec::new(),
                sites: Vec::new(),
                fd_params: Vec::new(),
                disclosures: Vec::new(),
                policies: Policies::default(),
            },
        }
    }

    /// Check the program under P-LOCK-RELEASE.
    pub fn lock_release_policy(&mut self) {
        self.prog.policies.lock_release = true;
    }

    /// Check thread roots `roots` under fd-identity.
    pub fn fd_identity_policy(&mut self, roots: &[usize]) {
        self.prog.policies.fd_identity = roots.to_vec();
    }

    /// A thread root that starts when another actor's
    /// [`BodyBuilder::spawn_thread`] names it; returns its index.
    pub fn thread(&mut self, name: &str, body: BodyId) -> usize {
        self.prog.roots.push(Root { name: name.to_string(), body, dormant: true });
        self.prog.roots.len() - 1
    }

    pub fn provenance(&mut self, repo: &str, commit: &str, path: &str, what: &str) {
        self.prog.provenance.push(Provenance {
            repo: repo.to_string(),
            commit: commit.to_string(),
            path: path.to_string(),
            what: what.to_string(),
        });
    }

    /// Disclose, in words, something this hand-written program leaves out or
    /// evaluates by hand ([`EventProgram::disclosures`]).
    pub fn disclose(&mut self, text: &str) {
        self.prog.disclosures.push(text.to_string());
    }

    pub fn var(&mut self, name: &str, init: i64) -> VarId {
        self.prog.vars.push(Var { name: name.to_string(), init });
        self.prog.vars.len() - 1
    }

    /// A descriptor argument placed by RL-INIT.
    pub fn fd_param(&mut self, name: &str, class: &str, peer_class: Option<&str>) -> VarId {
        let var = self.var(name, -1);
        self.prog.fd_params.push(FdParam {
            var,
            class: class.to_string(),
            peer_class: peer_class.map(str::to_string),
        });
        var
    }

    pub fn site(&mut self, name: &str, loc: &str, policy: Option<FdInherit>) -> SiteId {
        self.prog.sites.push(SpawnSite { name: name.to_string(), loc: Loc::new(loc), policy });
        self.prog.sites.len() - 1
    }

    /// Reserve a body id (for mutual references); fill it with [`Self::define`].
    pub fn declare(&mut self, name: &str, params: Vec<VarId>) -> BodyId {
        self.prog.bodies.push(Body { name: name.to_string(), params, blocks: Vec::new() });
        self.prog.bodies.len() - 1
    }

    pub fn define(&mut self, id: BodyId, f: impl FnOnce(&mut BodyBuilder)) {
        let mut b = BodyBuilder::new();
        f(&mut b);
        self.prog.bodies[id].blocks = b.finish();
    }

    pub fn body(
        &mut self,
        name: &str,
        params: Vec<VarId>,
        f: impl FnOnce(&mut BodyBuilder),
    ) -> BodyId {
        let id = self.declare(name, params);
        self.define(id, f);
        id
    }

    /// A thread root running from the program's start; returns its index.
    pub fn root(&mut self, name: &str, body: BodyId) -> usize {
        self.prog.roots.push(Root { name: name.to_string(), body, dormant: false });
        self.prog.roots.len() - 1
    }

    #[must_use]
    pub fn build(self) -> EventProgram {
        self.prog
    }
}

struct OpenBlock {
    stmts: Vec<Stmt>,
    term: Option<(Term, Loc, Option<String>)>,
}

/// Builds one body's CFG from structured statements.
pub struct BodyBuilder {
    blocks: Vec<OpenBlock>,
    cur: BlockId,
    pending_tag: Option<String>,
}

impl BodyBuilder {
    fn new() -> BodyBuilder {
        BodyBuilder {
            blocks: vec![OpenBlock { stmts: Vec::new(), term: None }],
            cur: 0,
            pending_tag: None,
        }
    }

    fn new_block(&mut self) -> BlockId {
        self.blocks.push(OpenBlock { stmts: Vec::new(), term: None });
        self.blocks.len() - 1
    }

    fn terminate(&mut self, term: Term, loc: Loc, tag: Option<String>) {
        let b = &mut self.blocks[self.cur];
        if b.term.is_none() {
            b.term = Some((term, loc, tag));
        }
    }

    /// Tag the next statement or branch (a mutant-sweep handle).
    pub fn tag(&mut self, tag: &str) -> &mut Self {
        self.pending_tag = Some(tag.to_string());
        self
    }

    pub fn push(&mut self, kind: StmtKind, loc: &str) {
        let tag = self.pending_tag.take();
        self.blocks[self.cur].stmts.push(Stmt { kind, loc: Loc::new(loc), tag });
    }

    /// A platform event with nominal oracle only.
    pub fn event(&mut self, loc: &str, symbol: &str, call: Call<Operand>, bind: Bind) {
        self.event_full(loc, symbol, call, bind, vec![Oracle::Nominal], None, Vec::new());
    }

    #[allow(clippy::too_many_arguments)]
    pub fn event_full(
        &mut self,
        loc: &str,
        symbol: &str,
        call: Call<Operand>,
        bind: Bind,
        oracles: Vec<Oracle>,
        site: Option<SiteId>,
        ofd_names: Vec<&str>,
    ) {
        self.push(
            StmtKind::Event(Event {
                symbol: symbol.to_string(),
                call,
                bind,
                oracles,
                site,
                ofd_names: ofd_names.into_iter().map(str::to_string).collect(),
                std_origin: None,
                path: None,
                assumption: None,
            }),
            loc,
        );
    }

    /// An `open` of a literal `path` (the census classifies it).
    pub fn open(&mut self, loc: &str, path: &str, call: Call<Operand>, bind: Bind, ofd: &str) {
        let ofd_names =
            if matches!(call, Call::Open { .. }) { vec![ofd.to_string()] } else { Vec::new() };
        self.push(
            StmtKind::Event(Event {
                symbol: "open".to_string(),
                call,
                bind,
                oracles: vec![Oracle::Nominal],
                site: None,
                ofd_names,
                std_origin: None,
                path: Some(path.to_string()),
                assumption: None,
            }),
            loc,
        );
    }

    /// An `open` of a literal `path` the census would classify as `Other`,
    /// with the hand census's statement of what it names
    /// ([`Event::assumption`]) and the oracle choices to explore.
    #[allow(clippy::too_many_arguments)]
    pub fn open_assuming(
        &mut self,
        loc: &str,
        path: &str,
        call: Call<Operand>,
        bind: Bind,
        ofd: &str,
        oracles: Vec<Oracle>,
        assumption: &str,
    ) {
        let ofd_names =
            if matches!(call, Call::Open { .. }) { vec![ofd.to_string()] } else { Vec::new() };
        self.push(
            StmtKind::Event(Event {
                symbol: "open".to_string(),
                call,
                bind,
                oracles,
                site: None,
                ofd_names,
                std_origin: None,
                path: Some(path.to_string()),
                assumption: Some(assumption.to_string()),
            }),
            loc,
        );
    }

    /// A raw `fork(2)` (a libc call, not `Command::spawn`): the child runs
    /// `child` — a body of its own, which must end in `execve` or `_exit` —
    /// with a copy of the forking actor's variables; the parent receives the
    /// child's pid in `bind` (or `-1`).
    pub fn fork(&mut self, loc: &str, child: BodyId, site: SiteId, bind: Option<VarId>) {
        self.push(StmtKind::Fork { child, site, bind, std_origin: None }, loc);
    }

    pub fn assign(&mut self, loc: &str, var: VarId, expr: Expr) {
        self.push(StmtKind::Assign { var, expr }, loc);
    }

    pub fn call(
        &mut self,
        loc: &str,
        body: BodyId,
        args: Vec<(VarId, Operand)>,
        ret: Option<VarId>,
    ) {
        self.push(StmtKind::Call { body, args, ret }, loc);
    }

    pub fn for_range(&mut self, loc: &str, var: VarId, lo: Operand, hi: Operand, body: BodyId) {
        self.push(StmtKind::ForRange { var, lo, hi, body }, loc);
    }

    pub fn neutral(&mut self, loc: &str, symbol: &str) {
        self.push(StmtKind::Neutral { symbol: symbol.to_string() }, loc);
    }

    /// The owner's release point for `classes` ([`StmtKind::Release`]).
    pub fn release(&mut self, loc: &str, classes: &[&str]) {
        let classes = classes.iter().map(|c| (*c).to_string()).collect();
        self.push(StmtKind::Release { classes }, loc);
    }

    /// `std::thread::spawn` of thread root `root` ([`ProgramBuilder::thread`]).
    pub fn spawn_thread(&mut self, loc: &str, root: usize) {
        self.push(StmtKind::SpawnThread { root }, loc);
    }

    /// `JoinHandle::join` of thread root `root`.
    pub fn join(&mut self, loc: &str, root: usize) {
        self.push(StmtKind::Join { root }, loc);
    }

    /// A `read`/`write` of a few bytes on a pipe or socketpair end, as the
    /// model's [`Call::ReadSome`] / [`Call::WriteSome`] (byte counts and
    /// contents abstracted), with the hand census's statement of why that is
    /// its effect ([`Event::assumption`], printed into the model's notes).
    pub fn io(&mut self, loc: &str, call: Call<Operand>, bind: Bind, assumption: &str) {
        self.push(
            StmtKind::Event(Event {
                symbol: call.symbol().to_string(),
                call,
                bind,
                oracles: vec![Oracle::Nominal],
                site: None,
                ofd_names: Vec::new(),
                std_origin: None,
                path: None,
                assumption: Some(assumption.to_string()),
            }),
            loc,
        );
    }

    /// `std::fs::File::open`/`create` (`std_fn`) of the namespace path
    /// `file`: STD-OPEN's step, resolved by the model's namespace
    /// (`trust_platform::std_summaries::std_open_path`).
    pub fn std_open(
        &mut self,
        loc: &str,
        std_fn: &str,
        file: &str,
        flags: i32,
        bind: VarId,
        ofd: &str,
    ) {
        self.push(
            StmtKind::Std(StdCall::OpenFile {
                std_fn: std_fn.to_string(),
                file: file.to_string(),
                flags,
                bind,
                ofd_name: ofd.to_string(),
            }),
            loc,
        );
    }

    pub fn std_row(
        &mut self,
        loc: &str,
        path: &str,
        args: Vec<Operand>,
        bind: Vec<VarId>,
        ofd_names: Vec<&str>,
    ) {
        self.push(
            StmtKind::Std(StdCall::Row {
                path: path.to_string(),
                args,
                bind,
                ofd_names: ofd_names.into_iter().map(str::to_string).collect(),
            }),
            loc,
        );
    }

    /// `Command::spawn()` of a command with these `pre_exec` closures and
    /// nothing else std's path choice reads, under current Trust std.
    /// Historical upstream fixtures select their std explicitly with [`Self::spawn`].
    pub fn spawn_fork(
        &mut self,
        loc: &str,
        stdio: [StdioPlan; 3],
        pre_exec: Vec<BodyId>,
        site: SiteId,
        bind: Option<VarId>,
    ) {
        let shape = CommandShape::with_pre_exec();
        self.spawn(loc, stdio, shape, pre_exec, site, bind);
    }

    /// `Command::spawn()` of a plain command (std's `posix_spawnp` path),
    /// under current Trust std (see [`Self::spawn_fork`]).
    pub fn spawn_posix(
        &mut self,
        loc: &str,
        stdio: [StdioPlan; 3],
        site: SiteId,
        bind: Option<VarId>,
    ) {
        let shape = CommandShape::default();
        self.spawn(loc, stdio, shape, Vec::new(), site, bind);
    }

    /// `Command::spawn()` of a command of any shape.
    pub fn spawn(
        &mut self,
        loc: &str,
        stdio: [StdioPlan; 3],
        shape: CommandShape,
        pre_exec: Vec<BodyId>,
        site: SiteId,
        bind: Option<VarId>,
    ) {
        self.push(StmtKind::Std(StdCall::CommandSpawn { stdio, shape, pre_exec, site, bind }), loc);
    }

    /// `if cond { then } else { els }`.
    pub fn if_(
        &mut self,
        loc: &str,
        cond: Cond,
        then: impl FnOnce(&mut BodyBuilder),
        els: impl FnOnce(&mut BodyBuilder),
    ) {
        let tag = self.pending_tag.take();
        let t = self.new_block();
        let e = self.new_block();
        let join = self.new_block();
        self.terminate(Term::Branch { cond, then: t, els: e }, Loc::new(loc), tag);
        self.cur = t;
        then(self);
        self.terminate(Term::Goto(join), Loc::new(loc), None);
        self.cur = e;
        els(self);
        self.terminate(Term::Goto(join), Loc::new(loc), None);
        self.cur = join;
    }

    /// `if cond { then }`.
    pub fn when(&mut self, loc: &str, cond: Cond, then: impl FnOnce(&mut BodyBuilder)) {
        self.if_(loc, cond, then, |_| {});
    }

    /// `return op;` — later statements of this arm are unreachable.
    pub fn ret(&mut self, loc: &str, op: Option<Operand>) {
        self.terminate(Term::Return(op), Loc::new(loc), None);
        self.cur = self.new_block();
    }

    fn finish(mut self) -> Vec<Block> {
        self.terminate(Term::Return(None), Loc::new("<end of body>"), None);
        self.blocks
            .into_iter()
            .map(|b| {
                let (term, term_loc, term_tag) =
                    b.term.unwrap_or((Term::Return(None), Loc::new("<end of body>"), None));
                Block { stmts: b.stmts, term, term_loc, term_tag }
            })
            .collect()
    }
}
