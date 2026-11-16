//! Surface -> core: std calls become the events of their trust-platform
//! summary rows, every symbol is joined with `trust_platform::symbols`
//! (I-FD-SPECIFIED), and each policy site's static `Declared` part (§2.4) is
//! computed from the policy. The dynamic part — the descriptors a child's
//! setup places or un-flags — is recorded by the interpreter as the child
//! runs, at the numbers the calls actually name.

use std::collections::BTreeMap;

use trust_platform::script::{Actor, Operand as ScriptOperand};
use trust_platform::std_summaries::{self, CommandShape, SpawnPath, StdRow, StdioPlan};
use trust_platform::symbols::{self, ClauseId, Modeled, OpenPath, UnmodeledPlatformEffect};
use trust_platform::{Call, FileAction, Oracle};

use crate::program::{
    Bind, Block, Body, BodyId, Cond, Event, EventProgram, Expr, Loc, Operand, SiteId, StdCall,
    StdOrigin, Stmt, StmtKind, StmtRef, Term, Var, VarId,
};

/// Why a program could not be lowered.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LowerError {
    /// A name the platform model does not cover (a named Unknown, never a
    /// silent no-op).
    Unmodeled { effect: UnmodeledPlatformEffect, loc: Loc },
    /// A symbol that looks up as a different clause than the event's call.
    SymbolMismatch { symbol: String, call: &'static str, loc: Loc },
    /// A std row the lowering cannot inline (wrong actor shape, bad args, a
    /// command shape whose child steps are not modeled).
    BadStdRow { path: String, detail: String, loc: Loc },
    /// A body id or variable out of range.
    Malformed(String),
    /// X1: a value the census did not track ([`Expr::Opaque`]) can reach a
    /// place the model executes: an event's descriptor operand, a branch
    /// guard or a loop bound ([`crate::track`]). The census reports the site
    /// `PC-UNTRACKED-FD`.
    Untracked { var: String, used_as: String, loc: Loc, origin: Loc },
}

impl std::fmt::Display for LowerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LowerError::Unmodeled { effect, loc } => write!(f, "{effect} at {loc}"),
            LowerError::SymbolMismatch { symbol, call, loc } => {
                write!(f, "symbol `{symbol}` does not name the `{call}` clause at {loc}")
            }
            LowerError::BadStdRow { path, detail, loc } => {
                write!(f, "std row for `{path}` cannot be inlined at {loc}: {detail}")
            }
            LowerError::Malformed(s) => write!(f, "malformed event program: {s}"),
            LowerError::Untracked { var, used_as, loc, origin } => write!(
                f,
                "`{var}` is untracked (its value comes from what the census could not follow at \
                 {origin}) but is the {used_as} at {loc}: the model would run on a value the \
                 program never computed"
            ),
        }
    }
}

/// One census row: a name the program calls and what the model says it is.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CensusRow {
    pub symbol: String,
    pub modeled: String,
    pub loc: Loc,
}

/// The static part of `Declared(site)` of P-FD-INHERIT (plan §2.4).
///
/// A child of the site may hold at exec: `allowed` plus every descriptor its
/// own setup placed or un-flagged (`dup2`/`adddup2`/`addopen` targets,
/// `F_SETFD` without `FD_CLOEXEC`, `FIONCLEX`, `addinherit_np` — recorded at
/// run time by number, whatever operand named it). It must hold `required`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Declared {
    /// `{0,1,2}` and the policy's lanes.
    pub allowed: std::collections::BTreeSet<i32>,
    /// The policy's lanes, with the class of description each must name. A
    /// placement target that is not a lane is allowed, not required: a
    /// scratch `dup2` target the setup later closes is no violation.
    pub required: Vec<(i32, Option<usize>)>,
}

/// A lowered program plus what the derivation needs to read it.
#[derive(Clone, Debug)]
pub struct CoreProgram {
    pub prog: EventProgram,
    /// Open-file-description classes (allocation sites and RL-INIT
    /// descriptors), by index.
    pub classes: Vec<String>,
    /// Per site: `Some` iff the site is under the fd-inherit policy.
    pub declared: Vec<Option<Declared>>,
    pub census: Vec<CensusRow>,
    /// Census assumptions the model rests on, printed into its notes (an
    /// `open` path assumed to name a fresh vnode, …).
    pub assumptions: Vec<String>,
    /// Per body and block: whether execution from the block's entry can
    /// still reach a spawn statement of a policy site (through calls).
    pub policy_reach: Vec<Vec<bool>>,
    /// Per body: whether a call to it can reach a policy spawn.
    pub body_reaches: Vec<bool>,
    /// The program uses an M2 feature (a lock, the namespace, `fstat`, a
    /// thread start or join, a release marker, a raw `read`/`write`, an M2
    /// policy): the derivation then encodes locks, nodes, names, status
    /// bits, pending data and bindings, lets an exec'd image exit, and keeps
    /// the fd-inherit horizon off. An M1 program derives exactly as before.
    pub extended: bool,
    /// A forked child's events that can change state other processes see
    /// (dropping a reference to a lockable or locked description, or the last
    /// one of a pipe/socket end; `flock`; I/O; the namespace; its exec and
    /// exit) are interleaving points instead of parts of one fork-to-exec
    /// macro step: set under P-LOCK-RELEASE or when the program can take a
    /// lock, because then WHEN a child drops its copy decides whether a lock
    /// outlives its owner (SD-3's split points).
    pub child_splits: bool,
}

impl CoreProgram {
    fn is_policy_spawn(&self, kind: &StmtKind) -> bool {
        let site = match kind {
            StmtKind::Fork { site, .. } => Some(*site),
            StmtKind::Event(ev) => ev.site,
            _ => None,
        };
        site.is_some_and(|s| matches!(self.declared.get(s), Some(Some(_))))
    }

    fn stmt_hits(&self, kind: &StmtKind) -> bool {
        self.is_policy_spawn(kind)
            || matches!(kind, StmtKind::Call { body, .. } | StmtKind::ForRange { body, .. }
                if self.body_reaches.get(*body).copied().unwrap_or(true))
    }

    fn term_any_succ(term: &Term, mut pred: impl FnMut(usize) -> bool) -> bool {
        match term {
            Term::Goto(b) => pred(*b),
            Term::Branch { then, els, .. } => pred(*then) || pred(*els),
            Term::Return(_) => false,
        }
    }

    /// Compute `policy_reach` / `body_reaches` (a least fixpoint).
    fn compute_policy_reach(&mut self) {
        self.body_reaches = vec![false; self.prog.bodies.len()];
        self.policy_reach = self.prog.bodies.iter().map(|b| vec![false; b.blocks.len()]).collect();
        loop {
            let mut changed = false;
            for (bi, body) in self.prog.bodies.iter().enumerate() {
                for (k, block) in body.blocks.iter().enumerate().rev() {
                    let hit = block.stmts.iter().any(|s| self.stmt_hits(&s.kind))
                        || Self::term_any_succ(&block.term, |n| {
                            self.policy_reach[bi].get(n).copied().unwrap_or(false)
                        });
                    if hit && !self.policy_reach[bi][k] {
                        self.policy_reach[bi][k] = true;
                        changed = true;
                    }
                }
                let entry = self.policy_reach[bi].first().copied().unwrap_or(false);
                if entry && !self.body_reaches[bi] {
                    self.body_reaches[bi] = true;
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
    }

    /// Whether execution resumed at `(body, block, idx)` can still reach a
    /// policy spawn.
    #[must_use]
    pub fn reaches_policy(&self, body: usize, block: usize, idx: usize) -> bool {
        let Some(b) = self.prog.bodies.get(body).and_then(|b| b.blocks.get(block)) else {
            return true;
        };
        b.stmts.iter().skip(idx).any(|s| self.stmt_hits(&s.kind))
            || Self::term_any_succ(&b.term, |n| {
                self.policy_reach[body].get(n).copied().unwrap_or(true)
            })
    }

    #[must_use]
    pub fn class_idx(&self, name: &str) -> Option<usize> {
        self.classes.iter().position(|c| c == name)
    }

    pub fn intern_class(&mut self, name: &str) -> usize {
        if let Some(i) = self.class_idx(name) {
            return i;
        }
        self.classes.push(name.to_string());
        self.classes.len() - 1
    }
}

fn clause_of<V>(call: &Call<V>) -> Option<ClauseId> {
    Some(match call {
        Call::Pipe => ClauseId::Pipe,
        Call::Socketpair { .. } => ClauseId::Socketpair,
        Call::Socket { .. } => ClauseId::Socket,
        Call::SocketOp { .. } => ClauseId::SocketOp,
        Call::Accept { .. } => ClauseId::Accept,
        Call::Open { .. } | Call::OpenAlias { .. } => ClauseId::Open,
        Call::Kqueue => ClauseId::Kqueue,
        Call::Fcntl { .. } => ClauseId::Fcntl,
        Call::Dup { .. } => ClauseId::Dup,
        Call::Dup2 { .. } => ClauseId::Dup2,
        Call::Close { .. } => ClauseId::Close,
        Call::Ioctl { .. } => ClauseId::Ioctl,
        Call::Fork => ClauseId::Fork,
        Call::Exec => ClauseId::Exec,
        Call::Spawn { .. } | Call::SpawnBegin | Call::SpawnEnd { .. } => ClauseId::Spawn,
        Call::Getrlimit { .. } => ClauseId::Getrlimit,
        Call::Setrlimit { .. } => ClauseId::Setrlimit,
        Call::ListOwnFds { .. } => ClauseId::ListOwnFds,
        Call::Sysctl { .. } => ClauseId::Sysctl,
        Call::Exit { .. } => ClauseId::Exit,
        Call::Waitpid { .. } => ClauseId::Waitpid,
        Call::ThreadCreate => ClauseId::ThreadCreate,
        Call::Flock { .. } => ClauseId::Flock,
        Call::OpenPath { at: None, .. } => ClauseId::Open,
        Call::OpenPath { at: Some(_), .. } => ClauseId::Openat,
        Call::Fstat { .. } => ClauseId::Fstat,
        Call::Mkfifo { .. } => ClauseId::Mkfifo,
        Call::Unlink { .. } => ClauseId::Unlink,
        Call::Symlink { .. } => ClauseId::Symlink,
        // std's status-pipe channel, or a raw read/write the hand census
        // states the effect of (`Event::assumption`); a continuation is the
        // interpreter's, never a census row.
        Call::ReadSome { .. } | Call::WriteSome { .. } | Call::Resume { .. }
        // These are compositions in std rows, never imported libc clauses.
        | Call::StdPlaceFd { .. } | Call::StdClearCloexec { .. }
        | Call::StdPassesExec { .. } | Call::StdMarkCloexec | Call::StdStatusFd { .. }
        | Call::StdCloseMovedStatus { .. } => return None,
        // The old strip primitive is not an imported libc clause. Current
        // Trust Command rows use StdMarkCloexec instead; a raw event cannot
        // acquire std-summary authority by naming either composition.
        Call::CloexecFrom { .. } => return None,
    })
}

/// How many fresh descriptions a call mints (by result component).
#[must_use]
pub fn allocates<V>(call: &Call<V>) -> usize {
    match call {
        Call::Pipe | Call::Socketpair { .. } => 2,
        Call::Socket { .. }
        | Call::Accept { .. }
        | Call::Open { .. }
        | Call::OpenPath { .. }
        | Call::Kqueue => 1,
        Call::Spawn { actions, .. } => {
            actions.iter().filter(|a| matches!(a, FileAction::Open { .. })).count()
        }
        _ => 0,
    }
}

/// A std call, expanded.
enum Expansion {
    /// Straight-line events.
    Inline(Vec<Stmt>),
    /// STD-SPAWN-FORK: `before` ends with the status read bound to
    /// `status`; `0` continues with `ok`, data with `err`; both then
    /// continue with the rest of the original block.
    Split { before: Vec<Stmt>, status: VarId, ok: Vec<Stmt>, err: Vec<Stmt>, loc: Loc },
}

struct Lowerer<'a> {
    src: &'a EventProgram,
    vars: Vec<Var>,
    new_bodies: Vec<Body>,
    census: Vec<CensusRow>,
    next_temp: usize,
}

impl Lowerer<'_> {
    fn temp(&mut self, hint: &str) -> VarId {
        self.next_temp += 1;
        self.vars.push(Var { name: format!("__{hint}#{}", self.next_temp), init: -1 });
        self.vars.len() - 1
    }

    fn temps(&mut self, row: &StdRow) -> Vec<[VarId; 2]> {
        (0..row.program.len())
            .map(|k| {
                [self.temp(&format!("{}.{k}.0", row.id)), self.temp(&format!("{}.{k}.1", row.id))]
            })
            .collect()
    }

    fn census_std(&mut self, path: &str, loc: &Loc) -> Result<Modeled, LowerError> {
        let l = symbols::lookup(path)
            .map_err(|effect| LowerError::Unmodeled { effect, loc: loc.clone() })?;
        self.census.push(CensusRow {
            symbol: path.to_string(),
            modeled: format!("{:?}", l.modeled),
            loc: loc.clone(),
        });
        Ok(l.modeled)
    }

    /// Convert one row call; `temps[k]` are step k's result vars.
    fn row_call(
        row: &StdRow,
        call: &Call<ScriptOperand>,
        args: &[Operand],
        temps: &[[VarId; 2]],
        loc: &Loc,
    ) -> Result<Call<Operand>, LowerError> {
        let mut bad = None;
        let c = call.map(|op| match *op {
            ScriptOperand::Lit(v) => Operand::Lit(i64::from(v)),
            ScriptOperand::Arg(i) => args.get(i).copied().unwrap_or_else(|| {
                bad = Some(format!("missing argument {i}"));
                Operand::Lit(-1)
            }),
            ScriptOperand::Ret { step, comp } => {
                temps.get(step).and_then(|t| t.get(usize::from(comp))).map_or_else(
                    || {
                        bad = Some(format!("result of step {step} not available"));
                        Operand::Lit(-1)
                    },
                    |v| Operand::Var(*v),
                )
            }
        });
        match bad {
            Some(detail) => {
                Err(LowerError::BadStdRow { path: row.id.to_string(), detail, loc: loc.clone() })
            }
            None => Ok(c),
        }
    }

    fn row_event(
        row: &StdRow,
        k: usize,
        call: Call<Operand>,
        bind: Bind,
        names: &mut std::slice::Iter<'_, String>,
    ) -> Event {
        let n = allocates(&call);
        let ofd_names = (0..n)
            .map(|c| names.next().cloned().unwrap_or_else(|| format!("{}_{k}_{c}", row.id)))
            .collect();
        Event {
            symbol: call.symbol().to_string(),
            call,
            bind,
            oracles: vec![Oracle::Nominal],
            site: None,
            ofd_names,
            std_origin: Some(StdOrigin { row: row.id, step: k, source: row.source }),
            path: None,
            assumption: None,
        }
    }

    fn step_bind(call: &Call<Operand>, temps: &[[VarId; 2]], k: usize) -> Bind {
        match call {
            Call::Pipe | Call::Socketpair { .. } => Bind::pair(temps[k][0], temps[k][1]),
            _ => Bind::ret(temps[k][0]),
        }
    }

    fn expand(
        &mut self,
        stmt: &Stmt,
        call: &StdCall,
        body_count: usize,
    ) -> Result<Expansion, LowerError> {
        let loc = &stmt.loc;
        let mk = |kind| Stmt { kind, loc: loc.clone(), tag: stmt.tag.clone() };
        match call {
            StdCall::Row { path, args, bind, ofd_names } => {
                let Modeled::StdRow(id) = self.census_std(path, loc)? else {
                    return Err(LowerError::BadStdRow {
                        path: path.clone(),
                        detail: "not a fixed std summary row".to_string(),
                        loc: loc.clone(),
                    });
                };
                if id == "STD-OPEN" {
                    return Err(LowerError::BadStdRow {
                        path: path.clone(),
                        detail: "STD-OPEN is parametric in the open flags and the path; a fixed \
                                 row would claim O_RDONLY for File::create"
                            .to_string(),
                        loc: loc.clone(),
                    });
                }
                let row = std_summaries::row(id).ok_or_else(|| LowerError::BadStdRow {
                    path: path.clone(),
                    detail: format!("no row {id}"),
                    loc: loc.clone(),
                })?;
                let temps = self.temps(&row);
                let mut names = ofd_names.iter();
                let mut out = Vec::new();
                for (k, ps) in row.program.iter().enumerate() {
                    if ps.actor != Actor::Root {
                        return Err(LowerError::BadStdRow {
                            path: path.clone(),
                            detail: "a fixed row with a child step".to_string(),
                            loc: loc.clone(),
                        });
                    }
                    if ps.branches() {
                        return Err(LowerError::BadStdRow {
                            path: path.clone(),
                            detail: "a fixed row with a guarded step".to_string(),
                            loc: loc.clone(),
                        });
                    }
                    let c = Self::row_call(&row, &ps.call, args, &temps, loc)?;
                    let b = Self::step_bind(&c, &temps, k);
                    out.push(mk(StmtKind::Event(Self::row_event(&row, k, c, b, &mut names))));
                }
                for (i, r) in row.returns.iter().enumerate() {
                    let Some(dst) = bind.get(i) else { continue };
                    let src = Self::resolve_ret(*r, &temps);
                    out.push(mk(StmtKind::Assign { var: *dst, expr: Expr::Use(src) }));
                }
                Ok(Expansion::Inline(out))
            }
            StdCall::OpenFile { std_fn, file, flags, bind, ofd_name } => {
                let Modeled::StdRow("STD-OPEN") = self.census_std(std_fn, loc)? else {
                    return Err(LowerError::BadStdRow {
                        path: std_fn.clone(),
                        detail: "not STD-OPEN".to_string(),
                        loc: loc.clone(),
                    });
                };
                let row = std_summaries::std_open_path(file, *flags);
                let temps = self.temps(&row);
                let names = [ofd_name.clone()];
                let mut names = names.iter();
                let mut out = Vec::new();
                for (k, ps) in row.program.iter().enumerate() {
                    let c = Self::row_call(&row, &ps.call, &[], &temps, loc)?;
                    let b = Self::step_bind(&c, &temps, k);
                    let mut ev = Self::row_event(&row, k, c, b, &mut names);
                    ev.path = Some(file.clone());
                    out.push(mk(StmtKind::Event(ev)));
                }
                let src = Self::resolve_ret(row.returns[0], &temps);
                out.push(mk(StmtKind::Assign { var: *bind, expr: Expr::Use(src) }));
                Ok(Expansion::Inline(out))
            }
            StdCall::CommandSpawn { stdio, shape, pre_exec, site, bind } => {
                let Modeled::StdCommandSpawn =
                    self.census_std("std::process::Command::spawn", loc)?
                else {
                    return Err(LowerError::Malformed("Command::spawn lookup".to_string()));
                };
                let mut shape = *shape;
                if !pre_exec.is_empty() {
                    shape.pre_exec = true;
                } else if shape.pre_exec {
                    return Err(LowerError::BadStdRow {
                        path: "std::process::Command::spawn".to_string(),
                        detail: "the command has pre_exec closures the program does not name"
                            .to_string(),
                        loc: loc.clone(),
                    });
                }
                match std_summaries::spawn_path(&shape) {
                    SpawnPath::Posix => self.expand_posix(stmt, *stdio, &shape, *site, *bind),
                    SpawnPath::Fork => {
                        self.census_std("std::os::unix::process::CommandExt::pre_exec", loc)?;
                        self.expand_fork(stmt, *stdio, &shape, pre_exec, *site, *bind, body_count)
                    }
                }
            }
        }
    }

    fn expand_posix(
        &mut self,
        stmt: &Stmt,
        stdio: [StdioPlan; 3],
        shape: &CommandShape,
        site: SiteId,
        bind: Option<VarId>,
    ) -> Result<Expansion, LowerError> {
        let loc = &stmt.loc;
        let mk = |kind| Stmt { kind, loc: loc.clone(), tag: stmt.tag.clone() };
        let (row, spawn) = std_summaries::command_spawn_posix(stdio, shape).map_err(|detail| {
            LowerError::BadStdRow {
                path: "std::process::Command::spawn".to_string(),
                detail,
                loc: loc.clone(),
            }
        })?;
        Self::command_row(&row, loc)?;
        let temps = self.temps(&row);
        let no_names: Vec<String> = Vec::new();
        let mut names = no_names.iter();
        let mut out = Vec::new();
        for (k, ps) in row.program.iter().enumerate() {
            if ps.actor != Actor::Root {
                return Err(LowerError::BadStdRow {
                    path: "std::process::Command::spawn".to_string(),
                    detail: "a posix Command row with a child step".to_string(),
                    loc: loc.clone(),
                });
            }
            let c = Self::row_call(&row, &ps.call, &[], &temps, loc)?;
            let b = Self::step_bind(&c, &temps, k);
            let mut ev = Self::row_event(&row, k, c, b, &mut names);
            if k == spawn {
                ev.site = Some(site);
            }
            out.push(mk(StmtKind::Event(ev)));
        }
        if let Some(b) = bind {
            out.push(mk(StmtKind::Assign {
                var: b,
                expr: Expr::Use(Operand::Var(temps[spawn][0])),
            }));
        }
        Ok(Expansion::Inline(out))
    }

    #[allow(clippy::too_many_arguments)]
    fn expand_fork(
        &mut self,
        stmt: &Stmt,
        stdio: [StdioPlan; 3],
        shape: &CommandShape,
        pre_exec: &[BodyId],
        site: SiteId,
        bind: Option<VarId>,
        body_count: usize,
    ) -> Result<Expansion, LowerError> {
        let loc = &stmt.loc;
        let mk = |kind| Stmt { kind, loc: loc.clone(), tag: stmt.tag.clone() };
        let fr = std_summaries::command_spawn_fork(stdio, shape, &[]).map_err(|detail| {
            LowerError::BadStdRow {
                path: "std::process::Command::spawn".to_string(),
                detail,
                loc: loc.clone(),
            }
        })?;
        Self::command_row(&fr.row, loc)?;
        let row = &fr.row;
        let temps = self.temps(row);
        let no_names: Vec<String> = Vec::new();
        let mut names = no_names.iter();
        let child_body = body_count + self.new_bodies.len();
        let mut before = Vec::new();
        let mut after = Vec::new();
        let mut child_steps = Vec::new();
        for (k, ps) in row.program.iter().enumerate() {
            let c = Self::row_call(row, &ps.call, &[], &temps, loc)?;
            let b = Self::step_bind(&c, &temps, k);
            let origin = StdOrigin { row: row.id, step: k, source: row.source };
            match ps.actor {
                Actor::Root if k == fr.fork => before.push(mk(StmtKind::Fork {
                    child: child_body,
                    site,
                    bind: Some(temps[k][0]),
                    std_origin: Some(origin),
                })),
                Actor::Root if k <= fr.status_read => {
                    before.push(mk(StmtKind::Event(Self::row_event(row, k, c, b, &mut names))));
                }
                Actor::Root => {
                    after.push(mk(StmtKind::Event(Self::row_event(row, k, c, b, &mut names))));
                }
                Actor::Child(f) if f == fr.fork => {
                    if k != fr.exec {
                        child_steps.push((k, Self::row_event(row, k, c, b, &mut names)));
                    }
                }
                Actor::Child(_) => {
                    return Err(LowerError::BadStdRow {
                        path: "std::process::Command::spawn".to_string(),
                        detail: "a step by an unknown child".to_string(),
                        loc: loc.clone(),
                    });
                }
            }
        }
        let child_error: Vec<Call<Operand>> = fr
            .child_error
            .iter()
            .map(|c| Self::row_call(row, c, &[], &temps, loc))
            .collect::<Result<_, _>>()?;
        let parent_error: Vec<Call<Operand>> = fr
            .parent_error
            .iter()
            .map(|c| Self::row_call(row, c, &[], &temps, loc))
            .collect::<Result<_, _>>()?;
        let body = self.child_body(row, &fr, child_steps, child_error, pre_exec, loc);
        self.new_bodies.push(body);
        let status = temps[fr.status_read][0];
        let mut ok = after.clone();
        let mut err: Vec<Stmt> = parent_error
            .into_iter()
            .map(|c| {
                let e = Event {
                    symbol: c.symbol().to_string(),
                    bind: Bind::none(),
                    call: c,
                    oracles: vec![Oracle::Nominal],
                    site: None,
                    ofd_names: Vec::new(),
                    std_origin: Some(StdOrigin {
                        row: row.id,
                        step: fr.status_read,
                        source: row.source,
                    }),
                    path: None,
                    assumption: None,
                };
                mk(StmtKind::Event(e))
            })
            .collect();
        err.extend(after);
        if let Some(b) = bind {
            ok.push(mk(StmtKind::Assign {
                var: b,
                expr: Expr::Use(Operand::Var(temps[fr.fork][0])),
            }));
            err.push(mk(StmtKind::Assign { var: b, expr: Expr::Use(Operand::Lit(-1)) }));
        }
        Ok(Expansion::Split { before, status, ok, err, loc: loc.clone() })
    }

    /// Both current Trust and historical upstream rows are straight-line.
    /// Trust's descriptor-dependent operations are existing executable
    /// compositions, not guards to erase here. Refuse any future guarded,
    /// assumed or non-nominal step rather than silently changing its meaning.
    fn command_row(row: &StdRow, loc: &Loc) -> Result<(), LowerError> {
        if row.program.iter().all(|ps| !ps.branches() && ps.oracle == Oracle::Nominal) {
            return Ok(());
        }
        Err(LowerError::BadStdRow {
            path: "std::process::Command::spawn".to_string(),
            detail: format!(
                "{}: guarded, assumed or non-nominal Command steps are not lowered",
                row.id
            ),
            loc: loc.clone(),
        })
    }

    fn resolve_ret(r: ScriptOperand, temps: &[[VarId; 2]]) -> Operand {
        match r {
            ScriptOperand::Ret { step, comp } => temps
                .get(step)
                .and_then(|t| t.get(usize::from(comp)))
                .map_or(Operand::Lit(-1), |v| Operand::Var(*v)),
            ScriptOperand::Lit(v) => Operand::Lit(i64::from(v)),
            ScriptOperand::Arg(_) => Operand::Lit(-1),
        }
    }

    /// The forked child of STD-SPAWN-FORK: std's child steps (a failing
    /// stdio `dup2` takes the error path, `unix.rs:288-296`), each `pre_exec`
    /// closure (an `Err` takes the error path), then `execvp` (whose failure
    /// takes it too). The error path is the row's: write the errno message to
    /// the status pipe, `_exit(1)`.
    fn child_body(
        &mut self,
        row: &StdRow,
        fr: &std_summaries::ForkRow,
        steps: Vec<(usize, Event)>,
        child_error: Vec<Call<Operand>>,
        hooks: &[BodyId],
        loc: &Loc,
    ) -> Body {
        let stmt = |kind| Stmt { kind, loc: loc.clone(), tag: None };
        // Block layout: one block per "checked" statement (a stdio dup2, a
        // hook call, execvp), each branching to `fail` on -1, then `fail`
        // and `done`.
        let mut blocks: Vec<Block> = Vec::new();
        let mut pending: Vec<Stmt> = Vec::new();
        let mut checked: Vec<(Vec<Stmt>, VarId)> = Vec::new();
        for (k, ev) in steps {
            let is_dup2 = matches!(ev.call, Call::Dup2 { .. } | Call::StdPlaceFd { .. });
            let ret = ev.bind.ret;
            pending.push(stmt(StmtKind::Event(ev)));
            if is_dup2
                && fr.row.retried_eintr.contains(&k)
                && let Some(r) = ret
            {
                checked.push((std::mem::take(&mut pending), r));
            }
        }
        for (i, h) in hooks.iter().enumerate() {
            let ret = self.temp(&format!("{}.pre_exec{i}", row.id));
            pending.push(stmt(StmtKind::Call { body: *h, args: Vec::new(), ret: Some(ret) }));
            checked.push((std::mem::take(&mut pending), ret));
        }
        let exec_ret = self.temp(&format!("{}.execvp", row.id));
        let exec_origin = StdOrigin { row: row.id, step: fr.exec, source: row.source };
        pending.push(stmt(StmtKind::Event(Event {
            symbol: "execvp".to_string(),
            call: Call::Exec,
            bind: Bind::ret(exec_ret),
            oracles: vec![Oracle::Nominal, Oracle::Fail(trust_platform::Errno::ENOENT)],
            site: None,
            ofd_names: Vec::new(),
            std_origin: Some(exec_origin.clone()),
            path: None,
            assumption: None,
        })));
        checked.push((pending, exec_ret));
        let n = checked.len();
        let (fail, done) = (n, n + 1);
        for (i, (stmts, ret)) in checked.into_iter().enumerate() {
            blocks.push(Block {
                stmts,
                term: Term::Branch {
                    cond: Cond::eq(Operand::Var(ret), Operand::Lit(-1)),
                    then: fail,
                    els: if i + 1 == n { done } else { i + 1 },
                },
                term_loc: loc.clone(),
                term_tag: None,
            });
        }
        let fail_stmts = child_error
            .into_iter()
            .map(|c| {
                stmt(StmtKind::Event(Event {
                    symbol: if matches!(c, Call::Exit { .. }) {
                        "_exit".to_string()
                    } else {
                        c.symbol().to_string()
                    },
                    call: c,
                    bind: Bind::none(),
                    oracles: vec![Oracle::Nominal],
                    site: None,
                    ofd_names: Vec::new(),
                    std_origin: Some(exec_origin.clone()),
                    path: None,
                    assumption: None,
                }))
            })
            .collect();
        blocks.push(Block {
            stmts: fail_stmts,
            term: Term::Return(None),
            term_loc: loc.clone(),
            term_tag: None,
        });
        blocks.push(Block {
            stmts: Vec::new(),
            term: Term::Return(None),
            term_loc: loc.clone(),
            term_tag: None,
        });
        Body { name: format!("{} child", row.id), params: Vec::new(), blocks }
    }
}

fn remap_term(term: &Term, map: &[usize]) -> Term {
    let m = |b: usize| map.get(b).copied().unwrap_or(b);
    match term {
        Term::Goto(b) => Term::Goto(m(*b)),
        Term::Branch { cond, then, els } => {
            Term::Branch { cond: cond.clone(), then: m(*then), els: m(*els) }
        }
        Term::Return(o) => Term::Return(*o),
    }
}

/// Lower one body: std calls expanded, a fork-path spawn splitting its block
/// on std's status read.
fn lower_body(l: &mut Lowerer<'_>, body: &Body, body_count: usize) -> Result<Body, LowerError> {
    // Pass 1: expand every statement; count the blocks each original block
    // becomes.
    let mut expanded: Vec<Vec<(Option<Expansion>, Stmt)>> = Vec::new();
    for block in &body.blocks {
        let mut v = Vec::new();
        for s in &block.stmts {
            match &s.kind {
                StmtKind::Std(call) => v.push((Some(l.expand(s, call, body_count)?), s.clone())),
                _ => v.push((None, s.clone())),
            }
        }
        expanded.push(v);
    }
    let mut first = Vec::with_capacity(body.blocks.len());
    let mut next = 0usize;
    for v in &expanded {
        first.push(next);
        let splits = v.iter().filter(|(e, _)| matches!(e, Some(Expansion::Split { .. }))).count();
        next += 1 + 3 * splits;
    }
    // Pass 2: emit.
    let mut blocks: Vec<Block> = Vec::with_capacity(next);
    for (bi, v) in expanded.into_iter().enumerate() {
        let orig = &body.blocks[bi];
        let mut cur: Vec<Stmt> = Vec::new();
        for (e, s) in v {
            match e {
                None => cur.push(s),
                Some(Expansion::Inline(stmts)) => cur.extend(stmts),
                Some(Expansion::Split { before, status, ok, err, loc }) => {
                    cur.extend(before);
                    let here = blocks.len();
                    let (ok_b, err_b, join) = (here + 1, here + 2, here + 3);
                    blocks.push(Block {
                        stmts: std::mem::take(&mut cur),
                        term: Term::Branch {
                            cond: Cond::eq(Operand::Var(status), Operand::Lit(0)),
                            then: ok_b,
                            els: err_b,
                        },
                        term_loc: loc.clone(),
                        term_tag: None,
                    });
                    for stmts in [ok, err] {
                        blocks.push(Block {
                            stmts,
                            term: Term::Goto(join),
                            term_loc: loc.clone(),
                            term_tag: None,
                        });
                    }
                }
            }
        }
        blocks.push(Block {
            stmts: cur,
            term: remap_term(&orig.term, &first),
            term_loc: orig.term_loc.clone(),
            term_tag: orig.term_tag.clone(),
        });
    }
    Ok(Body { blocks, ..body.clone() })
}

/// Lower a surface program and join it with the symbol table.
pub fn lower(src: &EventProgram) -> Result<CoreProgram, LowerError> {
    let mut l = Lowerer {
        src,
        vars: src.vars.clone(),
        new_bodies: Vec::new(),
        census: Vec::new(),
        next_temp: 0,
    };
    let body_count = src.bodies.len();
    let mut bodies = Vec::with_capacity(body_count);
    for body in &l.src.bodies {
        bodies.push(lower_body(&mut l, body, body_count)?);
    }
    bodies.append(&mut l.new_bodies);
    let mut prog = EventProgram { vars: l.vars, bodies, ..src.clone() };
    let mut census = l.census;
    let mut assumptions = Vec::new();

    // Validate references and join every non-std event with the symbol table.
    let nbodies = prog.bodies.len();
    let nvars = prog.vars.len();
    let mut defaults: Vec<(StmtRef, Vec<String>)> = Vec::new();
    for (at, s) in prog.stmts() {
        match &s.kind {
            StmtKind::Event(ev)
                if ev.std_origin.is_none()
                    && matches!(ev.call, Call::ReadSome { .. } | Call::WriteSome { .. }) =>
            {
                // A raw read/write: the model's ReadSome/WriteSome only with
                // the hand census's statement of why (I-FD-SPECIFIED).
                let Some(why) = &ev.assumption else {
                    return Err(LowerError::Unmodeled {
                        effect: UnmodeledPlatformEffect {
                            symbol: ev.symbol.clone(),
                            reason: "a read/write the census did not classify: only a few bytes \
                                     on a pipe or socketpair end is the model's ReadSome/WriteSome",
                        },
                        loc: s.loc.clone(),
                    });
                };
                if ev.symbol != ev.call.symbol() {
                    return Err(LowerError::SymbolMismatch {
                        symbol: ev.symbol.clone(),
                        call: ev.call.symbol(),
                        loc: s.loc.clone(),
                    });
                }
                assumptions.push(format!("{} at {}: {why}", ev.symbol, s.loc));
                census.push(CensusRow {
                    symbol: ev.symbol.clone(),
                    modeled: format!("{} (assumed: {why})", ev.call.symbol()),
                    loc: s.loc.clone(),
                });
            }
            StmtKind::Event(ev) => {
                if ev.std_origin.is_none() {
                    let l = symbols::lookup(&ev.symbol)
                        .map_err(|effect| LowerError::Unmodeled { effect, loc: s.loc.clone() })?;
                    match clause_of(&ev.call) {
                        Some(c) if l.modeled == Modeled::Clause(c) => {}
                        _ => {
                            return Err(LowerError::SymbolMismatch {
                                symbol: ev.symbol.clone(),
                                call: ev.call.symbol(),
                                loc: s.loc.clone(),
                            });
                        }
                    }
                    if let Some(a) = open_path_check(ev, &s.loc)? {
                        assumptions.push(a);
                    }
                    census.push(CensusRow {
                        symbol: ev.symbol.clone(),
                        modeled: format!("{:?}", l.modeled),
                        loc: s.loc.clone(),
                    });
                }
                for v in [ev.bind.ret, ev.bind.ret2, ev.bind.rlim_soft].into_iter().flatten() {
                    if v >= nvars {
                        return Err(LowerError::Malformed(format!("var {v} at {}", s.loc)));
                    }
                }
                let n = allocates(&ev.call);
                if ev.ofd_names.len() < n {
                    let mut names = ev.ofd_names.clone();
                    for c in names.len()..n {
                        names.push(format!("ofd_{at}_{c}"));
                    }
                    defaults.push((at, names));
                }
            }
            StmtKind::Neutral { symbol } => {
                let l = symbols::lookup(symbol)
                    .map_err(|effect| LowerError::Unmodeled { effect, loc: s.loc.clone() })?;
                if !matches!(l.modeled, Modeled::Neutral | Modeled::SpawnBuilder(_)) {
                    return Err(LowerError::SymbolMismatch {
                        symbol: symbol.clone(),
                        call: "neutral",
                        loc: s.loc.clone(),
                    });
                }
                census.push(CensusRow {
                    symbol: symbol.clone(),
                    modeled: format!("{:?}", l.modeled),
                    loc: s.loc.clone(),
                });
            }
            StmtKind::Call { body, .. } | StmtKind::ForRange { body, .. } => {
                if *body >= nbodies {
                    return Err(LowerError::Malformed(format!("body {body} at {}", s.loc)));
                }
            }
            StmtKind::Fork { child, std_origin, .. } => {
                if *child >= nbodies {
                    return Err(LowerError::Malformed(format!("child body {child}")));
                }
                // A raw libc `fork` the program calls itself (not a step of
                // STD-SPAWN-FORK): a census row like any other platform name.
                if std_origin.is_none() {
                    let l = symbols::lookup("fork")
                        .map_err(|effect| LowerError::Unmodeled { effect, loc: s.loc.clone() })?;
                    census.push(CensusRow {
                        symbol: "fork".to_string(),
                        modeled: format!("{:?}", l.modeled),
                        loc: s.loc.clone(),
                    });
                }
            }
            StmtKind::Std(_) => {
                return Err(LowerError::Malformed("std call survived lowering".to_string()));
            }
            StmtKind::SpawnThread { root } => {
                match prog.roots.get(*root) {
                    Some(r) if r.dormant => {}
                    _ => {
                        return Err(LowerError::Malformed(format!(
                            "spawn of root {root}, which is not a dormant thread root, at {}",
                            s.loc
                        )));
                    }
                }
                let l = symbols::lookup("pthread_create")
                    .map_err(|effect| LowerError::Unmodeled { effect, loc: s.loc.clone() })?;
                census.push(CensusRow {
                    symbol: "std::thread::spawn (pthread_create)".to_string(),
                    modeled: format!("{:?}", l.modeled),
                    loc: s.loc.clone(),
                });
            }
            StmtKind::Join { root } => {
                if *root >= prog.roots.len() {
                    return Err(LowerError::Malformed(format!("join of root {root} at {}", s.loc)));
                }
            }
            StmtKind::Release { .. } | StmtKind::Assign { .. } | StmtKind::Skip => {}
        }
    }
    for (at, names) in defaults {
        if let Some(StmtKind::Event(ev)) =
            prog.bodies[at.body].blocks[at.block].stmts.get_mut(at.idx).map(|s| &mut s.kind)
        {
            ev.ofd_names = names;
        }
    }
    // X1: no untracked value reaches an operand, a guard or a loop bound.
    crate::track::check(&prog)?;

    let m2_call = |c: &Call<Operand>| {
        matches!(
            c,
            Call::Flock { .. }
                | Call::OpenPath { .. }
                | Call::Fstat { .. }
                | Call::Mkfifo { .. }
                | Call::Unlink { .. }
                | Call::Symlink { .. }
        )
    };
    let lock_call = |c: &Call<Operand>| match c {
        Call::Flock { .. } => true,
        Call::OpenPath { flags, .. } => {
            flags & (trust_platform::darwin::O_EXLOCK | trust_platform::darwin::O_SHLOCK) != 0
        }
        _ => false,
    };
    let mut extended = prog.policies.lock_release || !prog.policies.fd_identity.is_empty();
    let mut locks = prog.policies.lock_release;
    for (_, s) in prog.stmts() {
        match &s.kind {
            StmtKind::Event(ev) => {
                extended |= m2_call(&ev.call)
                    || (ev.std_origin.is_none()
                        && matches!(ev.call, Call::ReadSome { .. } | Call::WriteSome { .. }));
                locks |= lock_call(&ev.call);
            }
            StmtKind::Release { .. } | StmtKind::SpawnThread { .. } | StmtKind::Join { .. } => {
                extended = true;
            }
            _ => {}
        }
    }
    let mut core = CoreProgram {
        prog,
        classes: Vec::new(),
        declared: Vec::new(),
        census,
        assumptions,
        policy_reach: Vec::new(),
        body_reaches: Vec::new(),
        extended,
        child_splits: locks,
    };
    // Classes: fd parameters first (stable indices), then allocation sites.
    let params = core.prog.fd_params.clone();
    for p in &params {
        core.intern_class(&p.class);
        if let Some(pc) = &p.peer_class {
            core.intern_class(pc);
        }
    }
    let alloc_names: Vec<String> = core
        .prog
        .stmts()
        .filter_map(|(_, s)| match &s.kind {
            StmtKind::Event(ev) => Some(ev.ofd_names.clone()),
            _ => None,
        })
        .flatten()
        .collect();
    for n in alloc_names {
        core.intern_class(&n);
    }
    // Release markers name allocation classes; an unknown name is a typo that
    // would make the property vacuous for it.
    let released: Vec<(String, Loc)> = core
        .prog
        .stmts()
        .filter_map(|(_, s)| match &s.kind {
            StmtKind::Release { classes } => {
                Some(classes.iter().map(|c| (c.clone(), s.loc.clone())).collect::<Vec<_>>())
            }
            _ => None,
        })
        .flatten()
        .collect();
    for (c, loc) in released {
        if core.class_idx(&c).is_none() {
            return Err(LowerError::Malformed(format!(
                "release of `{c}` at {loc}: no allocation site or descriptor argument has that class"
            )));
        }
    }
    core.declared = (0..core.prog.sites.len()).map(|s| declared_for(&mut core, s)).collect();
    core.compute_policy_reach();
    Ok(core)
}

/// The census's path check for an `open` event (I-FD-SPECIFIED): the path
/// must be named, an fdesc alias must be the alias clause and nothing else
/// may be, and an unclassified path is admitted only as a disclosed
/// assumption (a fresh vnode: not a FIFO, not an fdesc alias through a
/// symlink).
fn open_path_check(ev: &Event, loc: &Loc) -> Result<Option<String>, LowerError> {
    if !matches!(ev.call, Call::Open { .. } | Call::OpenAlias { .. }) {
        return Ok(None);
    }
    let unmodeled = |reason: &'static str| LowerError::Unmodeled {
        effect: UnmodeledPlatformEffect { symbol: ev.symbol.clone(), reason },
        loc: loc.clone(),
    };
    let Some(path) = &ev.path else {
        return Err(unmodeled(
            "an open whose path the census did not read: it could be an fdesc alias \
             (/dev/fd/N) or a FIFO",
        ));
    };
    match (symbols::classify_open_path(path), &ev.call) {
        (OpenPath::FdAlias(n), Call::OpenAlias { fd: Operand::Lit(m), .. })
            if i64::from(n) == *m =>
        {
            Ok(None)
        }
        (OpenPath::FdAlias(_), _) | (_, Call::OpenAlias { .. }) => {
            Err(LowerError::SymbolMismatch {
                symbol: format!("open(\"{path}\")"),
                call: ev.call.symbol(),
                loc: loc.clone(),
            })
        }
        // An ANONYMOUS open of a cloning or per-process device is what the
        // anonymous clause says — a fresh description on a node the model
        // does not name (each /dev/ptmx open IS a new device); only a NAMED
        // open, which would put every open on one node, refuses it.
        (OpenPath::Refused(why), _) => Ok(Some(format!(
            "open(\"{path}\") at {loc}: a fresh description on a device the model does not name \
             ({why})"
        ))),
        (OpenPath::DevNull, _) => Ok(None),
        (OpenPath::Other, _) if ev.assumption.is_some() => Ok(Some(format!(
            "open(\"{path}\") at {loc}: {}",
            ev.assumption.as_deref().unwrap_or_default()
        ))),
        (OpenPath::Other, _) => Ok(Some(format!(
            "open(\"{path}\") at {loc} is assumed to name a fresh vnode (not a FIFO, not an \
             fdesc alias through a symlink)"
        ))),
    }
}

fn declared_for(core: &mut CoreProgram, site: SiteId) -> Option<Declared> {
    let policy = core.prog.sites.get(site)?.policy.clone()?;
    let mut allowed: std::collections::BTreeSet<i32> = [0, 1, 2].into_iter().collect();
    let mut required: BTreeMap<i32, Option<usize>> = BTreeMap::new();
    for lane in &policy.lanes {
        allowed.insert(lane.fd);
        let class = core.intern_class(&lane.ofd_class);
        required.insert(lane.fd, Some(class));
    }
    Some(Declared { allowed, required: required.into_iter().collect() })
}

#[cfg(test)]
mod command_row_tests {
    use trust_platform::script::Guard;

    use super::*;
    use crate::program::ProgramBuilder;

    #[test]
    fn current_command_support_does_not_admit_missing_hooks_or_unsupported_shapes() {
        for (stdio, shape, want) in [
            (
                [StdioPlan::Piped, StdioPlan::Inherit, StdioPlan::Inherit],
                CommandShape::default(),
                "piped",
            ),
            (
                [StdioPlan::Inherit; 3],
                CommandShape { setsid: true, ..CommandShape::default() },
                "setsid",
            ),
            ([StdioPlan::Inherit; 3], CommandShape::with_pre_exec(), "does not name"),
        ] {
            let mut p = ProgramBuilder::new("unsupported_current_command");
            let site = p.site("child", "command-row:control", None);
            let main = p.body("main", Vec::new(), |b| {
                b.spawn("command-row:control", stdio, shape, Vec::new(), site, None);
            });
            p.root("main", main);
            match lower(&p.build()) {
                Err(LowerError::BadStdRow { detail, .. }) => {
                    assert!(detail.to_ascii_lowercase().contains(want), "{detail}");
                }
                other => panic!("expected the {want} refusal, got {other:?}"),
            }
        }
    }

    #[test]
    fn future_command_guards_assumptions_and_oracles_are_not_erased() {
        let (row, _) =
            std_summaries::command_spawn_posix([StdioPlan::Inherit; 3], &CommandShape::default())
                .unwrap();
        let loc = Loc("command-row:control".into());
        Lowerer::command_row(&row, &loc).unwrap();
        for variant in 0..3 {
            let mut mutant = row.clone();
            let step = mutant.program[0].clone();
            mutant.program[0] = match variant {
                0 => step.when(Guard::Below(ScriptOperand::Lit(0), 1), ScriptOperand::Lit(0)),
                1 => step.assuming(Guard::Below(ScriptOperand::Lit(0), 1), "unsupported branch"),
                _ => step.with_oracle(Oracle::Fail(trust_platform::Errno::EINTR)),
            };
            assert!(matches!(
                Lowerer::command_row(&mutant, &loc),
                Err(LowerError::BadStdRow { .. })
            ));
        }
    }
}
