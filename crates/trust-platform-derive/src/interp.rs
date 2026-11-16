//! The event-program interpreter over `trust_platform::step` — the one
//! Darwin definition (SD-9) — at the REAL constants. The exploration
//! ([`crate::explore`]) and the replay ([`crate::trace`]) run the same code.
//!
//! * Actors are the program's thread roots (all threads of the root
//!   process) and the children its fork sites create. Each actor has its own
//!   copy of the program variables (a forked child copies its parent's).
//! * An actor is *settled* when its next statement is an interleaving point
//!   (an event, a fork, a strip loop) or it has finished; local statements
//!   (assignments, calls, branches) run while settling.
//! * A forked child runs from the fork to its `execvp` (or `_exit`) as one
//!   macro step (SD-3: edits to the child's own table commute with every
//!   other process's events). Its events are logged individually, so a trace
//!   still shows each one. A child-side event on a shared object (a blocking
//!   read, a fork, a spawn) would need a split point and is refused; so is a
//!   call that is not async-signal-safe in the child of a multithreaded
//!   parent (DR-1).
//! * A `fork` or `posix_spawn` taken while another thread of the root is
//!   about to replace a slot (`dup2` onto an open descriptor) or to move a
//!   description (`F_DUPFD` then `close` of the source) may copy a TORN table
//!   that lacks that slot (`trust_platform::clauses::step_torn`, measured);
//!   the exploration takes those outcomes too.
//!
//! M2 additions (only in a program that uses them; an M1 program runs as
//! before):
//!
//! * **Thread start and join.** A dormant thread root starts at another
//!   actor's [`StmtKind::SpawnThread`] (one `pthread_create`), with a copy of
//!   the spawner's variables; [`StmtKind::Join`] waits for it to finish.
//! * **Child split points** ([`CoreProgram::child_splits`]): a forked child
//!   runs as one macro step only up to its next event that can change state
//!   another process sees ([`Interp::at_split`]); from there it interleaves
//!   like a thread. Its blocking reads are then "not enabled", not refused.
//! * **fd-identity.** Every actor of a program under fd-identity keeps, per
//!   descriptor NUMBER, the description it last bound there (an allocation, a
//!   `dup2` target), or "closed" (its own `close`), or what it first observed
//!   there; a thread starts with its creator's bindings, a forked child with
//!   its parent's, and a `join` hands the joiner what the joined thread wrote
//!   (happens-before). Each event of a CHECKED actor (a listed thread root, a
//!   forked child of a checked actor) on a number must reach that description
//!   ([`IdentityViolation`] otherwise; the first is kept in the state). An
//!   `fstat` is exempt: its result IS the identity of what the number names,
//!   which the program compares, so it presumes nothing. RL-FOREIGN may squat
//!   on any number an actor retired ([`Interp::squat_targets`]).
//! * **Release marks** ([`StmtKind::Release`]) let go of every live
//!   description of their classes ([`Config::released`]); the owner's exit
//!   lets go of everything; [`Config::owner_locks`] says whose lock a
//!   description holds (P-LOCK-RELEASE).
//! * **Calls in flight** (the M2 review): a `posix_spawn` is its copy, then
//!   (after any interleaving) its file actions and image; an `open` that waits
//!   and a `flock` that sleeps return [`Ret::Pending`] and are continued by a
//!   later firing of their actor ([`Pending`]).

use std::collections::{BTreeMap, BTreeSet};

use trust_platform::clauses::{spawn_refusal, step_torn};
use trust_platform::{
    Call, Errno, FileAction, Host, OfdId, Oracle, Phase, Pid, Refusal, Ret, SysResult, darwin,
    symbols,
};

use crate::lower::CoreProgram;
use crate::program::{
    BlockId, BodyId, CmpOp, Cond, Event, Expr, Operand, SiteId, StmtKind, StmtRef, Term, VarId,
};

/// Who acts.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Role {
    /// Thread root `i` of the root process.
    Thread(usize),
    /// The `nth` child forked at `site`.
    Child { site: SiteId, nth: u32 },
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Frame {
    pub body: BodyId,
    pub block: BlockId,
    pub idx: usize,
    /// Where the caller wants the return value.
    pub ret: Option<VarId>,
}

/// What an fd-identity-checked actor believes a descriptor NUMBER names.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Binding {
    /// This description (bound by an allocation, a `dup2`, or observed).
    Ofd(OfdId),
    /// Nothing: the actor closed it (or observed it closed).
    Closed,
    /// The description it was bound to no longer exists anywhere.
    Gone,
}

impl Binding {
    /// Whether the number naming `found` (or nothing) is what the actor
    /// believes.
    #[must_use]
    pub fn matches(self, found: Option<OfdId>) -> bool {
        match self {
            Binding::Ofd(o) => found == Some(o),
            Binding::Closed => found.is_none(),
            Binding::Gone => false,
        }
    }
}

/// The first fd-identity violation of a run: a checked actor's event on a
/// descriptor number reached something other than what it bound there.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct IdentityViolation {
    pub role: Role,
    pub at: StmtRef,
    pub fd: i32,
    /// What the actor bound the number to (a class, or "closed").
    pub believed: String,
    /// What the number named when the event ran (a class, or "closed").
    pub found: String,
}

/// A call an actor made that has not returned (M2 review): the actor's pc
/// stays at the event, and its next firing continues the call.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Pending {
    /// A `posix_spawn` between its halves ([`Call::SpawnBegin`] done; the
    /// child holds a copy of the whole table): next, [`Call::SpawnEnd`].
    Spawn { child: Pid },
    /// An `open` that waits or a `flock` that sleeps on this number
    /// ([`Ret::Pending`]): next, [`Call::Resume`].
    Resume { fd: i32 },
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Actor {
    pub role: Role,
    pub pid: Pid,
    /// Empty once the actor has finished (returned, exec'd or exited).
    pub frames: Vec<Frame>,
    pub vars: Vec<i64>,
    /// fd-identity: what this actor believes each number names. Kept by
    /// EVERY actor of a program under fd-identity (a thread inherits its
    /// creator's, a forked child its parent's, a joiner takes the joined
    /// thread's writes); empty otherwise.
    pub bindings: BTreeMap<i32, Binding>,
    /// fd-identity: the numbers this actor rebound itself since it started
    /// (an allocation, a `dup2` target, its `close`) — what a `join` hands
    /// the joiner (happens-before).
    pub wrote: BTreeSet<i32>,
    /// fd-identity: this actor's events are checked against its bindings (a
    /// listed thread root, or a forked child of a checked actor).
    pub checked: bool,
    /// P-LOCK-RELEASE: release marks not yet applied to the configuration
    /// (transient: [`Interp::finish`] turns them into
    /// [`Config::released`]).
    pub released: BTreeSet<usize>,
    /// A call this actor made that has not returned.
    pub pending: Option<Pending>,
}

impl Actor {
    #[must_use]
    pub fn done(&self) -> bool {
        self.frames.is_empty()
    }

    #[must_use]
    pub fn pc(&self) -> Option<StmtRef> {
        self.frames.last().map(|f| StmtRef { body: f.body, block: f.block, idx: f.idx })
    }
}

/// A child a spawn site created.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct SpawnRecord {
    pub site: SiteId,
    pub nth: u32,
    pub pid: Pid,
    /// The child runs an exec'd image (posix_spawn children are born so).
    pub execd: bool,
    /// The fd-bound premise held in the parent at the moment its table was
    /// copied for this child (the snapshot that decides what it inherits).
    pub premise: bool,
    /// Descriptors this child's own setup placed or un-flagged, by number
    /// (the dynamic part of `Declared`).
    pub declared: BTreeSet<i32>,
    /// The child was reaped: its pid may be reused and names it no more.
    pub gone: bool,
}

/// One explored state.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Config {
    pub host: Host,
    /// Allocation-site class of every live open file description.
    pub classes: BTreeMap<OfdId, usize>,
    pub actors: Vec<Actor>,
    pub spawns: Vec<SpawnRecord>,
    /// The first fd-identity violation (sticky; M2).
    pub identity_violation: Option<IdentityViolation>,
    /// P-LOCK-RELEASE: the descriptions an owner's release mark let go — every
    /// live description of a released class when the mark ran (or every live
    /// one when the owner process exited).
    pub released: BTreeSet<OfdId>,
    /// P-LOCK-RELEASE: the descriptions whose current lock the owner (root)
    /// process took (not a child that locked a copy on its own).
    pub owner_locks: BTreeSet<OfdId>,
}

impl Config {
    /// The live spawn record of `pid`.
    #[must_use]
    pub fn record(&self, pid: Pid) -> Option<&SpawnRecord> {
        self.spawns.iter().find(|r| r.pid == pid && !r.gone)
    }

    fn record_mut(&mut self, pid: Pid) -> Option<&mut SpawnRecord> {
        self.spawns.iter_mut().find(|r| r.pid == pid && !r.gone)
    }
}

/// One executed platform event (or strip loop), for traces.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Fired {
    pub role: Role,
    pub at: StmtRef,
    pub oracle: Oracle,
    /// Slots a torn table copy missed (fork / posix_spawn only).
    pub missed: Vec<i32>,
    pub pid: Pid,
    pub call: Option<Call<i32>>,
    pub result: Option<SysResult>,
    pub note: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InterpError {
    /// The model refused a step (an unmodeled effect is a named Unknown).
    Refused {
        at: StmtRef,
        refusal: Refusal,
    },
    /// DR-1: a call that is not async-signal-safe in the child of a fork made
    /// by a multithreaded process (it can deadlock there, holding every
    /// inherited descriptor).
    NotAsyncSignalSafe {
        at: StmtRef,
        symbol: String,
        parent_threads: u32,
    },
    /// A shape M1 does not handle (named, never skipped).
    Unsupported {
        at: Option<StmtRef>,
        detail: String,
    },
    /// A forked child's macro step (SD-3) fired more than
    /// [`MAX_CHILD_EVENTS`] events: a loop in the child that is not one
    /// `ForRange` step. Refused, never truncated: the exploration's state
    /// budget does not see inside a macro step, so without this bound one
    /// step could run (and log) unboundedly.
    Bound {
        at: Option<StmtRef>,
        events: usize,
    },
    Malformed(String),
}

impl std::fmt::Display for InterpError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            InterpError::Refused { at, refusal } => write!(f, "{at}: {refusal}"),
            InterpError::NotAsyncSignalSafe { at, symbol, parent_threads } => write!(
                f,
                "{at}: DR-1: `{symbol}` is not async-signal-safe in the child of a fork made by \
                 a process with {parent_threads} threads"
            ),
            InterpError::Unsupported { at, detail } => match at {
                Some(at) => write!(f, "{at}: unsupported: {detail}"),
                None => write!(f, "unsupported: {detail}"),
            },
            InterpError::Bound { at, events } => {
                if let Some(at) = at {
                    write!(f, "{at}: ")?;
                }
                write!(
                    f,
                    "a forked child's macro step exceeds {events} events (bound \
                     {MAX_CHILD_EVENTS}): a loop in the child that is not one ForRange step"
                )
            }
            InterpError::Malformed(s) => write!(f, "malformed: {s}"),
        }
    }
}

/// The interpreter for one lowered program.
pub struct Interp<'a> {
    pub core: &'a CoreProgram,
    /// The root process.
    pub root: Pid,
    /// The fd-bound premise's cap, if the program states it.
    pub fd_bound_cap: Option<i64>,
}

const LOCAL_FUEL: usize = 100_000;

/// The most events one forked child fires in one macro step (SD-3) before
/// the step is refused ([`InterpError::Bound`]). Host-independent (counted
/// in events, not time or memory); far above any straight-line child setup,
/// far below a CFG strip loop over the descriptor range.
pub const MAX_CHILD_EVENTS: usize = 4096;

/// The number of torn variants of one fork/spawn explored at most
/// (subsets of the racy slots); more racy slots is a named bound error.
const MAX_RACY_SLOTS: usize = 3;

impl Interp<'_> {
    // ---- scalars -----------------------------------------------------------

    fn val(a: &Actor, op: &Operand) -> Result<i64, InterpError> {
        match op {
            Operand::Lit(v) => Ok(*v),
            Operand::Var(x) => {
                a.vars.get(*x).copied().ok_or_else(|| InterpError::Malformed(format!("var {x}")))
            }
        }
    }

    fn eval(a: &Actor, e: &Expr) -> Result<i64, InterpError> {
        Ok(match e {
            Expr::Use(o) => Self::val(a, o)?,
            Expr::Add(x, y) => Self::val(a, x)?.saturating_add(Self::val(a, y)?),
            Expr::Min(x, y) => Self::val(a, x)?.min(Self::val(a, y)?),
            Expr::BitAnd(x, y) => Self::val(a, x)? & Self::val(a, y)?,
            // X1: decides nothing (`crate::track::check` refused every
            // program in which it could).
            Expr::Opaque => crate::track::OPAQUE_VALUE,
        })
    }

    /// A guard's value, three-valued (Kleene) over [`Cond::Nondet`]: `None`
    /// when it depends on an untracked guard. Without `Nondet` it is the
    /// two-valued, short-circuit evaluation (the right operand of a decided
    /// `&&`/`||` is not evaluated).
    pub(crate) fn cond3(a: &Actor, c: &Cond) -> Result<Option<bool>, InterpError> {
        Ok(match c {
            Cond::Const(b) => Some(*b),
            Cond::Nondet => None,
            Cond::Not(x) => Self::cond3(a, x)?.map(|b| !b),
            Cond::And(x, y) => match Self::cond3(a, x)? {
                Some(false) => Some(false),
                Some(true) => Self::cond3(a, y)?,
                None => match Self::cond3(a, y)? {
                    Some(false) => Some(false),
                    _ => None,
                },
            },
            Cond::Or(x, y) => match Self::cond3(a, x)? {
                Some(true) => Some(true),
                Some(false) => Self::cond3(a, y)?,
                None => match Self::cond3(a, y)? {
                    Some(true) => Some(true),
                    _ => None,
                },
            },
            Cond::Cmp(op, x, y) => {
                let (x, y) = (Self::val(a, x)?, Self::val(a, y)?);
                Some(match op {
                    CmpOp::Eq => x == y,
                    CmpOp::Ne => x != y,
                    CmpOp::Lt => x < y,
                    CmpOp::Le => x <= y,
                    CmpOp::Gt => x > y,
                    CmpOp::Ge => x >= y,
                })
            }
        })
    }

    // ---- local execution ---------------------------------------------------

    /// Run local statements until the next interleaving point or the end.
    pub fn settle(&self, a: &mut Actor) -> Result<(), InterpError> {
        for _ in 0..LOCAL_FUEL {
            let Some(f) = a.frames.last().cloned() else { return Ok(()) };
            let block = self
                .core
                .prog
                .bodies
                .get(f.body)
                .and_then(|b| b.blocks.get(f.block))
                .ok_or_else(|| InterpError::Malformed(format!("pc b{}.{}", f.body, f.block)))?;
            if let Some(s) = block.stmts.get(f.idx) {
                match &s.kind {
                    StmtKind::Event(_)
                    | StmtKind::Fork { .. }
                    | StmtKind::ForRange { .. }
                    | StmtKind::SpawnThread { .. }
                    | StmtKind::Join { .. } => {
                        return Ok(());
                    }
                    StmtKind::Release { classes } => {
                        for c in classes {
                            let k = self.core.class_idx(c).ok_or_else(|| {
                                InterpError::Malformed(format!("release of unknown class {c}"))
                            })?;
                            a.released.insert(k);
                        }
                        Self::advance(a);
                    }
                    StmtKind::Assign { var, expr } => {
                        let v = Self::eval(a, expr)?;
                        a.vars[*var] = v;
                        Self::advance(a);
                    }
                    StmtKind::Skip | StmtKind::Neutral { .. } => Self::advance(a),
                    StmtKind::Call { body, args, ret } => {
                        let vals: Vec<(VarId, i64)> = args
                            .iter()
                            .map(|(v, op)| Self::val(a, op).map(|x| (*v, x)))
                            .collect::<Result<_, _>>()?;
                        for (v, x) in vals {
                            a.vars[v] = x;
                        }
                        Self::advance(a);
                        a.frames.push(Frame { body: *body, block: 0, idx: 0, ret: *ret });
                    }
                    StmtKind::Std(_) => {
                        return Err(InterpError::Malformed("surface std call in core".into()));
                    }
                }
                continue;
            }
            match &block.term {
                Term::Goto(b) => Self::jump(a, *b),
                Term::Branch { cond, then, els } => match Self::cond3(a, cond)? {
                    Some(t) => Self::jump(a, if t { *then } else { *els }),
                    // X1: an undecided guard is a choice step
                    // (`crate::nondet`): the actor is settled here, at its
                    // block's terminator.
                    None => return Ok(()),
                },
                Term::Return(op) => {
                    let v = match op {
                        Some(o) => Self::val(a, o)?,
                        None => 0,
                    };
                    let done = a.frames.pop();
                    if let Some(Frame { ret: Some(r), .. }) = done
                        && !a.frames.is_empty()
                    {
                        a.vars[r] = v;
                    }
                }
            }
        }
        Err(InterpError::Malformed("a local loop ran without reaching an event".into()))
    }

    fn advance(a: &mut Actor) {
        if let Some(f) = a.frames.last_mut() {
            f.idx += 1;
        }
    }

    pub(crate) fn jump(a: &mut Actor, b: BlockId) {
        if let Some(f) = a.frames.last_mut() {
            f.block = b;
            f.idx = 0;
        }
    }

    /// The statement an actor is settled at.
    #[must_use]
    pub fn at(&self, a: &Actor) -> Option<(StmtRef, &StmtKind)> {
        let at = a.pc()?;
        self.core.prog.stmt(at).map(|s| (at, &s.kind))
    }

    /// The oracle choices of the statement an actor is settled at. A split
    /// `posix_spawn` may fail at its copy only as fork1 does (`EAGAIN`,
    /// `ENOMEM`), every listed failure at its end; a sleeping call may be
    /// interrupted (`EINTR`) when the event lists it, a fresh `flock` never.
    #[must_use]
    pub fn oracles(&self, a: &Actor) -> Vec<Oracle> {
        match self.at(a) {
            Some((_, StmtKind::Event(ev))) => {
                let listed = |keep: &dyn Fn(Errno) -> bool| -> Vec<Oracle> {
                    ev.oracles
                        .iter()
                        .copied()
                        .filter(|o| match o {
                            Oracle::Nominal => true,
                            Oracle::Fail(e) => keep(*e),
                        })
                        .collect()
                };
                let fork1 = |e: Errno| matches!(e, Errno::EAGAIN | Errno::ENOMEM);
                match (a.pending, &ev.call) {
                    (Some(Pending::Resume { .. }), _) => {
                        let mut v = vec![Oracle::Nominal];
                        if ev.oracles.contains(&Oracle::Fail(Errno::EINTR)) {
                            v.push(Oracle::Fail(Errno::EINTR));
                        }
                        v
                    }
                    (Some(Pending::Spawn { .. }), _) => ev.oracles.clone(),
                    (None, Call::Spawn { .. }) if self.splits_spawn() => {
                        // The copy is made unless fork1 fails; every other
                        // outcome (success, an action's or the image's
                        // failure) is decided at the end, after the window.
                        let past_copy =
                            ev.oracles.iter().any(|o| !matches!(o, Oracle::Fail(e) if fork1(*e)));
                        let mut v: Vec<Oracle> =
                            if past_copy { vec![Oracle::Nominal] } else { Vec::new() };
                        v.extend(
                            ev.oracles
                                .iter()
                                .copied()
                                .filter(|o| matches!(o, Oracle::Fail(e) if fork1(*e))),
                        );
                        v
                    }
                    (None, Call::Flock { .. }) => listed(&|e| e != Errno::EINTR),
                    (None, _) => ev.oracles.clone(),
                }
            }
            Some(_) => vec![Oracle::Nominal],
            None => Vec::new(),
        }
    }

    /// Whether a `posix_spawn` is two events here (its copy, then its file
    /// actions and image): in a program that uses M2 features. An M1
    /// program's spawn stays one event — its fd-inherit verdicts depend only
    /// on the exec'd table, which the window does not change.
    #[must_use]
    pub fn splits_spawn(&self) -> bool {
        self.core.extended
    }

    /// Whether actors keep fd-identity bindings (a program under fd-identity).
    #[must_use]
    pub fn tracks(&self) -> bool {
        !self.core.prog.policies.fd_identity.is_empty()
    }

    // ---- platform events ---------------------------------------------------

    fn concrete_call(a: &Actor, ev: &Event) -> Result<Call<i32>, InterpError> {
        let mut err = None;
        let call = ev.call.map(|op| match Self::val(a, op) {
            Ok(v) => i32::try_from(v).unwrap_or_else(|_| {
                err = Some(InterpError::Malformed(format!("operand {v} is not an int")));
                -1
            }),
            Err(e) => {
                err = Some(e);
                -1
            }
        });
        match err {
            Some(e) => Err(e),
            None => Ok(call),
        }
    }

    /// Name every description `ev` minted.
    fn classify(
        &self,
        before: &Host,
        c: &mut Config,
        pid: Pid,
        ev: &Event,
        call: &Call<i32>,
        result: &SysResult,
    ) -> Result<(), InterpError> {
        let old: BTreeSet<OfdId> = before.ofds().map(|(o, _)| o).collect();
        let fresh: Vec<OfdId> =
            c.host.ofds().map(|(o, _)| o).filter(|o| !old.contains(o)).collect();
        c.classes.retain(|o, _| c.host.ofd(*o).is_some());
        if fresh.is_empty() {
            return Ok(());
        }
        // Which (pid, fd) each result component landed on.
        let mut spots: Vec<(Pid, i32)> = Vec::new();
        match (call, result) {
            (_, Ok(Ret::Pair(x, y))) => spots.extend([(pid, *x), (pid, *y)]),
            (Call::Spawn { actions, .. }, Ok(Ret::Int(child))) => {
                let child = Pid(u32::try_from(*child).unwrap_or(0));
                for a in actions {
                    if let FileAction::Open { fd, .. } = a {
                        spots.push((child, *fd));
                    }
                }
            }
            (_, Ok(Ret::Int(n))) => spots.push((pid, i32::try_from(*n).unwrap_or(-1))),
            _ => {}
        }
        for o in fresh {
            let k = spots
                .iter()
                .position(|(p, fd)| c.host.entry(*p, *fd).is_some_and(|e| e.ofd == o))
                .unwrap_or(0);
            let name = ev.ofd_names.get(k).ok_or_else(|| {
                InterpError::Malformed(format!("`{}` minted an unnamed description", ev.symbol))
            })?;
            let cls = self
                .core
                .class_idx(name)
                .ok_or_else(|| InterpError::Malformed(format!("class {name} not interned")))?;
            c.classes.insert(o, cls);
        }
        Ok(())
    }

    fn bind(a: &mut Actor, ev: &Event, result: &SysResult) {
        let (r0, r1, soft) = match result {
            Ok(Ret::Int(n)) => (*n, -1, None),
            // fstat: the node identity and the file type.
            Ok(Ret::Stat { node, ftype }) => {
                (i64::try_from(*node).unwrap_or(i64::MAX), i64::from(*ftype), None)
            }
            Ok(Ret::Pair(x, y)) => (i64::from(*x), i64::from(*y), None),
            Ok(Ret::Rlimit { soft, .. }) => (0, -1, Some(i64::try_from(*soft).unwrap_or(i64::MAX))),
            Ok(Ret::NoReturn) => (0, -1, None),
            // Not returned yet: nothing is bound.
            Ok(Ret::Pending { .. }) => return,
            Err(_) => (-1, -1, None),
        };
        if let Some(v) = ev.bind.ret {
            a.vars[v] = r0;
        }
        if let Some(v) = ev.bind.ret2 {
            a.vars[v] = r1;
        }
        if let (Some(v), Some(s)) = (ev.bind.rlim_soft, soft) {
            a.vars[v] = s;
        }
    }

    /// Whether the description at `pid`'s `fd` in `c` is one the program may
    /// declare as a lane: anything but an RL-INIT FOREIGN description (an
    /// allocation site of the program, a descriptor argument or its peer,
    /// stdio). Placing or un-flagging a description the program never
    /// created declares nothing — inheriting it is the leak fd-inherit
    /// reports; deliberate transparent inheritance is a site-scoped intent
    /// (design Critique C-10), never implicit.
    fn owned_lane(&self, c: &Config, pid: Pid, fd: i32) -> bool {
        c.host
            .entry(pid, fd)
            .and_then(|e| c.classes.get(&e.ofd))
            .and_then(|k| self.core.classes.get(*k))
            .is_some_and(|class| class != crate::env::FOREIGN)
    }

    /// The descriptor a successful call by a policy child's setup places or
    /// un-flags (the dynamic part of `Declared`), in the state `c` AFTER the
    /// call — only when the description now there is one the program owns
    /// ([`Self::owned_lane`]).
    fn declares(&self, c: &Config, pid: Pid, call: &Call<i32>) -> Option<i32> {
        let fd = match *call {
            Call::Dup2 { to, .. } | Call::StdPlaceFd { to, .. } => to,
            Call::StdClearCloexec { fd } => fd,
            Call::Fcntl { fd, cmd, arg }
                if cmd == darwin::F_SETFD && arg & darwin::FD_CLOEXEC == 0 =>
            {
                fd
            }
            Call::Ioctl { fd, request, .. } if request == darwin::FIONCLEX => fd,
            _ => return None,
        };
        self.owned_lane(c, pid, fd).then_some(fd)
    }

    /// The descriptors a `posix_spawn`'s actions declare for its child: an
    /// `addopen` target, and a `adddup2`/`addinherit_np` of a description the
    /// program owns in the parent `before` the spawn ([`Self::owned_lane`]).
    fn spawn_declares(&self, before: &Config, pid: Pid, call: &Call<i32>) -> BTreeSet<i32> {
        let Call::Spawn { actions, .. } = call else { return BTreeSet::new() };
        actions
            .iter()
            .filter_map(|a| match *a {
                FileAction::Dup2 { from, to } | FileAction::PlaceStdio { from, to } => {
                    self.owned_lane(before, pid, from).then_some(to)
                }
                FileAction::Inherit { fd } => self.owned_lane(before, pid, fd).then_some(fd),
                FileAction::InheritIf { fd, enabled: 1 } => {
                    self.owned_lane(before, pid, fd).then_some(fd)
                }
                FileAction::InheritIf { .. } => None,
                FileAction::Open { fd, .. } => Some(fd),
                FileAction::Close { .. } | FileAction::Chdir | FileAction::Fchdir { .. } => None,
            })
            .collect()
    }

    /// DR-1: in the child of a fork made by a multithreaded process, every
    /// event must be async-signal-safe.
    fn check_dr1(
        &self,
        cfg: &Config,
        pid: Pid,
        at: StmtRef,
        ev: &Event,
    ) -> Result<(), InterpError> {
        if let Some(Phase::ForkedPreExec { parent_threads }) = cfg.host.proc(pid).map(|p| p.phase)
            && parent_threads > 1
            && !symbols::async_signal_safe(&ev.symbol)
            // These std-only events compose fcntl/dup2 and the child's
            // syscall-only strip. Their modeled allocation is not a call
            // to an allocator in the real forked child.
            && !(ev.std_origin.is_some()
                && matches!(ev.call,
                    Call::StdPlaceFd { .. } | Call::StdClearCloexec { .. }
                    | Call::StdMarkCloexec))
        {
            return Err(InterpError::NotAsyncSignalSafe {
                at,
                symbol: ev.symbol.clone(),
                parent_threads,
            });
        }
        Ok(())
    }

    /// Slots another thread of the root is about to replace or move: a
    /// `fork`/`posix_spawn` copying the table now may miss them (measured;
    /// `trust_platform::clauses::step_torn`).
    #[must_use]
    pub fn racy_slots(&self, cfg: &Config, i: usize) -> Vec<i32> {
        let me = &cfg.actors[i];
        let mut out: BTreeSet<i32> = BTreeSet::new();
        for (j, a) in cfg.actors.iter().enumerate() {
            if j == i || a.pid != me.pid || !matches!(a.role, Role::Thread(_)) || a.done() {
                continue;
            }
            let Some((at, StmtKind::Event(ev))) = self.at(a) else {
                continue;
            };
            let Ok(call) = Self::concrete_call(a, ev) else {
                continue;
            };
            let open = |fd: i32| cfg.host.entry(a.pid, fd).is_some();
            match call {
                // dup2 onto an open slot reserves it while it replaces it.
                Call::Dup2 { from, to } | Call::StdPlaceFd { from, to }
                    if from != to && open(to) && open(from) =>
                {
                    out.insert(to);
                }
                // F_DUPFD then close of the source: a move the copy can
                // straddle, finding the description in neither slot.
                Call::Fcntl { fd, cmd, .. }
                    if (cmd == darwin::F_DUPFD || cmd == darwin::F_DUPFD_CLOEXEC)
                        && open(fd)
                        && self.next_event_closes(at, &ev.call) =>
                {
                    out.insert(fd);
                }
                Call::StdStatusFd { fd }
                    if open(fd)
                        && self.next_event_closes(at, &ev.call)
                        && trust_platform::step(&cfg.host, a.pid, &call, Oracle::Nominal)
                            .is_ok_and(
                                |s| matches!(s.result, Ok(Ret::Int(n)) if n != i64::from(fd)),
                            ) =>
                {
                    out.insert(fd);
                }
                _ => {}
            }
        }
        out.into_iter().collect()
    }

    /// Whether the event after `at` in its block closes the descriptor the
    /// `F_DUPFD` at `at` duplicates (the same operand).
    fn next_event_closes(&self, at: StmtRef, call: &Call<Operand>) -> bool {
        let src = match call {
            Call::Fcntl { fd, .. } | Call::StdStatusFd { fd } => fd,
            _ => return false,
        };
        let Some(block) = self.core.prog.bodies.get(at.body).and_then(|b| b.blocks.get(at.block))
        else {
            return false;
        };
        let status_ret = block.stmts.get(at.idx).and_then(|s| match &s.kind {
            StmtKind::Event(e) if matches!(call, Call::StdStatusFd { .. }) => e.bind.ret,
            _ => None,
        });
        for s in block.stmts.iter().skip(at.idx + 1) {
            match &s.kind {
                StmtKind::Assign { var, .. }
                    if Operand::Var(*var) == *src || status_ret == Some(*var) =>
                {
                    return false;
                }
                StmtKind::Assign { .. } | StmtKind::Neutral { .. } | StmtKind::Skip => {}
                StmtKind::Event(e) => {
                    return match (call, &e.call) {
                        (Call::Fcntl { .. }, Call::Close { fd }) => fd == src,
                        (Call::StdStatusFd { .. }, Call::StdCloseMovedStatus { old, new }) => {
                            old == src && status_ret.is_some_and(|v| *new == Operand::Var(v))
                        }
                        _ => false,
                    };
                }
                _ => return false,
            }
        }
        false
    }

    /// The torn variants of a fork/spawn by actor `i`: every subset of its
    /// racy slots (the empty one is the atomic copy).
    pub fn torn_variants(&self, cfg: &Config, i: usize) -> Result<Vec<Vec<i32>>, InterpError> {
        let racy = self.racy_slots(cfg, i);
        if racy.len() > MAX_RACY_SLOTS {
            return Err(InterpError::Unsupported {
                at: cfg.actors[i].pc(),
                detail: format!(
                    "{} slots race this table copy (bound {MAX_RACY_SLOTS})",
                    racy.len()
                ),
            });
        }
        let mut out = Vec::new();
        for mask in 0u32..(1 << racy.len()) {
            out.push(
                racy.iter()
                    .enumerate()
                    .filter(|(b, _)| mask & (1 << b) != 0)
                    .map(|(_, fd)| *fd)
                    .collect(),
            );
        }
        Ok(out)
    }

    /// Execute the interleaving point actor `i` is settled at, with `oracle`
    /// (and, for a fork/spawn, a torn copy that `missed` these slots).
    /// `Ok(None)`: not enabled (blocks) in this state.
    pub fn fire(
        &self,
        cfg: &Config,
        i: usize,
        oracle: Oracle,
        missed: &[i32],
    ) -> Result<Option<(Config, Fired)>, InterpError> {
        let a = cfg.actors.get(i).ok_or_else(|| InterpError::Malformed("actor".into()))?;
        let Some((at, kind)) = self.at(a) else {
            return Err(InterpError::Malformed("firing a finished actor".into()));
        };
        let missed_set: BTreeSet<i32> = missed.iter().copied().collect();
        let role = a.role;
        let pid = a.pid;
        let mut c = cfg.clone();
        let fired = match kind {
            StmtKind::Event(ev) => {
                let call = Self::concrete_call(a, ev)?;
                if matches!(role, Role::Child { .. }) {
                    let io_ok = self.core.child_splits
                        && matches!(call, Call::ReadSome { .. } | Call::WriteSome { .. });
                    if !io_ok
                        && matches!(
                            call,
                            Call::Fork
                                | Call::Spawn { .. }
                                | Call::ReadSome { .. }
                                | Call::Waitpid { .. }
                                | Call::ThreadCreate
                        )
                    {
                        return Err(InterpError::Unsupported {
                            at: Some(at),
                            detail: format!(
                                "`{}` in a forked child touches a shared object: SD-3 split \
                                 points are not implemented",
                                call.symbol()
                            ),
                        });
                    }
                    self.check_dr1(cfg, pid, at, ev)?;
                }
                let root_thread = matches!(role, Role::Thread(_));
                if root_thread && matches!(call, Call::Exec) {
                    return Err(InterpError::Unsupported {
                        at: Some(at),
                        detail: "exec of the root process".to_string(),
                    });
                }
                if root_thread
                    && matches!(call, Call::Exit { .. })
                    && cfg.actors.iter().any(|x| x.pid == pid && x.pending.is_some())
                {
                    return Err(InterpError::Unsupported {
                        at: Some(at),
                        detail: "the root process exits while one of its calls is in flight"
                            .to_string(),
                    });
                }
                let resuming = a.pending;
                // What this firing executes: the call, its first half, or the
                // continuation of a call that has not returned.
                let exec_call = match (resuming, &call) {
                    (Some(Pending::Spawn { child }), Call::Spawn { actions, flags }) => {
                        Call::SpawnEnd {
                            child: i32::try_from(child.0).unwrap_or(-1),
                            actions: actions.clone(),
                            flags: *flags,
                        }
                    }
                    (Some(Pending::Resume { fd }), _) => Call::Resume { fd },
                    (Some(p), _) => {
                        return Err(InterpError::Malformed(format!(
                            "{p:?} pending at a `{}` event",
                            call.symbol()
                        )));
                    }
                    (None, Call::Spawn { actions, flags }) if self.splits_spawn() => {
                        if let Some(refusal) = spawn_refusal(actions, *flags) {
                            return Err(InterpError::Refused { at, refusal });
                        }
                        Call::SpawnBegin
                    }
                    (None, _) => call.clone(),
                };
                let premise = self.fd_bound_now(cfg);
                let step = match step_torn(&cfg.host, pid, &exec_call, oracle, &missed_set) {
                    Ok(s) => s,
                    Err(Refusal::Blocks) => return Ok(None),
                    Err(refusal) => return Err(InterpError::Refused { at, refusal }),
                };
                c.host = step.host;
                self.classify(&cfg.host, &mut c, pid, ev, &call, &step.result)?;
                self.track_locks(&cfg.host, &mut c, pid);
                if self.tracks() {
                    self.identity(cfg, &mut c, i, at, &call, &step.result, resuming.is_some());
                }
                let pending_now = match (&exec_call, &step.result) {
                    (Call::SpawnBegin, Ok(Ret::Int(child))) => {
                        Some(Pending::Spawn { child: Pid(u32::try_from(*child).unwrap_or(0)) })
                    }
                    (_, Ok(Ret::Pending { fd })) => Some(Pending::Resume { fd: *fd }),
                    _ => None,
                };
                if let Some(p) = pending_now {
                    // The call has not returned: the actor stays at it.
                    if let Pending::Spawn { child } = p {
                        let site = ev.site.ok_or_else(|| InterpError::Unsupported {
                            at: Some(at),
                            detail: "posix_spawn without a spawn site".to_string(),
                        })?;
                        let nth = Self::count_site(&c.spawns, site);
                        c.spawns.push(SpawnRecord {
                            site,
                            nth,
                            pid: child,
                            execd: false,
                            premise,
                            declared: self.spawn_declares(cfg, pid, &call),
                            gone: false,
                        });
                    }
                    c.actors[i].pending = Some(p);
                    return Ok(Some((
                        c,
                        Fired {
                            role,
                            at,
                            oracle,
                            missed: missed.to_vec(),
                            pid,
                            call: Some(exec_call),
                            result: Some(step.result),
                            note: "the call has not returned".to_string(),
                        },
                    )));
                }
                c.actors[i].pending = None;
                let declared =
                    if step.result.is_ok() { self.declares(&c, pid, &call) } else { None };
                if let Some(fd) = declared
                    && let Some(r) = c.record_mut(pid)
                {
                    r.declared.insert(fd);
                }
                let actor = &mut c.actors[i];
                Self::bind(actor, ev, &step.result);
                Self::advance(actor);
                match (&call, &step.result) {
                    (Call::Exec, Ok(_)) => {
                        actor.frames.clear();
                        if let Some(r) = c.record_mut(pid) {
                            r.execd = true;
                        }
                    }
                    (Call::Exit { .. }, Ok(_)) if root_thread => {
                        // The owner process is gone: every thread of it, and
                        // with it every description it let go (P-LOCK-RELEASE).
                        for x in &mut c.actors {
                            if x.pid == pid {
                                x.frames.clear();
                            }
                        }
                        let live: Vec<OfdId> = c.host.ofds().map(|(o, _)| o).collect();
                        c.released.extend(live);
                    }
                    (Call::Exit { .. }, Ok(_)) => actor.frames.clear(),
                    (Call::Spawn { .. }, Ok(Ret::Int(child))) => {
                        let child = Pid(u32::try_from(*child).unwrap_or(0));
                        if resuming.is_some() {
                            if let Some(r) = c.record_mut(child) {
                                r.execd = true;
                            }
                        } else {
                            let site = ev.site.ok_or_else(|| InterpError::Unsupported {
                                at: Some(at),
                                detail: "posix_spawn without a spawn site".to_string(),
                            })?;
                            let nth = Self::count_site(&c.spawns, site);
                            c.spawns.push(SpawnRecord {
                                site,
                                nth,
                                pid: child,
                                execd: true,
                                premise,
                                declared: self.spawn_declares(cfg, pid, &call),
                                gone: false,
                            });
                        }
                    }
                    _ => {}
                }
                self.settle(&mut c.actors[i])?;
                Fired {
                    role,
                    at,
                    oracle,
                    missed: missed.to_vec(),
                    pid,
                    call: Some(exec_call),
                    result: Some(step.result),
                    note: String::new(),
                }
            }
            StmtKind::Fork { child, site, bind, .. } => {
                if matches!(role, Role::Child { .. }) {
                    return Err(InterpError::Unsupported {
                        at: Some(at),
                        detail: "fork from a forked child".to_string(),
                    });
                }
                let premise = self.fd_bound_now(cfg);
                let step = match step_torn(&cfg.host, pid, &Call::Fork, oracle, &missed_set) {
                    Ok(s) => s,
                    Err(Refusal::Blocks) => return Ok(None),
                    Err(refusal) => return Err(InterpError::Refused { at, refusal }),
                };
                c.host = step.host;
                let child_pid = match step.result {
                    Ok(Ret::Int(n)) => Some(Pid(u32::try_from(n).unwrap_or(0))),
                    _ => None,
                };
                let parent = c.actors[i].clone();
                {
                    let actor = &mut c.actors[i];
                    if let Some(b) = bind {
                        actor.vars[*b] = child_pid.map_or(-1, |p| i64::from(p.0));
                    }
                    Self::advance(actor);
                }
                self.settle(&mut c.actors[i])?;
                if let Some(cp) = child_pid {
                    let nth = Self::count_site(&c.spawns, *site);
                    c.spawns.push(SpawnRecord {
                        site: *site,
                        nth,
                        pid: cp,
                        execd: false,
                        premise,
                        declared: BTreeSet::new(),
                        gone: false,
                    });
                    // A fork copies the forking thread: its view of the
                    // numbers (the child's table is the parent's) and whether
                    // its events are checked (fd-identity).
                    let mut kid = Actor {
                        role: Role::Child { site: *site, nth },
                        pid: cp,
                        frames: vec![Frame { body: *child, block: 0, idx: 0, ret: None }],
                        vars: parent.vars,
                        bindings: parent.bindings,
                        wrote: BTreeSet::new(),
                        checked: parent.checked,
                        released: BTreeSet::new(),
                        pending: None,
                    };
                    self.settle(&mut kid)?;
                    c.actors.push(kid);
                }
                Fired {
                    role,
                    at,
                    oracle,
                    missed: missed.to_vec(),
                    pid,
                    call: Some(Call::Fork),
                    result: Some(step.result),
                    note: String::new(),
                }
            }
            StmtKind::SpawnThread { root } => {
                let step = match step_torn(&cfg.host, pid, &Call::ThreadCreate, oracle, &missed_set)
                {
                    Ok(s) => s,
                    Err(Refusal::Blocks) => return Ok(None),
                    Err(refusal) => return Err(InterpError::Refused { at, refusal }),
                };
                c.host = step.host;
                let creator = c.actors[i].clone();
                Self::advance(&mut c.actors[i]);
                self.settle(&mut c.actors[i])?;
                if step.result.is_ok() {
                    let body =
                        self.core.prog.roots.get(*root).map(|r| r.body).ok_or_else(|| {
                            InterpError::Malformed(format!("spawn of unknown root {root}"))
                        })?;
                    let role_new = Role::Thread(*root);
                    // The thread starts knowing what its creator knew
                    // (happens-before), checked iff the policy lists it.
                    let mut t = Actor {
                        role: role_new,
                        pid,
                        frames: vec![Frame { body, block: 0, idx: 0, ret: None }],
                        vars: creator.vars.clone(),
                        bindings: creator.bindings.clone(),
                        wrote: BTreeSet::new(),
                        checked: self.listed(*root),
                        released: BTreeSet::new(),
                        pending: None,
                    };
                    self.settle(&mut t)?;
                    c.actors.push(t);
                }
                Fired {
                    role,
                    at,
                    oracle,
                    missed: Vec::new(),
                    pid,
                    call: Some(Call::ThreadCreate),
                    result: Some(step.result),
                    note: format!("starts thread `{}`", self.role_name(Role::Thread(*root))),
                }
            }
            StmtKind::Join { root } => {
                let Some(joined) =
                    cfg.actors.iter().find(|x| x.role == Role::Thread(*root) && x.done()).cloned()
                else {
                    return Ok(None);
                };
                // Happens-before: what the joined thread wrote is what the
                // joiner now knows.
                {
                    let me = &mut c.actors[i];
                    for n in &joined.wrote {
                        match joined.bindings.get(n) {
                            Some(b) => {
                                me.bindings.insert(*n, *b);
                            }
                            None => {
                                me.bindings.remove(n);
                            }
                        }
                    }
                    me.wrote.extend(joined.wrote.iter().copied());
                }
                Self::advance(&mut c.actors[i]);
                self.settle(&mut c.actors[i])?;
                Fired {
                    role,
                    at,
                    oracle,
                    missed: Vec::new(),
                    pid,
                    call: None,
                    result: None,
                    note: format!("joins thread `{}`", self.role_name(Role::Thread(*root))),
                }
            }
            StmtKind::ForRange { var, lo, hi, body } => {
                if !matches!(role, Role::Child { .. })
                    || !matches!(
                        cfg.host.proc(pid).map(|p| p.phase),
                        Some(Phase::ForkedPreExec { .. })
                    )
                {
                    return Err(InterpError::Unsupported {
                        at: Some(at),
                        detail: "a descriptor loop outside a forked child (no loop summary)"
                            .to_string(),
                    });
                }
                let (lo, hi) = (Self::val(a, lo)?, Self::val(a, hi)?);
                let (calls, changed, ran) = self.for_range(&mut c, i, *var, lo, hi, *body)?;
                let actor = &mut c.actors[i];
                actor.vars[*var] = hi.max(lo);
                Self::advance(actor);
                self.settle(&mut c.actors[i])?;
                Fired {
                    role,
                    at,
                    oracle,
                    missed: Vec::new(),
                    pid,
                    call: None,
                    result: None,
                    note: format!(
                        "for fd in {lo}..{hi}: {calls} calls ({changed} succeeded; {ran} \
                         executed, the rest are closed-slot iterations proved alike)"
                    ),
                }
            }
            _ => return Err(InterpError::Malformed("firing a local statement".into())),
        };
        Ok(Some((c, fired)))
    }

    /// P-LOCK-RELEASE provenance: after `pid`'s step from `before`, a
    /// description that was not locked and now is was locked BY `pid` — the
    /// owner's lock iff `pid` is the root process; a lock that ended takes the
    /// mark with it; a conversion keeps it.
    fn track_locks(&self, before: &Host, after: &mut Config, pid: Pid) {
        let now: Vec<(OfdId, bool)> =
            after.host.ofds().map(|(o, x)| (o, x.lock.is_some())).collect();
        after.owner_locks.retain(|o| after.host.ofd(*o).is_some_and(|x| x.lock.is_some()));
        for (o, locked) in now {
            let was = before.ofd(o).is_some_and(|x| x.lock.is_some());
            if locked && !was {
                if pid == self.root {
                    after.owner_locks.insert(o);
                } else {
                    after.owner_locks.remove(&o);
                }
            }
        }
    }

    /// RL-FOREIGN (fd-identity): foreign code may make a descriptor of its own
    /// at a free number — `dup2` of one of its descriptors onto it, or
    /// `F_DUPFD` with that floor — at any interleaving point. Only the numbers
    /// an actor of the root has retired (closed, or lost the description of)
    /// matter: those are where a stranger's description makes a later event on
    /// the number reach the wrong file. One squat per number.
    #[must_use]
    pub fn squat_targets(&self, cfg: &Config) -> Vec<i32> {
        if !self.tracks() {
            return Vec::new();
        }
        let Some(p) = cfg.host.proc(self.root) else { return Vec::new() };
        if !matches!(p.phase, Phase::Running) {
            return Vec::new();
        }
        let limit = cfg.host.alloc_limit(self.root);
        let mut out: BTreeSet<i32> = BTreeSet::new();
        for a in cfg.actors.iter().filter(|a| a.pid == self.root) {
            for (n, b) in &a.bindings {
                if matches!(b, Binding::Closed | Binding::Gone)
                    && !p.table.contains_key(n)
                    && !p.inflight.contains_key(n)
                    && *n >= 0
                    && i64::from(*n) < limit
                {
                    out.insert(*n);
                }
            }
        }
        out.into_iter().collect()
    }

    /// Apply an RL-FOREIGN squat at `fd`: foreign code's own unflagged
    /// descriptor, on a file only it reaches (class `foreign`).
    pub fn squat(&self, cfg: &Config, fd: i32) -> Result<Config, InterpError> {
        let mut c = cfg.clone();
        let o = c
            .host
            .install_foreign_file(self.root, fd)
            .map_err(|e| InterpError::Malformed(format!("RL-FOREIGN squat at {fd}: {e:?}")))?;
        let k = self.core.class_idx(crate::env::FOREIGN).ok_or_else(|| {
            InterpError::Malformed("the foreign class is not interned".to_string())
        })?;
        c.classes.insert(o, k);
        Ok(c)
    }

    fn count_site(spawns: &[SpawnRecord], site: SiteId) -> u32 {
        u32::try_from(spawns.iter().filter(|r| r.site == site).count()).unwrap_or(u32::MAX)
    }

    /// Whether `body` is a loop body whose iterations over CLOSED slots are
    /// interchangeable: only table-local events, `Neutral`/`Skip` statements
    /// and branches — no assignment, call or nested loop that could carry an
    /// index-dependent value from one iteration to the next.
    fn uniform_body(&self, body: BodyId) -> bool {
        let Some(b) = self.core.prog.bodies.get(body) else { return false };
        b.blocks.iter().all(|block| {
            block.stmts.iter().all(|s| match &s.kind {
                StmtKind::Event(ev) => matches!(
                    ev.call,
                    Call::Fcntl { .. }
                        | Call::Close { .. }
                        | Call::Ioctl { .. }
                        | Call::Dup2 { .. }
                ),
                StmtKind::Neutral { .. } | StmtKind::Skip => true,
                _ => false,
            })
        })
    }

    /// Literal operands of `body` (in events and branch conditions).
    fn body_literals(&self, body: BodyId) -> Vec<i64> {
        let mut out = Vec::new();
        let Some(b) = self.core.prog.bodies.get(body) else { return out };
        fn cond_lits(c: &Cond, out: &mut Vec<i64>) {
            match c {
                Cond::Cmp(_, x, y) => {
                    for o in [x, y] {
                        if let Operand::Lit(v) = o {
                            out.push(*v);
                        }
                    }
                }
                Cond::And(x, y) | Cond::Or(x, y) => {
                    cond_lits(x, out);
                    cond_lits(y, out);
                }
                Cond::Not(x) => cond_lits(x, out),
                Cond::Const(_) | Cond::Nondet => {}
            }
        }
        for block in &b.blocks {
            for s in &block.stmts {
                if let StmtKind::Event(ev) = &s.kind {
                    let _ = ev.call.map(|o| {
                        if let Operand::Lit(v) = o {
                            out.push(*v);
                        }
                    });
                }
            }
            if let Term::Branch { cond, .. } = &block.term {
                cond_lits(cond, &mut out);
            }
        }
        out
    }

    /// Run `body` once with `var = x`, synchronously, nominal oracles.
    /// Returns (calls, succeeded).
    fn iterate(
        &self,
        c: &mut Config,
        i: usize,
        var: VarId,
        x: i64,
        body: BodyId,
    ) -> Result<(usize, usize), InterpError> {
        let pid = c.actors[i].pid;
        let depth = c.actors[i].frames.len();
        {
            let a = &mut c.actors[i];
            a.vars[var] = x;
            a.frames.push(Frame { body, block: 0, idx: 0, ret: None });
        }
        let (mut calls, mut changed) = (0, 0);
        loop {
            self.settle(&mut c.actors[i])?;
            if c.actors[i].frames.len() <= depth {
                return Ok((calls, changed));
            }
            let a = &c.actors[i];
            if self.pending_choice(a)?.is_some() {
                return Err(InterpError::Unsupported {
                    at: a.pc(),
                    detail: "an undecided guard (Cond::Nondet) in a descriptor-loop body: the \
                             loop's one-step summary (SD-3) needs a deterministic body"
                        .to_string(),
                });
            }
            let Some((at, StmtKind::Event(ev))) = self.at(a) else {
                return Err(InterpError::Unsupported {
                    at: a.pc(),
                    detail: "a loop body with a non-event interleaving point".to_string(),
                });
            };
            let call = Self::concrete_call(a, ev)?;
            if !matches!(
                call,
                Call::Fcntl { .. } | Call::Close { .. } | Call::Ioctl { .. } | Call::Dup2 { .. }
            ) {
                return Err(InterpError::Unsupported {
                    at: Some(at),
                    detail: format!("`{}` in a loop body is not table-local", call.symbol()),
                });
            }
            self.check_dr1(c, pid, at, ev)?;
            let step = trust_platform::step(&c.host, pid, &call, Oracle::Nominal)
                .map_err(|refusal| InterpError::Refused { at, refusal })?;
            calls += 1;
            let ok = step.result.is_ok();
            c.host = step.host;
            c.classes.retain(|o, _| c.host.ofd(*o).is_some());
            if ok {
                changed += 1;
                if let Some(fd) = self.declares(c, pid, &call)
                    && let Some(r) = c.record_mut(pid)
                {
                    r.declared.insert(fd);
                }
            }
            let a = &mut c.actors[i];
            Self::bind(a, ev, &step.result);
            Self::advance(a);
        }
    }

    /// One strip-loop step (SD-3: one quantified step): run `body` for every
    /// index in `[lo, hi)`, synchronously, with nominal oracles, mutating `c`
    /// in place. At the real constants the strip is 65 533 iterations, so a
    /// UNIFORM body ([`Self::uniform_body`]) is run exactly at every
    /// "interesting" index — an open slot of the table, a literal of the
    /// body, a value of the actor's variables, the allocation limit (each
    /// with its neighbours), the end of the range — and the rest of a gap
    /// between them is skipped only after an iteration in it changed
    /// NOTHING: not the host, not the child's declared set, not one variable
    /// but the index. The next iteration then starts from the same state but
    /// for the index, the index meets only closed slots and the same outcome
    /// of every comparison the body can make (no point lies in the gap), and
    /// a uniform body has no arithmetic on it: it is the same no-op, and by
    /// induction so is every iteration to the end of the gap. Returns (calls,
    /// succeeded, executed).
    fn for_range(
        &self,
        c: &mut Config,
        i: usize,
        var: VarId,
        lo: i64,
        hi: i64,
        body: BodyId,
    ) -> Result<(usize, usize, usize), InterpError> {
        let (mut calls, mut changed, mut ran) = (0usize, 0usize, 0usize);
        if hi <= lo {
            return Ok((0, 0, 0));
        }
        let fast = self.uniform_body(body);
        let lits = self.body_literals(body);
        let pid = c.actors[i].pid;
        let mut x = lo;
        while x < hi {
            if fast {
                let next = self.next_interesting(c, i, pid, var, &lits, x, hi);
                if next > x {
                    // A gap [x, next): run x; if it is a fixpoint no-op, the
                    // gap is.
                    let masked = |c: &Config| {
                        let mut v = c.actors[i].vars.clone();
                        v[var] = 0;
                        v
                    };
                    let before =
                        (c.host.clone(), c.record(pid).map(|r| r.declared.clone()), masked(c));
                    let (k, ok) = self.iterate(c, i, var, x, body)?;
                    ran += 1;
                    calls += k;
                    changed += ok;
                    let unchanged = before.0 == c.host
                        && before.1.as_ref() == c.record(pid).map(|r| &r.declared)
                        && before.2 == masked(c);
                    if unchanged {
                        let rest = usize::try_from(next - x - 1).unwrap_or(0);
                        calls += k * rest;
                        changed += ok * rest;
                        x = next;
                    } else {
                        x += 1;
                    }
                    continue;
                }
            }
            let (k, ok) = self.iterate(c, i, var, x, body)?;
            ran += 1;
            calls += k;
            changed += ok;
            x += 1;
        }
        Ok((calls, changed, ran))
    }

    /// The smallest interesting index `>= x` (or `hi - 1`). The loop index
    /// itself (`var`, holding the previous iteration's value) is not a point.
    #[allow(clippy::too_many_arguments)]
    fn next_interesting(
        &self,
        c: &Config,
        i: usize,
        pid: Pid,
        var: VarId,
        lits: &[i64],
        x: i64,
        hi: i64,
    ) -> i64 {
        let mut best = hi - 1;
        let mut consider = |p: i64| {
            if p >= x && p < best {
                best = p;
            }
        };
        if let Some(p) = c.host.proc(pid)
            && let Ok(from) = i32::try_from(x.max(i64::from(i32::MIN)))
            && let Some((fd, _)) = p.table.range(from..).next()
        {
            consider(i64::from(*fd));
        }
        let limit = c.host.alloc_limit(pid);
        let vars = c.actors[i].vars.iter().enumerate().filter(|(k, _)| *k != var).map(|(_, v)| v);
        for v in lits.iter().chain(vars).chain([limit, 0].iter()) {
            for d in [-1, 0, 1] {
                consider(v.saturating_add(d));
            }
        }
        best.max(x)
    }

    /// Run a forked child to its exec or exit, branching on oracle choices:
    /// every outcome with its event log.
    pub fn run_child(
        &self,
        cfg: &Config,
        i: usize,
    ) -> Result<Vec<(Config, Vec<Fired>)>, InterpError> {
        let role = cfg.actors[i].role;
        let mut out = Vec::new();
        let mut stack = vec![(cfg.clone(), Vec::new())];
        while let Some((c, log)) = stack.pop() {
            let Some(j) = c.actors.iter().position(|a| a.role == role) else {
                return Err(InterpError::Malformed("child vanished".into()));
            };
            if c.actors[j].done() || self.at_split(&c, j) {
                out.push((c, log));
                continue;
            }
            // X1: an undecided guard ends the macro step; the choice is a step
            // of its own (`crate::nondet`), taken before anyone else moves,
            // and the next macro step resumes from the arm it took.
            if self.pending_choice(&c.actors[j])?.is_some() {
                if log.is_empty() {
                    return Err(InterpError::Malformed(
                        "a forked child's macro step starts at an undecided guard".into(),
                    ));
                }
                out.push((c, log));
                continue;
            }
            if log.len() >= MAX_CHILD_EVENTS {
                return Err(InterpError::Bound { at: c.actors[j].pc(), events: log.len() });
            }
            for o in self.oracles(&c.actors[j]) {
                match self.fire(&c, j, o, &[])? {
                    Some((c2, f)) => {
                        let mut l2 = log.clone();
                        l2.push(f);
                        stack.push((c2, l2));
                    }
                    None => {
                        return Err(InterpError::Unsupported {
                            at: c.actors[j].pc(),
                            detail: "a forked child blocks: SD-3 split points are not implemented"
                                .to_string(),
                        });
                    }
                }
            }
        }
        out.reverse();
        Ok(out)
    }

    /// Whether the fd-bound premise holds now: every descriptor the root
    /// process holds is below `min(soft RLIMIT_NOFILE, cap)`. With no premise
    /// stated it holds vacuously.
    #[must_use]
    pub fn fd_bound_now(&self, cfg: &Config) -> bool {
        let Some(cap) = self.fd_bound_cap else {
            return true;
        };
        let Some(p) = cfg.host.proc(self.root) else {
            return true;
        };
        let soft = i64::try_from(p.nofile.soft).unwrap_or(i64::MAX);
        let bound = soft.min(cap);
        p.table.keys().all(|fd| i64::from(*fd) < bound)
    }

    /// Whether thread root `t` is listed under fd-identity (checked).
    #[must_use]
    pub fn listed(&self, t: usize) -> bool {
        self.core.prog.policies.fd_identity.contains(&t)
    }

    /// The descriptor NUMBERS `call` acts on without learning which
    /// description they name (everything but `fstat`, whose answer is the
    /// identity).
    fn identity_operands(call: &Call<i32>) -> Vec<i32> {
        match call {
            Call::Fcntl { fd, .. }
            | Call::Dup { fd }
            | Call::Close { fd }
            | Call::Ioctl { fd, .. }
            | Call::SocketOp { fd, .. }
            | Call::Accept { fd }
            | Call::OpenAlias { fd, .. }
            | Call::Flock { fd, .. }
            | Call::ReadSome { fd }
            | Call::WriteSome { fd } => vec![*fd],
            Call::StdPassesExec { fd } | Call::StdClearCloexec { fd } => vec![*fd],
            Call::StdStatusFd { fd } if *fd < 10 => vec![*fd],
            Call::StdCloseMovedStatus { old, new } if old != new => vec![*old],
            Call::Dup2 { from, to } | Call::StdPlaceFd { from, to } => vec![*from, *to],
            Call::OpenPath { at: Some(d), path, .. }
                if *d != darwin::AT_FDCWD && !path.starts_with('/') =>
            {
                vec![*d]
            }
            Call::Spawn { actions, .. } => actions
                .iter()
                .filter_map(|a| match *a {
                    FileAction::Dup2 { from, .. } | FileAction::PlaceStdio { from, .. } => {
                        Some(from)
                    }
                    FileAction::Inherit { fd } | FileAction::Fchdir { fd } => Some(fd),
                    FileAction::InheritIf { fd, enabled: 1 } => Some(fd),
                    FileAction::InheritIf { .. } => None,
                    FileAction::Close { .. } | FileAction::Open { .. } | FileAction::Chdir => None,
                })
                .collect(),
            _ => Vec::new(),
        }
    }

    fn describe_ofd(&self, cfg: &Config, o: Option<OfdId>) -> String {
        match o {
            None => "closed".to_string(),
            Some(o) => cfg
                .classes
                .get(&o)
                .and_then(|k| self.core.classes.get(*k))
                .map_or_else(|| "an unclassified description".to_string(), Clone::clone),
        }
    }

    /// fd-identity for actor `i`'s event `call` (run from `before`, leaving
    /// `after`): check every number it acted on against the actor's binding
    /// (a violation is recorded only for a CHECKED actor; the first is kept),
    /// then update the bindings — an unbound number is bound to what was
    /// observed there, a `close` binds "closed", an allocation or a `dup2`
    /// target binds its description (each a write: [`Actor::wrote`]). A call
    /// that has not returned binds no result yet; its continuation
    /// (`completing`) checks nothing again and binds its result.
    #[allow(clippy::too_many_arguments)]
    fn identity(
        &self,
        before: &Config,
        after: &mut Config,
        i: usize,
        at: StmtRef,
        call: &Call<i32>,
        result: &SysResult,
        completing: bool,
    ) {
        let pid = before.actors[i].pid;
        let role = before.actors[i].role;
        let checked = before.actors[i].checked;
        let found = |n: i32| before.host.entry(pid, n).map(|e| e.ofd);
        if !completing {
            let mut ops = Self::identity_operands(call);
            if let Call::Fstat { fd } = call {
                // Exempt from the check; still an observation of an unbound number.
                if !before.actors[i].bindings.contains_key(fd) {
                    let b = found(*fd).map_or(Binding::Closed, Binding::Ofd);
                    after.actors[i].bindings.insert(*fd, b);
                }
                ops.clear();
            }
            for n in ops {
                let seen = found(n);
                match before.actors[i].bindings.get(&n) {
                    Some(b) if !b.matches(seen) => {
                        if checked && after.identity_violation.is_none() {
                            let believed = match *b {
                                Binding::Ofd(o) => self.describe_ofd(before, Some(o)),
                                Binding::Closed => "closed (this actor closed it)".to_string(),
                                Binding::Gone => "a description that no longer exists".to_string(),
                            };
                            after.identity_violation = Some(IdentityViolation {
                                role,
                                at,
                                fd: n,
                                believed,
                                found: self.describe_ofd(before, seen),
                            });
                        }
                    }
                    Some(_) => {}
                    None => {
                        after.actors[i]
                            .bindings
                            .insert(n, seen.map_or(Binding::Closed, Binding::Ofd));
                    }
                }
            }
        }
        if matches!(result, Ok(Ret::Pending { .. })) {
            return;
        }
        let bind_new = |after: &mut Config, n: i32| {
            if let Some(e) = after.host.entry(pid, n) {
                after.actors[i].bindings.insert(n, Binding::Ofd(e.ofd));
                after.actors[i].wrote.insert(n);
            }
        };
        match (call, result) {
            (Call::Close { fd }, _) => {
                after.actors[i].bindings.insert(*fd, Binding::Closed);
                after.actors[i].wrote.insert(*fd);
            }
            (Call::Dup2 { to, .. } | Call::StdPlaceFd { to, .. }, Ok(_)) => bind_new(after, *to),
            (Call::StdStatusFd { fd }, Ok(Ret::Int(n))) => {
                if let Ok(n) = i32::try_from(*n)
                    && n != *fd
                {
                    bind_new(after, n);
                }
            }
            (Call::StdCloseMovedStatus { old, new }, Ok(_)) if old != new => {
                after.actors[i].bindings.insert(*old, Binding::Closed);
                after.actors[i].wrote.insert(*old);
            }
            (_, Ok(Ret::Int(n))) if Self::returns_new_number(call) => {
                if let Ok(n) = i32::try_from(*n) {
                    bind_new(after, n);
                }
            }
            (_, Ok(Ret::Pair(x, y))) => {
                bind_new(after, *x);
                bind_new(after, *y);
            }
            _ => {}
        }
    }

    /// Whether `call`'s `Int` result is a descriptor number it just
    /// allocated.
    fn returns_new_number(call: &Call<i32>) -> bool {
        match call {
            Call::Open { .. }
            | Call::OpenPath { .. }
            | Call::OpenAlias { .. }
            | Call::Dup { .. }
            | Call::Socket { .. }
            | Call::Accept { .. }
            | Call::Kqueue => true,
            Call::Fcntl { cmd, .. } => *cmd == darwin::F_DUPFD || *cmd == darwin::F_DUPFD_CLOEXEC,
            _ => false,
        }
    }

    /// Whether forked child `j` is at a split point: its next statement is an
    /// event that can change state another process sees ([`CoreProgram::
    /// child_splits`]; never without it). Dropping a reference matters when
    /// the description is lockable and shared or locked (the lock's lifetime),
    /// or is the last reference to a pipe or socket end (its peer's EOF).
    #[must_use]
    pub fn at_split(&self, cfg: &Config, j: usize) -> bool {
        if !self.core.child_splits {
            return false;
        }
        let a = &cfg.actors[j];
        if !matches!(a.role, Role::Child { .. }) {
            return false;
        }
        let Some((_, kind)) = self.at(a) else { return false };
        let ev = match kind {
            StmtKind::Event(ev) => ev,
            StmtKind::ForRange { .. } => return true,
            _ => return false,
        };
        let Ok(call) = Self::concrete_call(a, ev) else { return true };
        let drops = |fds: Vec<i32>| fds.into_iter().any(|fd| self.drop_matters(cfg, a.pid, fd));
        match call {
            Call::Flock { .. }
            | Call::ReadSome { .. }
            | Call::WriteSome { .. }
            | Call::OpenPath { .. }
            | Call::Mkfifo { .. }
            | Call::Unlink { .. }
            | Call::Symlink { .. } => true,
            Call::Close { fd } => drops(vec![fd]),
            Call::StdCloseMovedStatus { old, new } if old != new => drops(vec![old]),
            Call::Dup2 { from, to } | Call::StdPlaceFd { from, to } if from != to => {
                drops(vec![to])
            }
            Call::Exec => drops(
                cfg.host
                    .proc(a.pid)
                    .map(|p| {
                        p.table
                            .iter()
                            .filter(|(_, e)| {
                                e.cloexec
                                    || cfg.host.ofd(e.ofd).is_some_and(|o| !o.kind.survives_exec())
                            })
                            .map(|(fd, _)| *fd)
                            .collect()
                    })
                    .unwrap_or_default(),
            ),
            Call::Exit { .. } => drops(
                cfg.host.proc(a.pid).map(|p| p.fds().into_iter().collect()).unwrap_or_default(),
            ),
            _ => false,
        }
    }

    /// Whether `pid` dropping its `fd` can change what another process sees.
    fn drop_matters(&self, cfg: &Config, pid: Pid, fd: i32) -> bool {
        let Some(e) = cfg.host.entry(pid, fd) else {
            return false;
        };
        let Some(o) = cfg.host.ofd(e.ofd) else {
            return false;
        };
        let lockable = o.node.and_then(|n| cfg.host.node(n)).is_some_and(|n| n.kind.lockable());
        let refs = cfg.host.refs(e.ofd);
        (lockable && (refs > 1 || o.lock.is_some()))
            || (refs == 1 && o.peer != trust_platform::Peer::None)
    }

    /// Display name of a role.
    #[must_use]
    pub fn role_name(&self, r: Role) -> String {
        match r {
            Role::Thread(t) => self
                .core
                .prog
                .roots
                .get(t)
                .map_or_else(|| format!("thread{t}"), |root| root.name.clone()),
            Role::Child { site, nth } => {
                let name = self.core.prog.sites.get(site).map_or("?", |s| s.name.as_str());
                if nth == 0 { format!("child[{name}]") } else { format!("child[{name}#{nth}]") }
            }
        }
    }
}

#[cfg(test)]
mod sp1_regressions {
    use trust_platform::{Access, OfdKind, Rlimit};

    use super::*;
    use crate::program::{Bind, ProgramBuilder};

    fn core() -> CoreProgram {
        let mut p = ProgramBuilder::new("sp1_parent_windows");
        let observer = p.body("observer", Vec::new(), |b| {
            b.event(
                "sp1:test",
                "getrlimit",
                Call::Getrlimit { resource: darwin::RLIMIT_NOFILE },
                Bind::none(),
            );
        });
        let hook = p.body("hook", Vec::new(), |b| b.ret("sp1:test", Some(Operand::Lit(0))));
        let site = p.site("child", "sp1:test", None);
        let mover = p.body("mover", Vec::new(), |b| {
            b.spawn_fork(
                "sp1:test",
                [trust_platform::std_summaries::StdioPlan::Inherit; 3],
                vec![hook],
                site,
                None,
            );
        });
        p.root("observer", observer);
        p.root("mover", mover);
        p.fd_identity_policy(&[0, 1]);
        // Exercise the actual lowered Trust row, including its bound result,
        // adjacent conditional close and authentic std origin. No hand-built
        // core substitutes for the production lowering in these race controls.
        crate::lower::lower(&p.build()).unwrap()
    }

    fn config(core: &CoreProgram, at: StmtRef, fd: i32, soft: u64) -> Config {
        let mut host = Host::new(92160);
        let pid = host.add_root(Rlimit { soft, hard: darwin::RLIM_INFINITY });
        let ofd = host.install_fresh(pid, fd, OfdKind::Opaque, Access::ReadWrite, 0, true).unwrap();
        host = trust_platform::step(&host, pid, &Call::ThreadCreate, Oracle::Nominal).unwrap().host;
        let source = match &core.prog.stmt(at).unwrap().kind {
            StmtKind::Event(Event { call: Call::StdStatusFd { fd: Operand::Var(v) }, .. }) => *v,
            _ => panic!("the interpreter fixture's status operation must bind its source"),
        };
        let mut vars: Vec<_> = core.prog.vars.iter().map(|v| v.init).collect();
        vars[source] = i64::from(fd);
        let actor = |role, frame| Actor {
            role,
            pid,
            frames: vec![frame],
            vars: vars.clone(),
            bindings: [(fd, Binding::Ofd(ofd))].into_iter().collect(),
            wrote: BTreeSet::new(),
            checked: true,
            released: BTreeSet::new(),
            pending: None,
        };
        let observer = core.prog.roots[0].body;
        Config {
            host,
            classes: BTreeMap::new(),
            actors: vec![
                actor(Role::Thread(0), Frame { body: observer, block: 0, idx: 0, ret: None }),
                actor(
                    Role::Thread(1),
                    Frame { body: at.body, block: at.block, idx: at.idx, ret: None },
                ),
            ],
            spawns: Vec::new(),
            identity_violation: None,
            released: BTreeSet::new(),
            owner_locks: BTreeSet::new(),
        }
    }

    #[test]
    fn status_move_window_and_identity_preserve_real_and_noop_outcomes() {
        let core = core();
        let (at, ev) = core
            .prog
            .stmts()
            .find_map(|(at, s)| match &s.kind {
                StmtKind::Event(e) if matches!(e.call, Call::StdStatusFd { .. }) => Some((at, e)),
                _ => None,
            })
            .unwrap();
        let interp = Interp { core: &core, root: Pid(1), fd_bound_cap: None };
        for (fd, soft, moved) in [(4, 256, true), (4, 8, false), (20, 256, false)] {
            let before = config(&core, at, fd, soft);
            assert_eq!(interp.racy_slots(&before, 0), if moved { vec![fd] } else { Vec::new() });
            let call = Interp::concrete_call(&before.actors[1], ev).unwrap();
            let step = trust_platform::step(&before.host, Pid(1), &call, Oracle::Nominal).unwrap();
            let Ok(Ret::Int(new)) = step.result else { panic!() };
            let new = i32::try_from(new).unwrap();
            let mut after = before.clone();
            after.host = step.host;
            interp.identity(&before, &mut after, 1, at, &call, &step.result, false);
            Interp::bind(&mut after.actors[1], ev, &step.result);
            assert_eq!(after.actors[1].bindings[&fd], before.actors[1].bindings[&fd]);
            assert_eq!(
                after.actors[1].wrote,
                if moved { [new].into_iter().collect() } else { BTreeSet::new() }
            );
            assert!(after.host.entry(Pid(1), fd).is_some(), "dup must expose the old alias");
            let close_at = StmtRef { idx: at.idx + 1, ..at };
            let StmtKind::Event(close) = &core.prog.stmt(close_at).unwrap().kind else { panic!() };
            let close_call = Interp::concrete_call(&after.actors[1], close).unwrap();
            assert_eq!(close_call, Call::StdCloseMovedStatus { old: fd, new });
            let step =
                trust_platform::step(&after.host, Pid(1), &close_call, Oracle::Nominal).unwrap();
            let mut closed = after.clone();
            closed.host = step.host;
            interp.identity(&after, &mut closed, 1, close_at, &close_call, &step.result, false);
            assert_eq!(closed.host.entry(Pid(1), fd).is_none(), moved);
            assert_eq!(closed.actors[1].wrote.contains(&fd), moved);
            assert_eq!(
                closed.actors[1].bindings[&fd],
                if moved { Binding::Closed } else { before.actors[1].bindings[&fd] }
            );
        }
    }

    #[test]
    fn stdio_replacement_keeps_raw_dup2_torn_slot_eligibility() {
        let mut core = core();
        let at = core
            .prog
            .stmts()
            .find_map(|(at, s)| {
                matches!(&s.kind, StmtKind::Event(Event { call: Call::StdStatusFd { .. }, .. }))
                    .then_some(at)
            })
            .unwrap();
        let mut cfg = config(&core, at, 4, 256);
        cfg.host.install_fresh(Pid(1), 3, OfdKind::Opaque, Access::ReadWrite, 0, false).unwrap();
        let StmtKind::Event(ev) =
            &mut core.prog.bodies[at.body].blocks[at.block].stmts[at.idx].kind
        else {
            panic!()
        };
        ev.call = Call::StdPlaceFd { from: Operand::Lit(3), to: Operand::Lit(4) };
        let interp = Interp { core: &core, root: Pid(1), fd_bound_cap: None };
        assert_eq!(interp.racy_slots(&cfg, 0), vec![4]);
    }
}
